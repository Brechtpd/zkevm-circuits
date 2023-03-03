//! The MPT circuit implementation.
use eth_types::Field;
use gadgets::{impl_expr, util::Scalar};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use std::{convert::TryInto, env::var, ops::Range};

mod account_leaf;
mod branch;
mod columns;
mod helpers;
mod param;
mod rlp_gadgets;
mod selectors;
mod start;
mod storage_leaf;
mod witness_row;

use branch::BranchConfig;
use columns::MainCols;
use witness_row::{MptWitnessRow, MptWitnessRowType};

use param::HASH_WIDTH;
use selectors::SelectorsConfig;

use crate::{
    assign, assignf, circuit,
    circuit_tools::{cell_manager::CellManager, constraint_builder::merge_lookups, memory::Memory},
    mpt_circuit::{
        helpers::{extend_rand, main_memory, parent_memory, MPTConstraintBuilder},
        start::StartConfig,
        storage_leaf::StorageLeafConfig,
    },
    table::{DynamicTableColumns, KeccakTable, MptTable},
    util::{power_of_randomness_from_instance, Challenges},
};

use self::{account_leaf::AccountLeafConfig, helpers::key_memory};

/// Merkle Patricia Trie config.
pub struct RowConfig<F> {
    start_config: StartConfig<F>,
    branch_config: BranchConfig<F>,
    storage_config: StorageLeafConfig<F>,
    account_config: AccountLeafConfig<F>,
}

/// Merkle Patricia Trie context
#[derive(Clone, Debug)]
pub struct MPTContext<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>,
    pub(crate) mpt_table: MptTable,
    pub(crate) s_main: MainCols<F>,
    pub(crate) c_main: MainCols<F>,
    pub(crate) managed_columns: Vec<Column<Advice>>,
    pub(crate) r: Vec<Expression<F>>,
    pub(crate) memory: Memory<F>,
}

impl<F: Field> MPTContext<F> {
    pub(crate) fn bytes(&self) -> Vec<Column<Advice>> {
        [self.s_main.bytes, self.c_main.bytes].concat().to_vec()
    }

    pub(crate) fn expr(&self, meta: &mut VirtualCells<F>, rot: i32) -> Vec<Expression<F>> {
        self.bytes()
            .iter()
            .map(|&byte| meta.query_advice(byte, Rotation(rot)))
            .collect::<Vec<_>>()
    }
}

/// Merkle Patricia Trie config.
#[derive(Clone)]
pub struct MPTConfig<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>,
    pub(crate) s_main: MainCols<F>,
    pub(crate) c_main: MainCols<F>,
    pub(crate) managed_columns: Vec<Column<Advice>>,
    pub(crate) memory: Memory<F>,
    keccak_table: KeccakTable,
    fixed_table: [Column<Fixed>; 3],
    start_config: StartConfig<F>,
    branch_config: BranchConfig<F>,
    storage_config: StorageLeafConfig<F>,
    account_config: AccountLeafConfig<F>,
    pub(crate) is_start: Column<Advice>,
    pub(crate) is_branch: Column<Advice>,
    pub(crate) is_account: Column<Advice>,
    pub(crate) is_storage: Column<Advice>,
    pub(crate) r: F,
    pub(crate) mpt_table: MptTable,
    cb: MPTConstraintBuilder<F>,
}

/// Enumerator to determine the type of row in the fixed table.
#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    /// All zero lookup data
    Disabled,
    /// Power of randomness: [1, r], [2, r^2],...
    RMult,
    /// 0 - 15
    Range16,
    /// 0 - 255
    Range256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen16,
}

impl_expr!(FixedTableTag);

// TODO(Brecht): remove by refactoring to use memory values instead
#[derive(Default)]
pub(crate) struct ProofValues<F> {
    pub(crate) memory: Memory<F>,
}

impl<F: Field> ProofValues<F> {
    fn new(memory: &Memory<F>) -> Self {
        Self {
            memory: memory.clone(),
            ..Default::default()
        }
    }
}

impl<F: Field> MPTConfig<F> {
    /// Configure MPT Circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        keccak_table: KeccakTable,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_not_first = meta.fixed_column();

        let mpt_table = MptTable::construct(meta);

        let is_start = meta.advice_column();
        let is_branch = meta.advice_column();
        let is_account = meta.advice_column();
        let is_storage = meta.advice_column();

        let s_main = MainCols::new(meta);
        let c_main = MainCols::new(meta);

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let managed_columns = (0..40).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let memory_columns = (0..5).map(|_| meta.advice_column()).collect::<Vec<_>>();

        let mut memory = Memory::new(memory_columns);
        memory.allocate(meta, key_memory(false));
        memory.allocate(meta, key_memory(true));
        memory.allocate(meta, parent_memory(false));
        memory.allocate(meta, parent_memory(true));
        memory.allocate(meta, main_memory());

        let ctx = MPTContext {
            q_enable: q_enable.clone(),
            q_not_first: q_not_first.clone(),
            mpt_table: mpt_table.clone(),
            s_main: s_main.clone(),
            c_main: c_main.clone(),
            managed_columns: managed_columns.clone(),
            r: extend_rand(&power_of_randomness),
            memory: memory.clone(),
        };

        let mut row_config: Option<RowConfig<F>> = None;

        let mut cb = MPTConstraintBuilder::new(33, None);
        meta.create_gate("MPT", |meta| {
            let cell_manager = CellManager::new(meta, &ctx.managed_columns);
            cb.base.set_cell_manager(cell_manager);

            circuit!([meta, cb.base], {
                /* General */
                SelectorsConfig::configure(meta, &mut cb, ctx.clone());

                //let mut cm = CellManager::new(meta, 1, &ctx.managed_columns, 0);
                let start_config;
                let branch_config;
                let storage_config;
                let account_config;
                ifx!{f!(q_enable) => {
                    matchx! {
                        a!(is_start) => {
                            start_config = StartConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_branch) => {
                            branch_config = BranchConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_account) => {
                            account_config = AccountLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_storage) => {
                            storage_config = StorageLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        _ => (),
                    }
                }}

                /* Range checks */
                // These range checks ensure that the value in the RLP columns are all byte value.
                // These lookups also enforce the byte value to be zero the byte index >= length.
                // TODO(Brecht): do 2 bytes/lookup when circuit height >= 2**21
                /*ifx!{f!(position_cols.q_enable) => {
                    // Sanity checks (can be removed, here for safety)
                    require!(cb.length_s.sum_conditions() => bool);
                    require!(cb.length_c.sum_conditions() => bool);
                    // Range checks
                    for &byte in ctx.bytes()[0..2].into_iter() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte), 0.expr()) => @"fixed");
                    }
                    for (idx, &byte) in ctx.bytes()[2..34].into_iter().enumerate() {
                        require!((cb.get_range_s(), a!(byte), cb.get_length_s() - (idx + 1).expr()) => @"fixed");
                    }
                    ifx!{cb.length_sc => {
                        for (idx, &byte) in ctx.bytes()[34..36].into_iter().enumerate() {
                            require!((FixedTableTag::RangeKeyLen256, a!(byte), cb.get_length_s() - 32.expr() - (idx + 1).expr()) => @"fixed");
                        }
                    }}
                    for (idx, &byte) in ctx.bytes()[36..68].into_iter().enumerate() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte), cb.get_length_c() - (idx + 1).expr()) => @"fixed");
                    }
                }}*/

                /* Mult checks */
                // TODO(Brecht): manually optimized lookups for now, but the constraint builder can
                // automatically do this. Shouldn't be too hard hopefully.
                for tag in ["mult", "mult2"] {
                    let lookups = cb.base.consume_lookups(&[tag]);
                    let optimize = true;
                    if optimize {
                        let (_, values) = merge_lookups(&mut cb.base, lookups);
                        require!(values => @"fixed");
                    } else {
                        for lookup in lookups.iter() {
                            ifx!{lookup.condition => {
                                require!(lookup.description, lookup.values => @"fixed");
                            }}
                        }
                    }
                }

                /* Populate lookup tables */
                require!(@"keccak" => keccak_table.columns().iter().map(|table| a!(table)).collect());
                require!(@"fixed" => fixed_table.iter().map(|table| f!(table)).collect());

                /* Memory banks */
                ifx!{f!(q_enable) => {
                    ctx.memory.generate_constraints(&mut cb.base);
                }}

                row_config = Some(RowConfig {
                    start_config,
                    branch_config,
                    storage_config,
                    account_config,
                });
            });

            cb.base.generate_constraints()
        });

        let disable_lookups: usize = var("DISABLE_LOOKUPS")
            .unwrap_or_else(|_| "0".to_string())
            .parse()
            .expect("Cannot parse DISABLE_LOOKUPS env var as usize");
        if disable_lookups == 0 {
            cb.base.generate_lookups(
                meta,
                &[
                    vec!["fixed".to_string(), "keccak".to_string()],
                    ctx.memory.tags(),
                ]
                .concat(),
            );
        } else if disable_lookups == 1 {
            cb.base.generate_lookups(
                meta,
                &[vec!["keccak".to_string()], ctx.memory.tags()].concat(),
            );
        } else if disable_lookups == 2 {
            cb.base.generate_lookups(meta, &ctx.memory.tags());
        } else if disable_lookups == 3 {
            cb.base
                .generate_lookups(meta, &vec!["fixed".to_string(), "keccak".to_string()]);
        } else if disable_lookups == 4 {
            cb.base.generate_lookups(meta, &vec!["keccak".to_string()]);
        }

        println!("num lookups: {}", meta.lookups().len());
        println!("num advices: {}", meta.num_advice_columns());
        println!("num fixed: {}", meta.num_fixed_columns());

        let row_config = row_config.unwrap();
        let randomness = F::zero();
        MPTConfig {
            q_enable,
            q_not_first,
            is_start,
            is_branch,
            is_account,
            is_storage,
            s_main,
            c_main,
            managed_columns,
            memory,
            keccak_table,
            fixed_table,
            start_config: row_config.start_config,
            branch_config: row_config.branch_config,
            storage_config: row_config.storage_config,
            account_config: row_config.account_config,
            r: randomness,
            mpt_table,
            cb,
        }
    }

    /// Make the assignments to the MPTCircuit
    pub fn assign(
        &mut self,
        layouter: &mut impl Layouter<F>,
        witness: &mut [MptWitnessRow<F>],
        r: F,
    ) -> Result<(), Error> {
        self.r = r;
        let mut height = 0;

        // TODO(Brecht): change this on the witness generation side
        let mut memory = self.memory.clone();
        for (_, row) in witness
            .iter_mut()
            .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
            .enumerate()
        {
            if row.get_type() == MptWitnessRowType::BranchChild {
                //println!("- {:?}", row.bytes);
                let mut child_s_bytes = row.bytes[0..34].to_owned();
                if child_s_bytes[1] == 160 {
                    child_s_bytes[0] = 0;
                    child_s_bytes.rotate_left(1);
                } else {
                    child_s_bytes[0] = 0;
                    child_s_bytes[1] = 0;
                    child_s_bytes.rotate_left(2);
                };

                let mut child_c_bytes = row.bytes[34..68].to_owned();
                if child_c_bytes[1] == 160 {
                    child_c_bytes[0] = 0;
                    child_c_bytes.rotate_left(1);
                } else {
                    child_c_bytes[0] = 0;
                    child_c_bytes[1] = 0;
                    child_c_bytes.rotate_left(2);
                };

                row.bytes = [
                    child_s_bytes.clone(),
                    child_c_bytes.clone(),
                    row.bytes[68..].to_owned(),
                ]
                .concat();
                //println!("+ {:?}", row.bytes);
            }

            if row.get_type() == MptWitnessRowType::ExtensionNodeS
                || row.get_type() == MptWitnessRowType::ExtensionNodeC
            {
                //println!("- {:?}", row.bytes);
                let mut value_bytes = row.bytes[34..68].to_owned();
                if value_bytes[1] == 160 {
                    value_bytes[0] = 0;
                    value_bytes.rotate_left(1);
                } else {
                    value_bytes[0] = 0;
                    value_bytes[1] = 0;
                    value_bytes.rotate_left(2);
                };
                row.bytes = [
                    row.bytes[0..34].to_owned(),
                    value_bytes.clone(),
                    row.bytes[68..].to_owned(),
                ]
                .concat();
                //println!("+ {:?}", row.bytes);
            }
        }

        layouter.assign_region(
            || "MPT",
            |mut region| {
                let mut offset = 0;
                let mut pv = ProofValues::new(&self.memory);

                memory.clear_witness_data();

                let working_witness = witness.to_owned().clone();
                for (idx, row) in working_witness
                    .iter()
                    .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
                    .enumerate()
                {
                    //println!("offset: {}", offset);
                    let mut new_proof = idx == 0;
                    if idx > 0 {
                        let row_prev = working_witness[idx - 1].clone();
                        let not_first_level_prev = row_prev.not_first_level();
                        let not_first_level_cur = row.not_first_level();
                        if not_first_level_cur == 0 && not_first_level_prev == 1 {
                            new_proof = true;
                        }
                    }

                    if new_proof {
                        pv = ProofValues::new(&pv.memory);

                        assign!(region, (self.is_start, offset) => 1.scalar())?;
                        self.start_config.assign(
                            &mut region,
                            self,
                            witness,
                            &mut pv,
                            offset,
                            idx,
                        )?;

                        // TODO(Brecht): copied
                        assignf!(region, (self.q_enable, offset) => 1.scalar())?;
                        let q_not_first = if offset == 0 { F::zero() } else { F::one() };
                        assignf!(region, (self.q_not_first, offset) => q_not_first)?;

                        offset += 1;
                    }
                    //println!("{} -> {:?}", offset, row.get_type());

                    assignf!(region, (self.q_enable, offset) => 1.scalar())?;
                    let q_not_first = if offset == 0 { F::zero() } else { F::one() };
                    assignf!(region, (self.q_not_first, offset) => q_not_first)?;

                    if row.get_type() == MptWitnessRowType::InitBranch {
                        //println!("{}: branch", offset);
                        assign!(region, (self.is_branch, offset) => 1.scalar())?;
                        self.branch_config.assign(
                            &mut region,
                            witness,
                            self,
                            &mut pv,
                            offset,
                            idx,
                        )?;
                    } else if row.get_type() == MptWitnessRowType::StorageLeafSKey {
                        assign!(region, (self.is_storage, offset) => 1.scalar())?;
                        //println!("{}: storage", offset);
                        self.storage_config.assign(
                            &mut region,
                            self,
                            witness,
                            &mut pv,
                            offset,
                            idx,
                        )?;
                    } else if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                        assign!(region, (self.is_account, offset) => 1.scalar())?;
                        //println!("{}: account", offset);
                        self.account_config.assign(
                            &mut region,
                            self,
                            witness,
                            &mut pv,
                            offset,
                            idx,
                        )?;
                    }

                    // assign bytes
                    witness[idx].assign(&mut region, self, offset)?;

                    offset += 1;
                }

                memory = pv.memory;
                height = offset;

                Ok(())
            },
        )?;

        memory.assign(layouter, height)?;

        Ok(())
    }

    fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                let mut offset = 0;

                // Zero lookup
                for fixed_table in self.fixed_table.iter() {
                    assignf!(region, (*fixed_table, offset) => 0.scalar())?;
                }
                offset += 1;

                // Mult table
                let mut mult = F::one();
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::RMult.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    assignf!(region, (self.fixed_table[2], offset) => mult)?;
                    mult *= randomness;
                    offset += 1;
                }

                // Byte range table
                for ind in 0..256 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range256.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                // Byte range with length table
                // These fixed rows enable to easily check whether there are zeros in the unused columns (the number of unused columns vary).
                // The lookups ensure that when the unused columns start, the values in these columns are zeros -
                // when the unused columns start, the value that is used for the lookup in the last column is negative
                // and thus a zero is enforced.
                let max_length = 34i32 + 1;
                for (tag, range) in [
                    (FixedTableTag::RangeKeyLen256, 256),
                    (FixedTableTag::RangeKeyLen16, 16),
                ] {
                    for n in -512..max_length {
                        let range = if n < 0 { 1 } else { range };
                        for idx in 0..range {
                            let v = F::from(n.unsigned_abs() as u64)
                                * if n.is_negative() { -F::one() } else { F::one() };
                            assignf!(region, (self.fixed_table[0], offset) => tag.scalar())?;
                            assignf!(region, (self.fixed_table[1], offset) => idx.scalar())?;
                            assignf!(region, (self.fixed_table[2], offset) => v)?;
                            offset += 1;
                        }
                    }
                }

                // Nibble range table
                for ind in 0..16 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range16.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[derive(Default)]
struct MPTCircuit<F> {
    witness: Vec<Vec<u8>>,
    randomness: F,
}

impl<F: Field> Circuit<F> for MPTCircuit<F> {
    type Config = MPTConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let keccak_table = KeccakTable::construct(meta);
        let power_of_randomness: [Expression<F>; HASH_WIDTH] =
            power_of_randomness_from_instance(meta);
        MPTConfig::configure(meta, power_of_randomness, keccak_table)
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut to_be_hashed = vec![];

        let mut witness_rows = vec![];
        for row in self.witness.iter() {
            if row[row.len() - 1] == 5 {
                to_be_hashed.push(row[0..row.len() - 1].to_vec());
            } else {
                let row = MptWitnessRow::new(row[0..row.len()].to_vec());
                witness_rows.push(row);
            }
        }

        config.load_fixed_table(&mut layouter, self.randomness)?;
        config.assign(&mut layouter, &mut witness_rows, self.randomness)?;

        let challenges = Challenges::mock(Value::known(self.randomness));
        config
            .keccak_table
            .dev_load(&mut layouter, &to_be_hashed, &challenges, false)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use param::IS_NON_EXISTING_STORAGE_POS;

    use crate::circuit_tools::constraint_builder::RLCableValue;

    use super::*;

    use halo2_proofs::{
        dev::MockProver,
        halo2curves::{bn256::Fr, FieldExt},
    };

    use std::fs;

    #[test]
    fn test_mpt() {
        // for debugging:
        let path = "src/mpt_circuit/tests";
        // let path = "tests";
        let files = fs::read_dir(path).unwrap();
        files
            .filter_map(Result::ok)
            .filter(|d| {
                if let Some(e) = d.path().extension() {
                    e == "json"
                } else {
                    false
                }
            })
            .enumerate()
            .for_each(|(idx, f)| {
                let path = f.path();
                let mut parts = path.to_str().unwrap().split('-');
                parts.next();
                let file = std::fs::File::open(path.clone());
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

                let mut pub_root = vec![];
                let acc_r = Fr::one() + Fr::one();
                let mut count = 0;
                for row in w.iter().filter(|r| r[r.len() - 1] != 5) {
                    let l = row.len();
                    let pub_root_rlc = row[l - HASH_WIDTH - IS_NON_EXISTING_STORAGE_POS
                        ..l - HASH_WIDTH - IS_NON_EXISTING_STORAGE_POS + HASH_WIDTH]
                        .rlc_value(acc_r);

                    pub_root.push(pub_root_rlc);
                    count += 1;
                }
                // TODO: add pub_root to instances

                let randomness = Fr::one() + Fr::one();
                let instance: Vec<Vec<Fr>> = (1..HASH_WIDTH + 1)
                    .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); count])
                    .collect();

                let circuit = MPTCircuit::<Fr> {
                    witness: w.clone(),
                    randomness,
                };

                println!("{} {:?}", idx, path);
                // let prover = MockProver::run(9, &circuit, vec![pub_root]).unwrap();
                let num_rows = w.len();
                let prover = MockProver::run(14 /* 9 */, &circuit, instance).unwrap();
                assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));
                //assert_eq!(prover.verify_par(), Ok(()));
                //prover.assert_satisfied();
            });
    }
}
