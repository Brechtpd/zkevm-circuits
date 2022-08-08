use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, not},
    util::Expr,
};
use eth_types::{Field, Word};
use gadgets::util::xor;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::{env::var, marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const KECCAK_RATE: usize = 1088;

const C_WIDTH: usize = 5 * 64;

const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const IOTA_ROUND_CST: [u64; 25] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
    0x0000000000000000, // absorb round
];
// Bit positions that have a non-zero value in `IOTA_ROUND_CST`.
const IOTA_ROUND_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];
//const NUM_BITS_PER_THETA_LOOKUP: usize = 3;
const MAX_INPUT_THETA_LOOKUP: u64 = 5;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

fn get_num_bits_per_theta_lookup() -> usize {
    let degree = get_degree() as u32;
    let mut num_bits = 1;
    while (MAX_INPUT_THETA_LOOKUP + 1).pow(num_bits + 1) <= 2u64.pow(degree) {
        num_bits += 1;
    }
    num_bits as usize
}

/// Public data for the bytecode
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct KeccakRow {
    s_bits: [u8; KECCAK_WIDTH],
    c_bits: [u8; C_WIDTH],
    a_bits: [u8; KECCAK_WIDTH / 25],
    q_end: u64,

    // padding
    d_bits: [u8; KECCAK_RATE],
    d_lens: [u32; KECCAK_RATE / 8],
    d_rlcs: [u8; KECCAK_RATE / 8],
    s_flags: [bool; KECCAK_RATE / 8],

}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakBitConfig<F> {
    q_enable: Selector,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_end: Column<Advice>,
    s_bits: [Column<Advice>; KECCAK_WIDTH],
    c_bits: [Column<Advice>; C_WIDTH],
    a_bits: [Column<Advice>; KECCAK_WIDTH / 25],
    iota_bits: [Column<Fixed>; IOTA_ROUND_BIT_POS.len()],
    c_table: Vec<TableColumn>,

    // padding
    d_bits: [Column<Advice>; KECCAK_RATE],
    d_lens: [Column<Advice>; KECCAK_RATE / 8],
    d_rlcs: [Column<Advice>; KECCAK_RATE / 8],
    s_flags: [Column<Advice>; KECCAK_RATE / 8],
    randomness: Column<Advice>,

    _marker: PhantomData<F>,
}

/// KeccakBitircuit
#[derive(Default)]
pub struct KeccakBitCircuit<F: Field> {
    inputs: Vec<KeccakRow>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakBitCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakBitCircuit<F> {
    type Config = KeccakBitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakBitConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.assign(layouter, self.size, &self.inputs)?;
        Ok(())
    }
}

impl<F: Field> KeccakBitConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        println!("num_bits_per_theta_lookup: {}", num_bits_per_theta_lookup);

        let q_enable = meta.selector();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_end = meta.advice_column();
        let s_bits = array_init::array_init(|_| meta.advice_column());
        let c_bits = array_init::array_init(|_| meta.advice_column());
        let a_bits = array_init::array_init(|_| meta.advice_column());
        let iota_bits = array_init::array_init(|_| meta.fixed_column());

        let mut c_table = Vec::new();
        for _ in 0..1 + num_bits_per_theta_lookup {
            c_table.push(meta.lookup_table_column());
        }

        let d_bits = [(); KECCAK_RATE].map(|_| meta.advice_column());
        let d_lens = [(); KECCAK_RATE / 8].map(|_| meta.advice_column());
        let d_rlcs = [(); KECCAK_RATE / 8].map(|_| meta.advice_column());
        let s_flags = [(); KECCAK_RATE / 8].map(|_| meta.advice_column());
        let randomness = meta.advice_column();

        let mut b = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        let mut b_next = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        b[i][j][k] = meta.query_advice(s_bits[counter], Rotation::cur());
                        b_next[i][j][k] = meta.query_advice(s_bits[counter], Rotation::next());
                        counter += 1;
                    }
                }
            }
            vec![0u64.expr()]
        });
        let mut c = vec![vec![0u64.expr(); 64]; 5];
        meta.create_gate("Query Theta c bits", |meta| {
            let mut counter = 0;
            for c in c.iter_mut() {
                for c in c.iter_mut() {
                    *c = meta.query_advice(c_bits[counter], Rotation::cur());
                    counter += 1;
                }
            }
            vec![0u64.expr()]
        });
        let mut a = vec![0u64.expr(); 64];
        let mut a_next = vec![vec![0u64.expr(); 64]; 25];
        meta.create_gate("Absorb bits", |meta| {
            for k in 0..64 {
                a[k] = meta.query_advice(a_bits[k], Rotation::cur());
            }
            for (i, a_next) in a_next.iter_mut().enumerate() {
                for (k, a_next) in a_next.iter_mut().enumerate() {
                    *a_next = meta.query_advice(a_bits[k], Rotation((i + 1) as i32));
                }
            }
            vec![0u64.expr()]
        });

        // Theta lookups
        // TODO: pack 4 (or even more) of these in a single lookup
        // => Total number of lookups: 5*64/4 = 80
        let mut theta = Vec::new();
        for (i, c) in c.iter().enumerate() {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for (k, c) in c.iter().enumerate() {
                let pk = (64 + k - 1) % 64;
                /*input = input * 10u64.expr()
                + (b[pi][0][k].clone()
                    + b[pi][1][k].clone()
                    + b[pi][2][k].clone()
                    + b[pi][3][k].clone()
                    + b[pi][4][k].clone()
                    + b[ni][0][pk].clone()
                    + b[ni][1][pk].clone()
                    + b[ni][2][pk].clone()
                    + b[ni][3][pk].clone()
                    + b[ni][4][pk].clone());*/
                let bit = xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone())
                    + xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone())
                    + xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone())
                    + xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone())
                    + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());
                /*input = input * MAX_INPUT_THETA_LOOKUP.expr()
                + xor::expr(
                    xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone()),
                    xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone()),
                )
                + xor::expr(
                    xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone()),
                    xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone()),
                )
                + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());*/
                theta.push((c.clone(), bit));
            }
        }

        let mut lookup_counter = 0;
        for chunk in theta.chunks(num_bits_per_theta_lookup) {
            meta.lookup("Theta c", |_| {
                let mut factor = 1u64;
                let mut input = 0u64.expr();
                let mut tables = Vec::new();
                for (idx, (bit, expr)) in chunk.iter().enumerate() {
                    //input = input * MAX_INPUT_THETA_LOOKUP.expr() + expr.clone();
                    input = input + expr.clone() * factor.expr();
                    factor *= MAX_INPUT_THETA_LOOKUP;
                    tables.push((bit.clone(), c_table[1 + idx]));
                }
                tables.push((input, c_table[0]));
                tables
            });
            lookup_counter += 1;
        }
        println!("Lookups: {}", lookup_counter);

        meta.create_gate("boolean checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            // State bits
            // TODO: optimize
            for b in &b {
                for b in b {
                    for b in b {
                        cb.require_boolean("boolean state bit", b.clone());
                    }
                }
            }

            for data_bit in d_bits {
                let b = meta.query_advice(data_bit, Rotation::cur());
                cb.require_boolean("input data bit", b);
            }

            for s_flag in s_flags {
                let s = meta.query_advice(s_flag, Rotation::cur());
                cb.require_boolean("boolean state bit", s);
            }

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_sub1 = meta.query_advice(s_flags[i - 1], Rotation::cur());
                cb.require_boolean("boolean state switch", s_i - s_i_sub1);
            }

            // Absorb bits
            for a in &a {
                cb.require_boolean("boolean state bit", a.clone());
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("padding bit checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_sub1 = meta.query_advice(s_flags[i - 1], Rotation::cur());
                let d_bit_0 = meta.query_advice(d_bits[8 * i], Rotation::cur());
                let s_padding_start = s_i - s_i_sub1;
                cb.condition(s_padding_start, |cb| {
                    cb.require_equal("start with 1", d_bit_0, 1u64.expr());
                });
            }
            let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let d_last = meta.query_advice(d_bits[KECCAK_RATE - 1], Rotation::cur());

            cb.condition(s_last, |cb| {
                cb.require_equal("end with 1", d_last, 1u64.expr())
            });
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("intermedium 0 checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut sum_padding_bits = 0u64.expr();
            for i in 0..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                sum_padding_bits = d_bits[i * 8..(i + 1) * 8]
                    .iter()
                    .map(|b| meta.query_advice(*b, Rotation::cur()))
                    .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
            }

            cb.require_equal("sum(padding_bits) == 2", sum_padding_bits, 2u64.expr());
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input len check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let len_i = meta.query_advice(d_lens[i], Rotation::cur());
                let len_i_sub1 = meta.query_advice(d_lens[i - 1], Rotation::cur());

                cb.require_equal(
                    "len[i] = len[i-1] + !s_i",
                    len_i,
                    len_i_sub1 + not::expr(s_i),
                );
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("round", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut b = b.clone();

            // Theta
            let mut ob = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        ob[i][j][k] = xor::expr(b[i][j][k].clone(), c[i][k].clone());
                    }
                }
            }
            b = ob.clone();

            // Rho/Pi
            for (i, b) in b.iter().enumerate() {
                for (j, b) in b.iter().enumerate() {
                    for k in 0..64 {
                        ob[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64].clone();
                    }
                }
            }
            b = ob.clone();

            // Chi/Iota
            let mut iota_counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        if i == 0 && j == 0 && IOTA_ROUND_BIT_POS.contains(&k) {
                            cb.require_equal(
                                "round state transition with round constant",
                                not::expr(b[(i + 1) % 5][j][k].clone())
                                    * b[(i + 2) % 5][j][k].clone(),
                                xor::expr(
                                    xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                                    meta.query_fixed(iota_bits[iota_counter], Rotation::cur()),
                                ),
                            );
                            iota_counter += 1;
                        } else {
                            cb.require_equal(
                                "round state transition",
                                not::expr(b[(i + 1) % 5][j][k].clone())
                                    * b[(i + 2) % 5][j][k].clone(),
                                xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                            );
                        }
                    }
                }
            }

            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let absorb_positions = get_absorb_positions();
            let mut a_slice = 0;
            for i in 0..5 {
                for j in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb bit",
                                xor::expr(b[i][j][k].clone(), a_next[a_slice][k].clone()),
                                b_next[i][j][k].clone(),
                            );
                        }
                        a_slice += 1;
                    } else {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb copy",
                                b[i][j][k].clone(),
                                b_next[i][j][k].clone(),
                            );
                        }
                    }
                }
            }

            cb.gate(
                meta.query_fixed(q_absorb, Rotation::cur())
                    * not::expr(meta.query_advice(q_end, Rotation::cur())),
            )
        });

        println!("degree: {}", meta.degree());

        KeccakBitConfig {
            q_enable,
            q_round,
            q_absorb,
            q_end,
            s_bits,
            c_bits,
            a_bits,
            iota_bits,
            c_table,
            d_bits,
            d_lens,
            d_rlcs,
            s_flags,
            randomness,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[KeccakRow],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                for (offset, keccak_row) in witness.iter().enumerate() {
                    self.set_row(
                        &mut region,
                        offset,
                        keccak_row.q_end,
                        keccak_row.s_bits,
                        keccak_row.c_bits,
                        keccak_row.a_bits,
                        keccak_row.d_bits,
                        keccak_row.d_lens,
                        keccak_row.d_rlcs,
                        keccak_row.s_flags,
                        KeccakBitCircuit::r()
                    )?;
                }
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        s_bits: [u8; KECCAK_WIDTH],
        c_bits: [u8; C_WIDTH],
        a_bits: [u8; KECCAK_WIDTH / 25],
        d_bits: [u8; KECCAK_RATE],
        d_lens: [u32; KECCAK_RATE / 8],
        d_rlcs: [u8; KECCAK_RATE / 8],
        s_flags: [bool; KECCAK_RATE / 8],
        randomness: F,
    ) -> Result<(), Error> {
        let round = offset % 25;

        self.q_enable.enable(region, offset)?;

        // q_round
        region.assign_fixed(
            || format!("assign q_round {}", offset),
            self.q_round,
            offset,
            || Ok(F::from(round != 24)),
        )?;
        // q_absorb
        region.assign_fixed(
            || format!("assign q_absorb {}", offset),
            self.q_absorb,
            offset,
            || Ok(F::from(round == 24)),
        )?;
        // q_end
        region.assign_advice(
            || format!("assign q_end {}", offset),
            self.q_end,
            offset,
            || Ok(F::from(q_end)),
        )?;

        // Input bits d_bits
        for (idx, (bit, column)) in d_bits.iter().zip(self.d_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // padding
        for (idx, (s_flag, column)) in s_flags.iter().zip(self.s_flags.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data select flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*s_flag as u64)),
            )?;
        }

        for (idx, (d_len, column)) in d_lens.iter().zip(self.d_lens.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data len {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*d_len as u64)),
            )?;
        }

        region.assign_advice(
            || format!("assign randomness{}", offset),
            self.randomness,
            offset,
            || Ok(randomness),
        )?;

        // State bits
        for (idx, (bit, column)) in s_bits.iter().zip(self.s_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Theta c bits
        for (idx, (bit, column)) in c_bits.iter().zip(self.c_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign theta c bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Absorb c bits
        for (idx, (bit, column)) in a_bits.iter().zip(self.a_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign absorb bits {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Iota bit columns
        if round < 24 {
            for (pos, column) in IOTA_ROUND_BIT_POS.iter().zip(self.iota_bits.iter()) {
                region.assign_fixed(
                    || format!("assign iota bit {} {}", *pos, offset),
                    *column,
                    offset,
                    || Ok(F::from(((IOTA_ROUND_CST[round] >> *pos) & 1) as u64)),
                )?;
            }
        }

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        layouter.assign_table(
            || "c table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..=MAX_INPUT_THETA_LOOKUP)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut compressed_value = 0u64;
                    let mut factor = 1u64;
                    for (idx, input) in perm.iter().enumerate() {
                        compressed_value += input * factor;
                        factor *= MAX_INPUT_THETA_LOOKUP;

                        table.assign_cell(
                            || "theta c output",
                            self.c_table[idx + 1],
                            offset,
                            || Ok(F::from(*input & 1)),
                        )?;
                    }

                    table.assign_cell(
                        || "theta c input",
                        self.c_table[0],
                        offset,
                        || Ok(F::from(compressed_value)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

fn get_absorb_positions() -> Vec<(usize, usize)> {
    let mut absorb_positions = Vec::new();
    for i in 0..5 {
        for j in 0..5 {
            if i + j * 5 < 17 {
                absorb_positions.push((i, j));
            }
        }
    }
    absorb_positions
}

fn keccak(bytes: Vec<u8>) -> Vec<KeccakRow> {
    let mut rows: Vec<KeccakRow> = Vec::new();
    let mut bits = into_bits(&bytes);

    // Absorb
    let mut b = [[[0u8; 64]; 5]; 5];

    let absorb_positions = get_absorb_positions();

    let keccak_rate_in_bytes = KECCAK_RATE / 8;
    let data_len = bits.len();

    bits.push(1);
    while (bits.len() + 1) % KECCAK_RATE != 0 {
        bits.push(0);
    }
    bits.push(1);

    println!("bits {:?}", bits);
    println!("data_len {:?}, bits.len() {:?}", data_len, bits.len());

    let chunks = bits.chunks(KECCAK_RATE);
    let num_chunks = chunks.len();
    println!("num_chunks: {}", num_chunks);
    for (idx, chunk) in chunks.enumerate() {
        // Absorb
        let mut counter = 0;
        for &(i, j) in &absorb_positions {
            for k in 0..64 {
                b[i][j][k] ^= chunk[counter];
                counter += 1;
            }
        }

        let data_len_offset = (data_len / 8 % keccak_rate_in_bytes) as u32;
        let data_len_base = ((data_len / 8 / keccak_rate_in_bytes) * keccak_rate_in_bytes) as u32;
        println!("data_len_offset {:?}", data_len_offset);
        println!("data_len_base {:?}", data_len_base);

        // padding
        // Add d_bit to all 24 rounds + 1 absort round
        let mut d_bits = [0u8; KECCAK_RATE];
        let mut d_lens = [0u32; KECCAK_RATE / 8];
        let d_rlcs = [0u8; KECCAK_RATE / 8];
        let mut s_flags = [false; KECCAK_RATE / 8];

        let mut counter = 0;
        for d_bit in d_bits.iter_mut() {
            *d_bit = chunk[counter];
            counter += 1;
        }

        for i in 0 as usize..(KECCAK_RATE / 8) {
            if i == 0 {
                s_flags[i] = data_len_offset == 0;
                d_lens[i] = data_len_base + !s_flags[i] as u32;
                continue
            }

            if (i as u32) < data_len_offset {
                s_flags[i] = false;
            } else {
                s_flags[i] = true;
            }

            d_lens[i] = d_lens[i - 1] + !s_flags[i] as u32;
        }

        println!("s_flags {:?}", s_flags);
        println!("d_lens {:?}", d_lens);

        let mut counter = 0;
        for (round, round_cst) in IOTA_ROUND_CST.iter().enumerate() {
            let mut a_bits = [0u8; 64];
            if counter < KECCAK_RATE {
                for a_bit in a_bits.iter_mut() {
                    *a_bit = chunk[counter];
                    counter += 1;
                }
            }

            let mut c = [[0u8; 64]; 5];
            for (i, c) in c.iter_mut().enumerate() {
                let pi = (5 + i - 1) % 5;
                let ni = (i + 1) % 5;
                for (k, c) in c.iter_mut().enumerate() {
                    let pk = (64 + k - 1) % 64;
                    *c = (b[pi][0][k]
                        + b[pi][1][k]
                        + b[pi][2][k]
                        + b[pi][3][k]
                        + b[pi][4][k]
                        + b[ni][1][pk]
                        + b[ni][0][pk]
                        + b[ni][2][pk]
                        + b[ni][3][pk]
                        + b[ni][4][pk])
                        & 1;
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut s_bits = [0u8; KECCAK_WIDTH];
            for b in b {
                for b in b {
                    for b in b {
                        s_bits[counter] = b;
                        counter += 1;
                    }
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut c_bits = [0u8; C_WIDTH];
            for c in c {
                for c in c {
                    c_bits[counter] = c;
                    counter += 1;
                }
            }

            let q_end = round == 24 && idx == num_chunks - 1;

            rows.push(KeccakRow {
                s_bits,
                c_bits,
                a_bits,
                q_end: q_end as u64,
                d_bits,
                d_lens,
                d_rlcs,
                s_flags,
            });

            if round < 24 {
                // Theta
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            b[i][j][k] ^= c[i][k];
                        }
                    }
                }

                // Rho/Pi
                let mut ob = b;
                for (i, b) in b.iter().enumerate() {
                    for (j, b) in b.iter().enumerate() {
                        for k in 0..64 {
                            ob[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64]
                        }
                    }
                }
                b = ob;

                // Chi
                let mut ob = b;
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            ob[i][j][k] =
                                b[i][j][k] ^ ((1 - b[(i + 1) % 5][j][k]) * b[(i + 2) % 5][j][k]);
                        }
                    }
                }
                b = ob;

                // Iota
                for k in IOTA_ROUND_BIT_POS {
                    b[0][0][k] ^= ((round_cst >> k) & 1) as u8;
                }
            }
        }
    }

    let hash_bytes = b
        .into_iter()
        .take(4)
        .map(|a| from_bits(&a[0]).as_u64().to_le_bytes())
        .collect::<Vec<_>>();
    println!("Hash: {:x?}", &(hash_bytes[0..4].concat()));

    rows
}

fn into_bits(bytes: &[u8]) -> Vec<u8> {
    let num_bits = bytes.len() * 8;
    let mut bits: Vec<u8> = vec![0; num_bits];

    let mut counter = 0;
    for byte in bytes {
        for idx in 0u64..8 {
            bits[counter] = (*byte >> idx) & 1;
            counter += 1;
        }
    }

    bits
}

fn from_bits(bits: &[u8]) -> Word {
    let mut value = Word::zero();
    for (idx, bit) in bits.iter().enumerate() {
        value += Word::from(*bit as u64) << idx;
    }
    value
}

fn to_bytes(bits: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for byte_bits in bits.chunks(5) {
        let mut value = 0u8;
        for (idx, bit) in byte_bits.iter().enumerate() {
            value += *bit << idx;
        }
        bytes.push(value);
    }
    bytes
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakRow>, success: bool) {
        let circuit = KeccakBitCircuit::<F> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    #[test]
    fn bit_keccak_simple() {
        let k = 8;
        let inputs = keccak(vec![1u8; 200]);
        verify::<Fr>(k, inputs, true);
    }

    #[test]
    fn bit_keccak_simple_padding() {
        let k = 8;
        let inputs = keccak(vec![1u8; 100]);
        verify::<Fr>(k, inputs, true);
    }
}
