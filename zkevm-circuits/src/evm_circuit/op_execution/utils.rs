//! Reusable utilities for the op code implementations.

use super::super::Constraint;
use super::utils::constraint_builder::ConstraintBuilder;
use super::OpExecutionState;
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

pub(crate) mod common_cases;
pub(crate) mod constraint_builder;
pub(crate) mod math_gadgets;
pub(crate) mod memory_gadgets;

pub const STACK_START_IDX: usize = 1024;
pub const MAX_GAS_SIZE_IN_BYTES: usize = 8;
// Number of bytes that will be used of the address word.
// If any of the other more signficant bytes are used it will
// always result in an out-of-gas error.
pub const NUM_ADDRESS_BYTES_USED: usize = 5;
pub const MAX_MEMORY_SIZE_IN_BYTES: usize = 5;

type Address = u64;
type MemorySize = u64;

// Makes sure all state transition variables are always constrained.
// This makes it impossible for opcodes to forget to constrain
// any state variables. If no update is specified it is assumed
// that the state variable needs to remain the same (which may not
// be correct, but this will easily be detected while testing).
#[derive(Clone, Debug, Default)]
pub(crate) struct StateTransitions<F> {
    pub gc_delta: Option<Expression<F>>,
    pub sp_delta: Option<Expression<F>>,
    pub pc_delta: Option<Expression<F>>,
    pub gas_delta: Option<Expression<F>>,
    pub next_memory_size: Option<Expression<F>>,
}

impl<F: FieldExt> StateTransitions<F> {
    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) {
        // Global Counter
        cb.add_expression(
            state_next.global_counter.expr()
                - (state_curr.global_counter.expr()
                    + self.gc_delta.clone().unwrap_or_else(|| 0.expr())),
        );
        // Stack Pointer
        cb.add_expression(
            state_next.stack_pointer.expr()
                - (state_curr.stack_pointer.expr()
                    + self.sp_delta.clone().unwrap_or_else(|| 0.expr())),
        );
        // Program Counter
        cb.add_expression(
            state_next.program_counter.expr()
                - (state_curr.program_counter.expr()
                    + self.pc_delta.clone().unwrap_or_else(|| 0.expr())),
        );
        // Gas Counter
        cb.add_expression(
            state_next.gas_counter.expr()
                - (state_curr.gas_counter.expr()
                    + self.gas_delta.clone().unwrap_or_else(|| 0.expr())),
        );
        // Memory size
        cb.add_expression(
            state_next.memory_size.expr()
                - (self
                    .next_memory_size
                    .clone()
                    .unwrap_or_else(|| state_curr.memory_size.expr())),
        );
    }
}

pub(crate) fn batch_add_expressions<F: FieldExt>(
    constraints: Vec<Constraint<F>>,
    expressions: Vec<Expression<F>>,
) -> Vec<Constraint<F>> {
    constraints
        .into_iter()
        .map(|mut constraint| {
            constraint.polys =
                [constraint.polys.clone(), expressions.clone().to_vec()]
                    .concat();
            constraint
        })
        .collect()
}

/// Returns the sum of the passed in cells
pub(crate) mod sum {
    use super::super::Cell;
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(cells: &[Cell<F>]) -> Expression<F> {
        cells.iter().fold(0.expr(), |acc, cell| acc + cell.expr())
    }

    pub(crate) fn value<F: FieldExt>(values: &[u8]) -> F {
        values
            .iter()
            .fold(F::zero(), |acc, value| acc + F::from_u64(*value as u64))
    }
}

/// Returns `1` when `expr[0] && expr[1] && ... == 1`, and returns `0` otherwise.
/// Inputs need to be boolean
pub(crate) mod and {
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(
        inputs: Vec<Expression<F>>,
    ) -> Expression<F> {
        inputs
            .iter()
            .fold(1.expr(), |acc, input| acc * input.clone())
    }

    pub(crate) fn value<F: FieldExt>(inputs: Vec<F>) -> F {
        inputs.iter().fold(F::one(), |acc, input| acc * input)
    }
}

/// Returns `when_true` when `selector == 1`, and returns `when_false` when `selector == 0`.
/// `selector` needs to be boolean.
pub(crate) mod select {
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(
        selector: Expression<F>,
        when_true: Expression<F>,
        when_false: Expression<F>,
    ) -> Expression<F> {
        selector.clone() * when_true + (1.expr() - selector) * when_false
    }

    pub(crate) fn value<F: FieldExt>(
        selector: F,
        when_true: F,
        when_false: F,
    ) -> F {
        selector * when_true + (F::one() - selector) * when_false
    }
}

/// Decodes a field element from its byte representation
pub(crate) mod from_bytes {
    use crate::{evm_circuit::Cell, util::Expr};
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(bytes: Vec<Cell<F>>) -> Expression<F> {
        let mut multiplier = 1.expr();
        let mut value = 0.expr();
        for byte in bytes.iter() {
            value = value + byte.expr() * multiplier.clone();
            multiplier = multiplier * 256.expr();
        }
        value
    }

    pub(crate) fn value<F: FieldExt>(bytes: Vec<u8>) -> F {
        let mut value = F::from_u64(0);
        let mut multiplier = F::from_u64(1);
        for byte in bytes.iter() {
            value += F::from_u64(*byte as u64) * multiplier;
            multiplier *= F::from_u64(256);
        }
        value
    }
}

/// Returns 2**num_bits
pub(crate) fn get_range<F: FieldExt>(num_bits: usize) -> F {
    F::from_u64(2).pow(&[num_bits as u64, 0, 0, 0])
}

/// Counts the number of repetitions
#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + crate::count!($($xs)*));
}

/// Common OpGadget implementer
#[macro_export]
macro_rules! impl_op_gadget {
    ([$($op:ident),*] $name:ident { $($case:ident ($($args:expr),*) ),* $(,)? }) => {

        paste::paste! {
            #[derive(Clone, Debug)]
            pub struct $name<F> {
                $(
                    [<$case:snake>]: $case<F>,
                )*
            }
        }

        impl<F: FieldExt> OpGadget<F> for $name<F> {
            const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[$(OpcodeId::$op),*];

            const CASE_CONFIGS: &'static [CaseConfig] = &[
                $(
                    *$case::<F>::CASE_CONFIG,
                )*
            ];

            fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
                paste::paste! {
                    let [
                        $(
                            mut [<$case:snake>],
                        )*
                    ]: [CaseAllocation<F>; crate::count!($($case)*)] =
                        case_allocations.try_into().unwrap();
                    Self {
                        $(
                            [<$case:snake>]: $case::construct(
                                &mut [<$case:snake>],
                                $(
                                    $args,
                                )*
                            ),
                        )*
                    }
                }
            }

            fn constraints(
                &self,
                state_curr: &OpExecutionState<F>,
                state_next: &OpExecutionState<F>,
            ) -> Vec<Constraint<F>> {
                paste::paste! {
                    $(
                        let [<$case:snake>] = self.[<$case:snake>].constraint(
                            state_curr,
                            state_next,
                            concat!(stringify!($name), " ", stringify!([<$case:snake>])),
                        );
                    )*
                    let cases = vec![
                        $(
                            [<$case:snake>],
                        )*
                    ];
                }
                // Add common expressions to all cases
                let mut cb = ConstraintBuilder::default();
                cb.require_in_set(
                    state_curr.opcode.expr(),
                    vec![$(OpcodeId::$op.expr()),*],
                );
                utils::batch_add_expressions(
                    cases,
                    cb.expressions,
                )
            }

            paste::paste! {
                fn assign(
                    &self,
                    region: &mut Region<'_, F>,
                    offset: usize,
                    op_execution_state: &mut CoreStateInstance,
                    execution_step: &ExecutionStep,
                ) -> Result<(), Error> {
                    $(
                        if execution_step.case == $case::<F>::CASE_CONFIG.case {
                            return self.[<$case:snake>].assign(
                                region,
                                offset,
                                op_execution_state,
                                execution_step,
                            );
                        }
                    )*
                    else {
                        unreachable!();
                    }
                }
            }
        }
    };
}
