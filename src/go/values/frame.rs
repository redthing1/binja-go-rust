use std::collections::BTreeSet;

use binaryninja::low_level_il::expression::{ExpressionHandler, LowLevelILExpressionKind as Expr};
use binaryninja::low_level_il::instruction::{
    InstructionHandler, LowLevelILInstructionKind as Instruction,
};
use binaryninja::variable::RegisterValueType;

use super::{Expression, Reader, Site, Value};

// These proofs describe actual callee writes and normal returns, independently
// of the call outputs and memory effects inferred by the core.
impl Reader<'_> {
    /// A conditional full-word write cannot replace a known non-stack word
    /// when the same memory word must first equal a stack address.
    fn guarded_stack_store(&self, site: Site<'_>, nonstack: bool, width: usize) -> bool {
        if !nonstack || width != 8 {
            return false;
        }
        let Instruction::StoreSsa(store) = site.kind() else {
            return false;
        };
        let panic_pointer = self.panic_pointer(store.dest_expr(), site.index.0);
        if store.size() != 8 || !panic_pointer {
            return false;
        }
        let Some(block) = site.basic_block() else {
            return false;
        };
        // No intervening memory operation may invalidate the tested word.
        if block.start_index() != site.index {
            return false;
        }
        let edges = block.incoming_edges();
        !edges.is_empty()
            && edges.iter().all(|edge| {
                let Some(index) = edge.source.end_index().0.checked_sub(1) else {
                    return false;
                };
                let Some(branch) = self.ssa.il.instruction_from_index(index.into()) else {
                    return false;
                };
                let Instruction::If(op) = branch.kind() else {
                    return false;
                };
                let condition = op.condition();
                let (left, right, equal) = match condition.kind() {
                    Expr::CmpE(op) => (op.left(), op.right(), true),
                    Expr::CmpNe(op) => (op.left(), op.right(), false),
                    _ => return false,
                };
                use binaryninja::architecture::BranchType;
                if !matches!(
                    (equal, edge.branch),
                    (true, BranchType::TrueBranch) | (false, BranchType::FalseBranch)
                ) {
                    return false;
                }
                [(left, right), (right, left)].iter().any(|(load, stack)| {
                    let Expr::LoadSsa(load) = load.kind() else {
                        return false;
                    };
                    let Some(destination) = self.ssa.expression(store.dest_expr().index.0) else {
                        return false;
                    };
                    let Some(source) = self.ssa.expression(load.source_expr().index.0) else {
                        return false;
                    };
                    load.size() == 8
                        && load.source_memory_version() == store.source_memory_version()
                        && destination.operation == source.operation
                        && destination.size == source.size
                        && destination.operands == source.operands
                        && stack.value().state == RegisterValueType::StackFrameOffset
                })
            })
    }

    /// Go's aligned g._panic pointer may itself refer to a stack object.
    /// Do not classify it as a heap allocation or permit arbitrary guarded stores.
    fn panic_pointer(&self, expression: Expression<'_>, position: usize) -> bool {
        use binaryninja::architecture::{ArchitectureExt, Register};
        let Expr::RegSsa(reg) = expression.kind() else {
            return false;
        };
        let register = reg.source_reg().physical_reg();
        let Some(definition) = self.ssa.il.get_ssa_register_definition(reg.source_reg()) else {
            return false;
        };
        let Instruction::SetRegSsa(set) = definition.kind() else {
            return false;
        };
        let value = set.source_expr();
        let Expr::LoadSsa(load) = value.kind() else {
            return false;
        };
        let address = load.source_expr();
        let Expr::Add(add) = address.kind() else {
            return false;
        };
        let left = add.left();
        let right = add.right();
        let Expr::RegSsa(g) = left.kind() else {
            return false;
        };
        let Some(function) = self.ssa.il.function() else {
            return false;
        };
        let Some(r14) = function.arch().register_by_name("r14") else {
            return false;
        };
        if load.size() != 8
            || g.source_reg().physical_reg().version != 0
            || g.source_reg().physical_reg().id() != r14.id()
            || !matches!(right.kind(), Expr::Const(op) if op.value() == 32)
        {
            return false;
        }
        // This compiler wrapper sequence has no calls or hidden writes between
        // the load and its guarded use. Reject unfamiliar instruction effects.
        for index in definition.index.0 + 1..position {
            let Some(site) = self.ssa.il.instruction_from_index(index.into()) else {
                return false;
            };
            match site.kind() {
                Instruction::SetRegSsa(op)
                    if op.dest_reg().physical_reg().id() != register.id() =>
                {
                    ()
                }
                Instruction::RegPhi(op) if op.dest_reg().physical_reg().id() != register.id() => (),
                Instruction::Nop(_)
                | Instruction::If(_)
                | Instruction::Goto(_)
                | Instruction::Ret(_)
                | Instruction::MemPhi(_)
                | Instruction::FlagPhi(_) => (),
                _ => return false,
            }
        }
        true
    }

    pub(super) fn disjoint_store(
        &mut self,
        site: Site<'_>,
        offset: i64,
        width: usize,
        nonstack: bool,
    ) -> bool {
        let Instruction::StoreSsa(op) = site.kind() else {
            return false;
        };
        let destination = op.dest_expr().value();
        if destination.state == RegisterValueType::StackFrameOffset {
            return offset
                .checked_add(width as i64)
                .is_some_and(|end| end <= destination.value)
                || destination
                    .value
                    .checked_add(op.size() as i64)
                    .is_some_and(|end| end <= offset);
        }
        self.visit(op.dest_expr(), site.index.0, 0, &mut BTreeSet::new())
            .is_some_and(|value| value.contains(op.size()))
            || (offset % 8 == 0 && self.guarded_stack_store(site, nonstack, width))
    }

    fn safe_memory(&mut self, memory: usize, depth: usize) -> Option<()> {
        self.spend(depth)?;
        if memory == 0 {
            return Some(());
        }
        let index = self.ssa.memory_definition(memory)?;
        let site = self.ssa.il.instruction_from_index(index)?;
        match site.kind() {
            Instruction::StoreSsa(op) if self.disjoint_store(site, 0, 8, true) => {
                self.safe_memory(op.source_memory_version() as usize, depth + 1)
            }
            Instruction::MemPhi(op) => {
                for memory in op.source_memory_versions() {
                    self.safe_memory(memory, depth + 1)?;
                }
                Some(())
            }
            Instruction::CallSsa(_) if self.effects?.preserves(self, site, 0, 8, true) => {
                self.safe_memory(self.ssa.call_stack(index.0)?.1, depth + 1)
            }
            _ => None,
        }
    }

    pub(in crate::go) fn preserves_frame(
        &mut self,
        offset: i64,
        width: usize,
        nonstack: bool,
    ) -> bool {
        for index in 0..self.ssa.il.instruction_count() {
            if self.spend(0).is_none() {
                return false;
            }
            let Some(site) = self.ssa.il.instruction_from_index(index.into()) else {
                return false;
            };
            let valid = match site.kind() {
                Instruction::StoreSsa(_) => self.disjoint_store(site, offset, width, nonstack),
                Instruction::CallSsa(_) => self.effects.is_some_and(|effects| {
                    effects.exit_call(self, site)
                        || effects.preserves(self, site, offset, width, nonstack)
                }),
                Instruction::NoRet(_) => {
                    self.effects.is_some_and(|effects| effects.exit(self, site))
                }
                Instruction::Ret(op) => self.return_destination(op.target()),
                Instruction::TailCallSsa(_)
                | Instruction::Jump(_)
                | Instruction::JumpTo(_)
                | Instruction::Undef(_)
                | Instruction::SyscallSsa(_)
                | Instruction::Intrinsic(_)
                | Instruction::Trap(_) => false,
                _ => inert(site),
            };
            if !valid {
                return false;
            }
        }
        true
    }

    fn return_destination(&mut self, destination: Expression<'_>) -> bool {
        let Expr::LoadSsa(op) = destination.kind() else {
            return false;
        };
        let stack = op.source_expr().value();
        op.size() == 8
            && stack.state == RegisterValueType::StackFrameOffset
            && stack.value == 0
            && self
                .safe_memory(op.source_memory_version() as usize, 0)
                .is_some()
    }

    pub(in crate::go) fn returned(&mut self, register: u32) -> Option<Value> {
        let mut result = None;
        for index in 0..self.ssa.il.instruction_count() {
            let site = self.ssa.il.instruction_from_index(index.into())?;
            match site.kind() {
                Instruction::Ret(op) => {
                    if !self.return_destination(op.target()) {
                        return None;
                    }
                    let value = self.before(index, register, 0)?.returned();
                    if result.is_some_and(|previous| previous != value) {
                        return None;
                    }
                    result = Some(value);
                }
                Instruction::NoRet(_) if self.effects?.exit(self, site) => (),
                Instruction::TailCallSsa(_)
                | Instruction::Jump(_)
                | Instruction::JumpTo(_)
                | Instruction::NoRet(_)
                | Instruction::Undef(_)
                | Instruction::Trap(_) => return None,
                Instruction::CallSsa(_) | Instruction::StoreSsa(_) => (),
                _ if inert(site) => (),
                _ => return None,
            }
        }
        result
    }
}

fn inert(site: Site<'_>) -> bool {
    match site.kind() {
        Instruction::Nop(_)
        | Instruction::SetRegSsa(_)
        | Instruction::SetRegPartialSsa(_)
        | Instruction::SetRegSplitSsa(_)
        | Instruction::SetFlagSsa(_)
        | Instruction::RegPhi(_)
        | Instruction::FlagPhi(_)
        | Instruction::MemPhi(_)
        | Instruction::If(_)
        | Instruction::Goto(_) => true,
        Instruction::Value(expression) => matches!(expression.kind(), Expr::And(_)),
        _ => false,
    }
}
