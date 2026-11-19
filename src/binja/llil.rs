use binaryninja::architecture::{
    Architecture, CoreArchitecture, Register, RegisterId, RegisterInfo,
};
use binaryninja::function::Function;
use binaryninja::low_level_il::{
    LowLevelILSSAFunction,
    expression::{ExpressionHandler, LowLevelILExpressionKind as Expr},
    instruction::{
        InstructionHandler, LowLevelILInstructionKind as Instruction, LowLevelInstructionIndex,
    },
};
use binaryninja::rc::Ref;
use binaryninja::variable::RegisterValueType;
use binaryninjacore_sys::*;

use super::FunctionHandle;

/// Owned current SSA with the few physical queries omitted by the Rust SDK.
#[derive(Clone)]
pub(crate) struct Ssa {
    pub il: Ref<LowLevelILSSAFunction>,
    raw: *mut BNLowLevelILFunction,
    arch: CoreArchitecture,
}

impl Ssa {
    fn handle(function: &Function) -> Option<*mut BNLowLevelILFunction> {
        let function = FunctionHandle::new(function)?;
        unsafe {
            let regular = BNGetFunctionLowLevelILIfAvailable(function.as_ptr());
            if regular.is_null() {
                return None;
            }
            let raw = BNGetLowLevelILSSAForm(regular);
            BNFreeLowLevelILFunction(regular);
            (!raw.is_null()).then_some(raw)
        }
    }

    pub fn new(function: &Function) -> Option<Self> {
        let _regular = function.low_level_il().ok()?;
        let raw = Self::handle(function)?;
        let il = unsafe { LowLevelILSSAFunction::from_raw(raw) }.to_owned();
        unsafe { BNFreeLowLevelILFunction(raw) };
        Some(Self {
            il,
            raw,
            arch: function.arch(),
        })
    }

    pub fn current(&self, function: &Function) -> bool {
        !function.is_update_needed()
            && Self::handle(function).is_some_and(|raw| {
                let same = raw == self.raw;
                unsafe { BNFreeLowLevelILFunction(raw) };
                same
            })
    }

    pub fn expression(&self, index: usize) -> Option<BNLowLevelILInstruction> {
        (index < self.il.expression_count())
            .then(|| unsafe { BNGetLowLevelILByIndex(self.raw, index) })
    }

    pub fn memory_definition(&self, version: usize) -> Option<LowLevelInstructionIndex> {
        let index = unsafe { BNGetLowLevelILSSAMemoryDefinition(self.raw, version) };
        (index < self.il.instruction_count()).then_some(LowLevelInstructionIndex(index))
    }

    pub fn position(&self, expression: usize) -> Option<usize> {
        let index = unsafe { BNGetLowLevelILInstructionForExpr(self.raw, expression) };
        (index < self.il.instruction_count()).then_some(index)
    }

    /// amd64 callee entry stack offset and memory immediately before a call.
    pub fn call_stack(&self, index: usize) -> Option<(i64, usize)> {
        if self.arch.name() != "x86_64" {
            return None;
        }
        let site = self.il.instruction_from_index(index.into())?;
        let op = match site.kind() {
            Instruction::CallSsa(op) | Instruction::TailCallSsa(op) => op,
            _ => return None,
        };
        let stack = op.stack_expr();
        let raw = self.expression(stack.index.0)?;
        let Expr::CallStackSsa(op) = stack.kind() else {
            return None;
        };
        if op.source_reg().physical_reg().id() != self.arch.stack_pointer_reg()?.id() {
            return None;
        }
        let value = self.il.get_ssa_register_value(op.source_reg())?;
        if value.state != RegisterValueType::StackFrameOffset {
            return None;
        }
        let adjustment = if matches!(site.kind(), Instruction::TailCallSsa(_)) {
            0
        } else {
            8
        };
        Some((
            value.value.checked_sub(adjustment)?,
            raw.operands[2] as usize,
        ))
    }

    pub fn has_user_values(function: &Function) -> bool {
        let Some(handle) = FunctionHandle::new(function) else {
            return true;
        };
        let mut count = 0;
        unsafe {
            let values = BNGetAllUserVariableValues(handle.as_ptr(), &mut count);
            if !values.is_null() {
                BNFreeUserVariableValues(values);
            }
        }
        count != 0
    }

    /// Split destinations have their own opcode, omitted by the SDK's value enum.
    pub fn split_destination(&self, expression: usize) -> Option<u32> {
        let expression = self.expression(expression)?;
        if expression.operation != BNLowLevelILOperation::LLIL_REG_SPLIT_DEST_SSA {
            return None;
        }
        let id = RegisterId(u32::try_from(expression.operands[0]).ok()?);
        if id.is_temporary() {
            return Some(id.0);
        }
        let register = self.arch.register_from_id(id)?;
        Some(register.info().parent().unwrap_or(register).id().0)
    }
}
