// Copyright © 2021, StarCrossTech.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License.  You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
// express or implied.  See the License for the specific language governing permissions and
// limitations under the License.
#![allow(unused_parens)]
use super::{ArithPcodeTranslator, BlockTranslator, MemMappedMemory, Result};
use crate::{Address, PcodeOp, SeqNum, Varnode, emu::{EmuError, Memory}};
use dynasm::dynasm;
use dynasmrt::{
    x64::{self, X64Relocation},
    Assembler, AssemblyOffset, DynasmApi, ExecutableBuffer, DynasmLabelApi
};
use std::{
    borrow::Borrow,
    cell::{Ref, RefCell},
    collections::{BTreeMap, HashMap},
};

macro_rules! init_reg_rcx {
    ($ops:expr, $mem:expr, $input_varnode:expr) => {
        let input_addr = $mem.translate_addr($input_varnode.addr())?;
        dynasm!($ops
            ; mov rdi, QWORD input_addr as _
        );
        let size = $input_varnode.size();
        match size {
            1 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov cl, BYTE [rdi]
                );
            }
            2 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov cx, WORD [rdi]
                );
            }
            4 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov ecx, DWORD [rdi]
                );
            }
            8 => {
                dynasm!($ops
                    ; mov rcx, QWORD [rdi]
                );
            },
            _ => unreachable!()
        }
    };
}

macro_rules! fini_reg_rax {
    ($ops:expr, $mem:expr, $input_varnode:expr) => {
        let out_addr = $mem.translate_addr($input_varnode.addr())?;
        dynasm!($ops
            ; mov rdi, QWORD out_addr as _
        );
        let size = $input_varnode.size();
        match size {
            1 => {
                dynasm!($ops
                    ; mov BYTE [rdi], al
                );
            }
            2 => {
                dynasm!($ops
                    ; mov WORD [rdi], ax
                );
            }
            4 => {
                dynasm!($ops
                    ; mov DWORD [rdi], eax
                );
            }
            8 => {
                dynasm!($ops
                    ; mov QWORD [rdi], rax
                );
            },
            _ => unreachable!()
        }
    };
}

/// Jitting pcode translator. Translate pcode by jitting it into x86 asm.
#[derive(Debug, Default)]
pub struct X64ArithJitPcodeTranslator;

macro_rules! ensure_output {
    ($out:ident) => {
        let $out = match $out {
            Some(out) => out,
            None => return Ok(()),
        };
    };
}

/// This macro is used to simplify the implement of various opcode
/// operations which looks quite the same.
///
/// usage: `impl_jit_pcode(opname [operation assembly])
///
/// The operation assembly part is the actual opertaion in x86 assembly which
/// the accumulator value is in rax and the actual value is in rcx.
///
/// An example of int_add implement looks like the following code:
///
/// ```ignore
/// impl_jit_pcode!(int_add [add rax, rcx]);
/// ```
///
/// After the assembly, rax is assumed to be the final output

macro_rules! impl_jit_pcode {
    ($opname:ident [$op:tt $dst_reg:tt, $src_reg:tt $(; $next_ops:tt $next_dests:tt $(, $next_srcs:tt)?)*]) => {
        fn $opname(
            &self,
            ops: &mut dynasmrt::Assembler<Self::Reloc>,
            mem: &mut MemMappedMemory,
            inputs: &[&dyn crate::Varnode],
            out: Option<&dyn crate::Varnode>
        ) -> Result<()> {
            ensure_output!(out);
            dynasm!(ops
                ; xor rax, rax
            );
            for input in inputs {
                if &input.addr().space() == "const" {
                    let value = input.addr().offset();
                    dynasm!(ops
                        ; $op $dst_reg, value as _
                    );
                } else {
                    init_reg_rcx!(ops, mem, input);
                    dynasm!(ops
                        ; $op $dst_reg, $src_reg
                        $(; $next_ops $next_dests $(, $next_srcs)?)*
                    );
                }
            }
            fini_reg_rax!(ops, mem, out);
            Ok(())
        }
    };
    ($opname:ident [$op:tt $src_reg:tt $(; $next_ops:tt $next_dests:tt $(, $next_srcs:tt)?)*]) => {
        fn $opname(
            &self,
            ops: &mut dynasmrt::Assembler<Self::Reloc>,
            mem: &mut MemMappedMemory,
            inputs: &[&dyn crate::Varnode],
            out: Option<&dyn crate::Varnode>
        ) -> Result<()> {
            ensure_output!(out);
            dynasm!(ops
                ; xor rax, rax
            );
            for input in inputs {
                if &input.addr().space() == "const" {
                    let value = input.addr().offset() as i64;
                    // many 1 operand operations don't support immediate
                    // e.g: mul, div..
                    dynasm!(ops
                        ; mov $src_reg, QWORD value
                        ; $op $src_reg
                    );
                } else {
                    init_reg_rcx!(ops, mem, input);
                    dynasm!(ops
                        ; $op $src_reg
                        $(; $next_ops $next_dests $(, $next_srcs)?)*
                    );
                }
            }
            fini_reg_rax!(ops, mem, out);
            Ok(())
        }
    };
}

macro_rules! impl_float_jit_pcode {
    ($opname:ident $asm_block:expr) => {
        fn $opname(
            &self,
            ops: &mut dynasmrt::Assembler<Self::Reloc>,
            mem: &mut MemMappedMemory,
            inputs: &[&dyn crate::Varnode],
            out: Option<&dyn crate::Varnode>
        ) -> Result<()> {
            ensure_output!(out);
            let temp_base = mem.temp_base();
            dynasm!(ops
                ; mov rdi, QWORD temp_base as _
            );
            for input in inputs {
                if &input.addr().space() == "const" {
                    let value = input.addr().offset();
                    dynasm!(ops
                        ; mov QWORD [rdi], 0
                        ; mov QWORD [rdi], value as _
                    );
                    $asm_block(ops, temp_base);
                } else {
                    init_reg_rcx!(ops, mem, input);
                    dynasm!(ops
                        ; xor rax, rax
                        ; mov QWORD [rdi], 0
                        ; mov QWORD [rdi], rcx
                    );
                    $asm_block(ops, temp_base);
                }
            }
            dynasm!(ops
                ; fstp QWORD [rdi]
                ; mov rax, QWORD [rdi]
            );
            fini_reg_rax!(ops, mem, out);
            Ok(())
        }
    };
}

impl ArithPcodeTranslator for X64ArithJitPcodeTranslator {
    type Mem = MemMappedMemory;
    type Reloc = X64Relocation;

    impl_jit_pcode!(copy [mov rax, rcx]);

    fn load(
        &self,
        ops: &mut dynasmrt::Assembler<Self::Reloc>,
        mem: &mut MemMappedMemory,
        inputs: &[&dyn crate::Varnode],
        out: Option<&dyn crate::Varnode>,
    ) -> Result<()> {
        ensure_output!(out);
        dynasm!(ops
            ; xor rax, rax
        );
        init_reg_rcx!(ops, mem, inputs[0]);
        let space_id = inputs[0].addr().offset();
        let offset = inputs[1].addr().offset();
        let addr = mem.trans_addr_under_space_id(space_id, offset)?;
        match out.size() {
            1 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov al, BYTE [rdi]
                );
            }
            2 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov ax, WORD [rdi]
                );
            }
            4 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov eax, DWORD [rdi]
                );
            }
            8 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov rax, QWORD [rdi]
                );
            }
            _ => unreachable!(),
        }
        fini_reg_rax!(ops, mem, out);
        Ok(())
    }

    fn store(
        &self,
        ops: &mut dynasmrt::Assembler<Self::Reloc>,
        mem: &mut MemMappedMemory,
        inputs: &[&dyn crate::Varnode],
        out: Option<&dyn crate::Varnode>,
    ) -> Result<()> {
        ensure_output!(out);
        dynasm!(ops
            ; xor rcx, rcx
        );
        init_reg_rcx!(ops, mem, inputs[2]);
        let space_id = inputs[0].addr().offset();
        let offset = inputs[1].addr().offset();
        let addr = mem.trans_addr_under_space_id(space_id, offset)?;
        match out.size() {
            1 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov BYTE [rdi], cl
                );
            }
            2 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov WORD [rdi], cx
                );
            }
            4 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov DWORD [rdi], ecx
                );
            }
            8 => {
                dynasm!(ops
                    ; mov rdi, QWORD addr as _
                    ; mov QWORD [rdi], rcx
                );
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn piece(
        &self,
        ops: &mut dynasmrt::Assembler<Self::Reloc>,
        mem: &mut MemMappedMemory,
        inputs: &[&dyn crate::Varnode],
        out: Option<&dyn crate::Varnode>,
    ) -> Result<()> {
        ensure_output!(out);
        dynasm!(ops
            ; xor rax, rax
        );
        let most_sig = inputs[0];
        let least_sig = inputs[1];
        let shift_bits = least_sig.size() * 8;
        if most_sig.addr().space() == "const" {
            let value = most_sig.addr().offset();
            dynasm!(ops
                ; mov rax, value as _
                ; shl rax, shift_bits as _
            );
        } else {
            init_reg_rcx!(ops, mem, most_sig);
            dynasm!(ops
                ; shl rcx, shift_bits as _
                ; mov rax, rcx
            );
        };

        if least_sig.addr().space() == "const" {
            let value = least_sig.addr().offset();
            dynasm!(ops
                ; mov rcx, value as _
                ; add rax, rcx
            );
        } else {
            init_reg_rcx!(ops, mem, least_sig);
            dynasm!(ops
                ; add rax, rcx
            );
        }
        fini_reg_rax!(ops, mem, out);
        Ok(())
    }

    fn subpiece(
        &self,
        ops: &mut dynasmrt::Assembler<Self::Reloc>,
        mem: &mut MemMappedMemory,
        inputs: &[&dyn crate::Varnode],
        out: Option<&dyn crate::Varnode>,
    ) -> Result<()> {
        ensure_output!(out);
        dynasm!(ops
            ; xor rax, rax
        );
        let src = inputs[0];
        let bytes = inputs[1];

        let bytes = if bytes.addr().space() == "const" {
            bytes.addr().offset()
        } else {
            return Err(EmuError::InvalidPcode(format!(
                "subpiece got inputs1 non const but {:?}",
                bytes
            )));
        };
        init_reg_rcx!(ops, mem, src);

        let bits = bytes * 8;
        // truncate: shift right then shift left
        dynasm!(ops
            ; shr rcx, bits as _
            ; shl rcx, bits as _
        );

        let output_size = out.size();
        // truncate msb: shift left then shift right
        let bits = (8 - output_size) * 8;
        dynasm!(ops
            ; shl rcx, bits as _
            ; shr rcx, bits as _
            ; mov rax, rcx
        );
        fini_reg_rax!(ops, mem, out);
        Ok(())
    }

    impl_jit_pcode!(int_equal [cmp rax, rcx; mov rbx, 1; cmove rax, rbx]);
    impl_jit_pcode!(int_notequal [cmp rax, rcx; mov rbx, 1; cmovne rax, rbx]);
    impl_jit_pcode!(int_less [cmp rax, rcx; mov rbx, 1; cmovb rax, rbx]);
    impl_jit_pcode!(int_sless [cmp rax, rcx; mov rbx, 1; cmovl rax, rbx]);
    impl_jit_pcode!(int_lessequal [cmp rax, rcx; mov rbx, 1; cmovbe rax, rbx]);
    impl_jit_pcode!(int_slessequal [cmp rax, rcx; mov rbx, 1; cmovle rax, rbx]);
    impl_jit_pcode!(int_zext [mov rax, rcx]);
    impl_jit_pcode!(int_sext [test rcx, rcx; mov rbx, (-1); cmovs rax, rbx]);

    impl_jit_pcode!(int_add [add rax, rcx]);
    impl_jit_pcode!(int_sub [sub rax, rcx]);
    impl_jit_pcode!(int_carry [add rax, rcx; mov rbx, 1; cmovc rax, rbx]);
    impl_jit_pcode!(int_scarry [add rax, rcx; mov rbx, 1; cmovo rax, rbx]);
    impl_jit_pcode!(int_sborrow [sub rax, rcx; mov rbx, 1; cmovc rax, rbx]);
    impl_jit_pcode!(int_2comp [sub rax, rcx]);
    impl_jit_pcode!(int_negate [not rcx; mov rax, rcx]);
    impl_jit_pcode!(int_xor [xor rax, rcx]);
    impl_jit_pcode!(int_and [and rax, rcx]);
    impl_jit_pcode!(int_or [or rax, rcx]);
    impl_jit_pcode!(int_left [shl rax, cl]);
    impl_jit_pcode!(int_right [shr rax, cl]);
    impl_jit_pcode!(int_sright [sar rax, cl]);
    impl_jit_pcode!(int_mult [mul rcx]);
    impl_jit_pcode!(int_div [div rcx]);
    impl_jit_pcode!(int_rem[div rcx; mov rax, rdx]);
    impl_jit_pcode!(int_sdiv [idiv rcx]);
    impl_jit_pcode!(int_srem[idiv rcx; mov rax, rdx]);
    impl_jit_pcode!(bool_negate [not rax; and rax, 1]);
    impl_jit_pcode!(bool_xor [xor rax, rcx; and rax, 1]);
    impl_jit_pcode!(bool_and [and rax, rcx; and rax, 1]);
    impl_jit_pcode!(bool_or [or rax, rcx; and rax, 1]);
    impl_float_jit_pcode!(
        float_equal | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fcom
                ; fld1
                ; fld1
                ; fcmove st0, st2
            );
        }
    );

    impl_float_jit_pcode!(
        float_notequal | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fcom
                ; fld1
                ; fld1
                ; fcmovne st0, st2
            );
        }
    );

    impl_float_jit_pcode!(
        float_less | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fcom
                ; fld1
                ; fld1
                ; fcmovb st0, st2
            );
        }
    );

    impl_float_jit_pcode!(
        float_lessequal | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fcom
                ; fld1
                ; fld1
                ; fcmovbe st0, st2
            );
        }
    );

    impl_float_jit_pcode!(
        float_add | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fadd
            );
        }
    );

    impl_float_jit_pcode!(
        float_sub | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fsub
            );
        }
    );

    impl_float_jit_pcode!(
        float_mult | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fmul
            );
        }
    );

    impl_float_jit_pcode!(
        float_div | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fdiv
            );
        }
    );

    impl_float_jit_pcode!(
        float_neg | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fldz
                ; fsub
            );
        }
    );

    impl_float_jit_pcode!(
        float_abs | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fabs
            );
        }
    );

    impl_float_jit_pcode!(
        float_sqrt | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fsqrt
            );
        }
    );

    impl_float_jit_pcode!(
        float_ceil | ops: &mut Assembler<Self::Reloc>,
        temp_base | {
            dynasm!(ops
                ; fstp QWORD [temp_base as _]
                ; movsd xmm1, QWORD [temp_base as _]
                ; roundsd xmm1, QWORD [temp_base as _], 0b1010
                ; movsd QWORD [temp_base as _], xmm1
                ; fld QWORD [temp_base as _]
            );
        }
    );

    impl_float_jit_pcode!(
        float_floor | ops: &mut Assembler<Self::Reloc>,
        temp_base | {
            dynasm!(ops
                ; fstp QWORD [temp_base as _]
                ; movsd xmm1, QWORD [temp_base as _]
                ; roundsd xmm1, QWORD [temp_base as _], 0b1001
                ; movsd QWORD [temp_base as _], xmm1
                ; fld QWORD [temp_base as _]
            );
        }
    );

    impl_float_jit_pcode!(
        float_round | ops: &mut Assembler<Self::Reloc>,
        temp_base | {
            dynasm!(ops
                ; fstp QWORD [temp_base as _]
                ; movsd xmm1, QWORD [temp_base as _]
                ; roundsd xmm1, QWORD [temp_base as _], 0b1000
                ; movsd QWORD [temp_base as _], xmm1
                ; fld QWORD [temp_base as _]
            );
        }
    );

    impl_float_jit_pcode!(
        float_nan | ops: &mut Assembler<Self::Reloc>,
        _temp_base | {
            dynasm!(ops
                ; fldz
                ; fcom
                ; fld1
                ; fldz
                ; fcmovu st0, st1
            );
        }
    );

    impl_float_jit_pcode!(
        int2float | _ops: &mut Assembler<Self::Reloc>,
        _temp_base | {}
    );

    impl_float_jit_pcode!(
        float2float | _ops: &mut Assembler<Self::Reloc>,
        _temp_base | {}
    );

    impl_float_jit_pcode!(
        trunc | ops: &mut Assembler<Self::Reloc>,
        temp_base | {
            dynasm!(ops
                ; fstp QWORD [temp_base as _]
                ; movsd xmm1, QWORD [temp_base as _]
                ; roundsd xmm1, QWORD [temp_base as _], 0b1011
                ; movsd QWORD [temp_base as _], xmm1
                ; fld QWORD [temp_base as _]
            );
        }
    );
}

/// Pcode cache only block translator that does not translate anything not in the cache.
/// In other words, no actual translation engine is included.
pub struct PcodeCacheOnlyTranslator<'a, PcodeTrans: ArithPcodeTranslator> {
    /// addr to index into `pcode_cache`
    cache: BTreeMap<(usize, usize), &'a dyn PcodeOp>,
    block_cache: RefCell<HashMap<usize, (AssemblyOffset, ExecutableBuffer)>>,
    pcode_trans: PcodeTrans,
    /// user functions: (id, param) -> return value
    user_defined: HashMap<usize, extern "C" fn(usize, &mut Vec<&dyn Varnode>) -> usize>,
}

impl<'a, PcodeTrans: ArithPcodeTranslator> std::fmt::Debug
    for PcodeCacheOnlyTranslator<'a, PcodeTrans>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PcodeCacheOnlyTranslator")
            .field("cache", &self.cache)
            .field("block_cache", &self.block_cache)
            .field("pcode_trans", &self.pcode_trans)
            .finish()
    }
}

impl<'a, PcodeTrans: ArithPcodeTranslator<Reloc = X64Relocation, Mem = MemMappedMemory>>
    PcodeCacheOnlyTranslator<'a, PcodeTrans>
{
    pub fn new(pcode_trans: PcodeTrans) -> Self {
        Self {
            cache: BTreeMap::new(),
            block_cache: RefCell::new(HashMap::new()),
            user_defined: HashMap::new(),
            pcode_trans,
        }
    }

    pub fn from_cache(
        cache: BTreeMap<(usize, usize), &'a dyn PcodeOp>,
        pcode_trans: PcodeTrans,
    ) -> Self {
        Self {
            cache,
            block_cache: RefCell::new(HashMap::default()),
            pcode_trans,
            user_defined: HashMap::new(),
        }
    }

    pub fn add_userop(
        &mut self,
        id: usize,
        func: extern "C" fn(usize, &mut Vec<&dyn Varnode>) -> usize,
    ) {
        self.user_defined.insert(id, func);
    }

    pub fn add_pcode(&mut self, seq: &dyn SeqNum, pcode: &'a dyn PcodeOp) {
        self.cache.insert((seq.addr().offset() as usize, seq.uniq() as usize), pcode);
    }

    extern "C" fn jump_stub(&mut self, mem: &mut MemMappedMemory, target_addr: &dyn Address) {
        let addr = mem.translate_addr(target_addr).unwrap();
        if let Some((offset, code)) = self.block_cache.borrow().get(&addr) {
            let f: extern "win64" fn() -> () = unsafe { std::mem::transmute(code.ptr(*offset)) };
            f();
            unreachable!();
        };

        let (offset, code) = self.translate(mem, target_addr).unwrap();
        let f: extern "win64" fn() -> () = unsafe { std::mem::transmute(code.ptr(*offset)) };
        f();
    }

    fn translate_branch(
        &self,
        mem: &mut MemMappedMemory,
        pcode: &dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let addr = mem.translate_addr(pcode.inputs()[0].addr())?;
        match self.block_cache.borrow().get(&addr) {
            Some((offset, code)) => {
                let target = code.ptr(*offset);
                dynasm!(ops
                    ; mov rax, QWORD target as _
                    ; jmp rax
                );
                return Ok(());
            }
            None => {}
        }

        let (offset, code) = self.translate(mem, pcode.inputs()[0].addr())?;
        let target = code.borrow().ptr(offset.to_owned());
        dynasm!(ops
            ; mov rax, QWORD target as _
            ; jmp rax
        );
        Ok(())
    }

    fn translate_cbranch(
        &self,
        mem: &mut MemMappedMemory,
        pcode: &dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let inputs = pcode.inputs();
        let predicate = mem.translate_addr(inputs[0].addr())?;
        let addr = mem.translate_addr(inputs[1].addr())?;
        let cached = self.block_cache.borrow();
        let target = match cached.get(&addr) {
            Some((offset, code)) => code.ptr(*offset),
            None => {
                let (offset, code) = self.translate(mem, inputs[1].addr())?;
                code.borrow().ptr(offset.to_owned())
            }
        };

        dynasm!(ops
            ; mov al, BYTE [predicate as _]
            ; test al, al
            ; jz ->no_jmp
            ; mov rbx, QWORD target as _
            ; jmp rbx
            ; ->no_jmp:
        );
        Ok(())
    }

    fn translate_branchind(
        &self,
        mem: &mut MemMappedMemory,
        pcode: &'a dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let inputs = pcode.inputs();
        let addr = inputs[0].addr() as *const _ as *const () as usize;

        let self_ptr = self as *const _ as usize;
        let mem_ptr = mem as *const _ as usize;

        let stub = Self::jump_stub as usize;

        dynasm!(ops
            ; mov rdi, QWORD self_ptr as _
            ; mov rsi, QWORD mem_ptr as _
            ; mov rdx, QWORD addr as _
            ; mov rax, QWORD stub as _
            ; jmp rax
        );
        Ok(())
    }

    fn translate_call(
        &self,
        mem: &mut MemMappedMemory,
        pcode: &'a dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let addr = mem.translate_addr(pcode.inputs()[0].addr())?;
        let cached = self.block_cache.borrow();
        let target = match cached.get(&addr) {
            Some((offset, code)) => code.ptr(*offset),
            None => {
                let (offset, code) = self.translate(mem, pcode.inputs()[0].addr())?;
                code.borrow().ptr(offset.to_owned())
            }
        };

        dynasm!(ops
            ; mov rax, QWORD target as _
            ; call rax
        );
        Ok(())
    }

    fn translate_callind(
        &self,
        mem: &mut MemMappedMemory,
        pcode: &'a dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let inputs = pcode.inputs();
        let addr = mem.translate_addr(inputs[0].addr())?;

        let self_ptr = self as *const _ as usize;
        let mem_ptr = mem as *const _ as usize;

        let stub = Self::jump_stub as usize;

        dynasm!(ops
            ; mov rdi, QWORD self_ptr as _
            ; mov rsi, QWORD mem_ptr as _
            ; mov rdx, QWORD addr as _
            ; mov rax, QWORD stub as _
            ; call rax
        );
        Ok(())
    }

    fn translate_userdefined(
        &self,
        _mem: &mut MemMappedMemory,
        pcode: &'a dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        let params = Box::leak(Box::new(pcode.inputs())) as *const _ as usize;
        let userop_id = pcode.inputs()[0].addr().offset() as usize;
        let func = (self
            .user_defined
            .get(&userop_id)
            .ok_or(EmuError::InvalidPcode(format!(
                "No such userop with id {}",
                userop_id
            )))?) as *const _ as usize;
        dynasm!(ops
            ; mov rdi, QWORD userop_id as _
            ; mov rsi, QWORD params as _
            ; mov rax, QWORD func as _
            ; call rax
        );
        Ok(())
    }

    fn translate_return(
        &self,
        _mem: &mut MemMappedMemory,
        _pcode: &'a dyn PcodeOp,
        ops: &mut Assembler<X64Relocation>,
    ) -> Result<()> {
        dynasm!(ops
            ; ret
        );
        Ok(())
    }
}

impl<'a, PcodeTrans: ArithPcodeTranslator<Reloc = X64Relocation, Mem = MemMappedMemory>>
    BlockTranslator<MemMappedMemory> for PcodeCacheOnlyTranslator<'a, PcodeTrans>
{
    fn translate(
        &self,
        mem: &mut MemMappedMemory,
        addr: &dyn Address,
    ) -> Result<(Ref<AssemblyOffset>, Ref<ExecutableBuffer>)> {
        let cache_op_iter = self
            .cache
            .iter()
            .skip_while(|c| (*c.0).0 != addr.offset() as usize);

        let mut ops = x64::Assembler::new().unwrap();

        dynasm!(ops
            ; .arch x64
        );
        let offset = ops.offset();

        for (_, pcode) in cache_op_iter {
            use crate::OpCode::*;

            match self.pcode_trans.translate_pcode(&mut ops, mem, *pcode) {
                Ok(_) => {}
                Err(EmuError::UnableToTranslate) => match pcode.opcode() {
                    Branch => {
                        self.translate_branch(mem, *pcode, &mut ops)?;
                    }
                    Cbranch => {
                        self.translate_cbranch(mem, *pcode, &mut ops)?;
                    }
                    BranchInd => {
                        self.translate_branchind(mem, *pcode, &mut ops)?;
                    }
                    Call => {
                        self.translate_call(mem, *pcode, &mut ops)?;
                    }
                    CallInd => {
                        self.translate_callind(mem, *pcode, &mut ops)?;
                    }
                    CallOther => {
                        self.translate_userdefined(mem, *pcode, &mut ops)?;
                    }
                    Return => {
                        self.translate_return(mem, *pcode, &mut ops)?;
                    }
                    _ => return Err(EmuError::UnableToTranslate),
                },
                Err(e) => return Err(e),
            }
        }

        let block_result = ops.finalize().unwrap();

        let translated_addr = mem.translate_addr(addr)?;

        self.block_cache
            .borrow_mut()
            .insert(translated_addr, (offset, block_result));

        let res = Ref::map(self.block_cache.borrow(), |block_cache| {
            block_cache.get(&translated_addr).unwrap()
        });

        let offset = Ref::map(Ref::clone(&res), |res| &res.0);
        let code = Ref::map(res, |res| &res.1);

        Ok((offset, code))
    }
}

#[test]
fn test_single_block() {
    use crate::backend::plain::*;
    use crate::emu::Emulator;
    use crate::plain_pcode;
    use crate::OpCode::*;

    let insns = vec![
        plain_pcode!(0x1000:0| ("register", 0, 8) = [Copy] ("const", 8, 8)),
        plain_pcode!(0x1001:0| ("register", 0x8, 8) = [Copy] ("const", 8, 8)),
        plain_pcode!(0x1002:0| ("register", 0, 8) = [IntAdd] ("register", 0, 8) ("register", 8, 8)),
        plain_pcode!(0x1003:0| [Return]),
    ];

    let mut mem = MemMappedMemory::new().unwrap();
    mem.insert_space(0, "register".to_string()).unwrap();
    mem.insert_space(1, "ram".to_string()).unwrap();

    let mut block_trans = PcodeCacheOnlyTranslator::new(X64ArithJitPcodeTranslator::default());

    for ins in insns.iter() {
        block_trans.add_pcode(ins.seq(), ins);
    }

    let mut emu = Emulator::new(block_trans, mem);

    emu.run(&PlainAddress {
        space: "ram".to_string(),
        offset: 0x1000,
    })
    .unwrap();

    assert_eq!(
        emu.mem
            .read_mem::<u64>(&PlainAddress {
                space: "register".to_string(),
                offset: 0x0
            })
            .unwrap(),
        0x10
    );
}

#[test]
fn test_two_blocks() {
    use crate::backend::plain::*;
    use crate::emu::Emulator;
    use crate::plain_pcode;
    use crate::OpCode::*;

    let insns = vec![
        plain_pcode!(0x1000:0| ("register", 0, 8) = [Copy] ("const", 8, 8)),
        plain_pcode!(0x1001:0| ("register", 0x8, 8) = [Copy] ("const", 8, 8)),
        plain_pcode!(0x1002:0| ("register", 0, 8) = [IntAdd] ("register", 0, 8) ("register", 8, 8)),
        plain_pcode!(0x1010:0| [Branch] ("ram", 0x1011, 8)),
        plain_pcode!(0x1011:0| [Return]),
    ];

    let mut mem = MemMappedMemory::new().unwrap();
    mem.insert_space(0, "register".to_string()).unwrap();
    mem.insert_space(1, "ram".to_string()).unwrap();

    let mut block_trans = PcodeCacheOnlyTranslator::new(X64ArithJitPcodeTranslator::default());

    for ins in insns.iter() {
        block_trans.add_pcode(ins.seq(), ins);
    }

    let mut emu = Emulator::new(block_trans, mem);

    emu.run(&PlainAddress {
        space: "ram".to_string(),
        offset: 0x1000,
    })
    .unwrap();

    assert_eq!(
        emu.mem
            .read_mem::<u64>(&PlainAddress {
                space: "register".to_string(),
                offset: 0x0
            })
            .unwrap(),
        0x10
    );
}
