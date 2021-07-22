#![allow(unused_parens)]
use super::{ArithPcodeTranslator, BlockTranslator, MemMappedMemory, Result};
use crate::{PcodeOp, emu::{EmuError, Memory}};
use dynasm::dynasm;
use dynasmrt::{Assembler, AssemblyOffset, DynasmApi, ExecutableBuffer, x64::{self, X64Relocation}};
use std::collections::{BTreeMap, HashMap};

macro_rules! init_reg_rcx {
    ($ops:expr, $mem:expr, $input_varnode:expr) => {
        let input_addr = $mem.translate_addr($input_varnode.addr())?;
        let size = $input_varnode.size();
        match size {
            1 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov cl, BYTE [input_addr as _]
                );
            }
            2 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov cx, WORD [input_addr as _]
                );
            }
            4 => {
                dynasm!($ops
                    ; xor rcx, rcx
                    ; mov ecx, DWORD [input_addr as _]
                );
            }
            8 => {
                dynasm!($ops
                    ; mov rcx, QWORD [input_addr as _]
                );
            },
            _ => unreachable!()
        }
    };
}

macro_rules! fini_reg_rax {
    ($ops:expr, $mem:expr, $input_varnode:expr) => {
        let out_addr = $mem.translate_addr($input_varnode.addr())?;
        let size = $input_varnode.size();
        match size {
            1 => {
                dynasm!($ops
                    ; mov BYTE [out_addr as _], al
                );
            }
            2 => {
                dynasm!($ops
                    ; mov WORD [out_addr as _], ax
                );
            }
            4 => {
                dynasm!($ops
                    ; mov DWORD [out_addr as _], eax
                );
            }
            8 => {
                dynasm!($ops
                    ; mov QWORD [out_addr as _], rax
                );
            },
            _ => unreachable!()
        }
    };
}

/// Jitting pcode translator. Translate pcode by jitting it into x86 asm.
#[derive(Debug)]
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
            &mut self,
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
            &mut self,
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
                    // many 1 operand operations don't support immediate
                    // e.g: mul, div..
                    dynasm!(ops
                        ; mov $src_reg, value as _
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
            &mut self,
            ops: &mut dynasmrt::Assembler<Self::Reloc>,
            mem: &mut MemMappedMemory,
            inputs: &[&dyn crate::Varnode],
            out: Option<&dyn crate::Varnode>
        ) -> Result<()> {
            ensure_output!(out);
            let temp_base = mem.temp_base();
            for input in inputs {
                if &input.addr().space() == "const" {
                    let value = input.addr().offset();
                    dynasm!(ops
                        ; mov QWORD [temp_base as _], 0
                        ; mov QWORD [temp_base as _], value as _
                    );
                    $asm_block(ops, temp_base);
                } else {
                    init_reg_rcx!(ops, mem, input);
                    dynasm!(ops
                        ; xor rax, rax
                        ; mov QWORD [temp_base as _], 0 
                        ; mov QWORD [temp_base as _], rcx
                    );
                    $asm_block(ops, temp_base);
                }
            }
            dynasm!(ops
                ; fstp QWORD [temp_base as _]
                ; mov rax, QWORD [temp_base as _]
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
        &mut self,
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
                    ; mov al, BYTE [addr as _]
                );
            }
            2 => {
                dynasm!(ops
                    ; mov ax, WORD [addr as _]
                );
            }
            4 => {
                dynasm!(ops
                    ; mov eax, DWORD [addr as _]
                );
            }
            8 => {
                dynasm!(ops
                    ; mov rax, QWORD [addr as _]
                );
            }
            _ => unreachable!(),
        }
        fini_reg_rax!(ops, mem, out);
        Ok(())
    }

    fn store(
        &mut self,
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
                    ; mov BYTE [addr as _], cl
                );
            }
            2 => {
                dynasm!(ops
                    ; mov WORD [addr as _], cx
                );
            }
            4 => {
                dynasm!(ops
                    ; mov DWORD [addr as _], ecx
                );
            }
            8 => {
                dynasm!(ops
                    ; mov QWORD [addr as _], rcx
                );
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn piece(
        &mut self,
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
        &mut self,
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
            return Err(EmuError::InvalidPcode(format!("subpiece got inputs1 non const but {:?}", bytes)));
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
    impl_jit_pcode!(bool_negate [not al; and rax, 1]);
    impl_jit_pcode!(bool_xor [xor rax, rcx; and rax, 1]);
    impl_jit_pcode!(bool_and [and rax, rcx; and rax, 1]);
    impl_jit_pcode!(bool_or [or rax, rcx; and rax, 1]);
    impl_float_jit_pcode!(float_equal |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fcom
            ; fld1
            ; fld1
            ; fcmove st0, st2
        );
    });

    impl_float_jit_pcode!(float_notequal |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fcom
            ; fld1
            ; fld1
            ; fcmovne st0, st2
        );
    });

    impl_float_jit_pcode!(float_less |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fcom
            ; fld1
            ; fld1
            ; fcmovb st0, st2
        );
    });

    impl_float_jit_pcode!(float_lessequal |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fcom
            ; fld1
            ; fld1
            ; fcmovbe st0, st2
        );
    });

    impl_float_jit_pcode!(float_add |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fadd
        );
    });

    impl_float_jit_pcode!(float_sub |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fsub
        );
    });

    impl_float_jit_pcode!(float_mult |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fmul
        );
    });

    impl_float_jit_pcode!(float_div |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fdiv
        );
    });

    impl_float_jit_pcode!(float_neg |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fldz
            ; fsub
        );
    });

    impl_float_jit_pcode!(float_abs |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fabs
        );
    });

    impl_float_jit_pcode!(float_sqrt |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fsqrt
        );
    });

    impl_float_jit_pcode!(float_ceil |ops: &mut Assembler<Self::Reloc>, temp_base| {
        dynasm!(ops
            ; fstp QWORD [temp_base as _]
            ; movsd xmm1, QWORD [temp_base as _]
            ; roundsd xmm1, QWORD [temp_base as _], 0b1010
            ; movsd QWORD [temp_base as _], xmm1
            ; fld QWORD [temp_base as _]
        );
    });

    impl_float_jit_pcode!(float_floor |ops: &mut Assembler<Self::Reloc>, temp_base| {
        dynasm!(ops
            ; fstp QWORD [temp_base as _]
            ; movsd xmm1, QWORD [temp_base as _]
            ; roundsd xmm1, QWORD [temp_base as _], 0b1001
            ; movsd QWORD [temp_base as _], xmm1
            ; fld QWORD [temp_base as _]
        );
    });

    impl_float_jit_pcode!(float_round |ops: &mut Assembler<Self::Reloc>, temp_base| {
        dynasm!(ops
            ; fstp QWORD [temp_base as _]
            ; movsd xmm1, QWORD [temp_base as _]
            ; roundsd xmm1, QWORD [temp_base as _], 0b1000
            ; movsd QWORD [temp_base as _], xmm1
            ; fld QWORD [temp_base as _]
        );
    });

    impl_float_jit_pcode!(float_nan |ops: &mut Assembler<Self::Reloc>, _temp_base| {
        dynasm!(ops
            ; fldz
            ; fcom
            ; fld1
            ; fldz
            ; fcmovu st0, st1
        );
    });

    impl_float_jit_pcode!(int2float |_ops: &mut Assembler<Self::Reloc>, _temp_base| {
    });


    impl_float_jit_pcode!(float2float |_ops: &mut Assembler<Self::Reloc>, _temp_base| {
    });

    impl_float_jit_pcode!(trunc |ops: &mut Assembler<Self::Reloc>, temp_base| {
        dynasm!(ops
            ; fstp QWORD [temp_base as _]
            ; movsd xmm1, QWORD [temp_base as _]
            ; roundsd xmm1, QWORD [temp_base as _], 0b1011
            ; movsd QWORD [temp_base as _], xmm1
            ; fld QWORD [temp_base as _]
        );
    });
}

/// Pcode cache only block translator that does not translate anything not in the cache.
/// In other words, no actual translation engine is included.
#[derive(Debug)]
pub struct PcodeCacheOnlyTranslator<'a, PcodeTrans: ArithPcodeTranslator> {
    /// addr to index into `pcode_cache`
    cache: BTreeMap<usize, &'a dyn PcodeOp>,
    block_cache: HashMap<usize, (AssemblyOffset, ExecutableBuffer)>,
    pcode_trans: PcodeTrans,
}

impl<'a, PcodeTrans: ArithPcodeTranslator> PcodeCacheOnlyTranslator<'a, PcodeTrans> {
    pub fn from_cache(cache: BTreeMap<usize, &'a dyn PcodeOp>, pcode_trans: PcodeTrans) -> Self {
        Self {
            cache,
            block_cache: HashMap::default(),
            pcode_trans,
        }
    }

    pub fn add_pcode(&mut self, pcode: &'a dyn PcodeOp, addr: usize) {
        self.cache.insert(addr, pcode);
    }
}

impl<'a, PcodeTrans: ArithPcodeTranslator<Reloc = X64Relocation, Mem = MemMappedMemory>>
    BlockTranslator<MemMappedMemory> for PcodeCacheOnlyTranslator<'a, PcodeTrans>
{
    fn translate(&mut self, mem: &mut MemMappedMemory, addr: usize) -> Result<*const u8> {
        let cache_op_iter = self.cache.iter().skip_while(|c| *c.0 != addr);

        let mut ops = x64::Assembler::new().unwrap();

        dynasm!(ops
            ; .arch x64
        );
        let offset = ops.offset();

        for (_, pcode) in cache_op_iter {
            self.pcode_trans.translate_pcode(&mut ops, mem, *pcode)?;
        }

        let block_result = ops.finalize().unwrap();
        let buf = block_result.ptr(offset);

        self.block_cache.insert(addr, (offset, block_result));

        Ok(buf)
    }
}
