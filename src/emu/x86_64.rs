use super::{BlockTranslator, MemMappedMemory, PcodeTranslator, Result};
use crate::{emu::Memory, PcodeOp};
use dynasm::dynasm;
use dynasmrt::{
    x64::{self, X64Relocation},
    AssemblyOffset, DynasmApi, ExecutableBuffer,
};
use std::collections::{BTreeMap, HashMap};

/// Jitting pcode translator. Translate pcode by jitting it into x86 asm.
#[derive(Debug)]
pub struct X64JitPcodeTranslator {
    /// register base address
    reg_base: usize,
}

impl PcodeTranslator for X64JitPcodeTranslator {
    type Mem = MemMappedMemory;
    type Reloc = X64Relocation;

    fn int_add(
        &mut self,
        ops: &mut dynasmrt::Assembler<Self::Reloc>,
        mem: &MemMappedMemory,
        inputs: &[&dyn crate::Varnode],
        out: &dyn crate::Varnode,
    ) -> Result<()> {
        dynasm!(ops
            ; xor rax, rax // rax is the accumulation value
        );

        for input in inputs {
            if &input.addr().space() == "const" {
                // add a const
                let value = input.addr().offset();
                dynasm!(ops
                    ; add rax, value as _
                );
            } else {
                let input_addr = mem.translate(input.addr())?;
                let size = input.size();
                match size {
                    1 => {
                        dynasm!(ops
                            ; xor rdx, rdx
                            ; mov dl, BYTE [input_addr as _]
                            ; add rax, rdx
                        );
                    }
                    2 => {
                        dynasm!(ops
                            ; xor rdx, rdx
                            ; mov dx, WORD [input_addr as _]
                            ; add rax, rdx
                        );
                    }
                    4 => {
                        dynasm!(ops
                            ; xor rdx, rdx
                            ; mov edx, DWORD [input_addr as _]
                            ; add rax, rdx
                        );
                    }
                    8 => {
                        dynasm!(ops
                            ; add rax, QWORD [input_addr as _]
                        );
                    }
                    _ => unreachable!(),
                }
            }
        }

        let out_addr = mem.translate(out.addr())?;
        let size = out.size();

        match size {
            1 => {
                dynasm!(ops
                    ; mov BYTE [out_addr as _], al
                );
            }
            2 => {
                dynasm!(ops
                    ; mov WORD [out_addr as _], ax
                );
            }
            4 => {
                dynasm!(ops
                    ; mov DWORD [out_addr as _], eax
                );
            }
            8 => {
                dynasm!(ops
                    ; mov QWORD [out_addr as _], rax
                );
            }
            _ => unreachable!(),
        }

        Ok(())
    }
}

/// Pcode cache only block translator that does not translate anything not in the cache.
/// In other words, no actual translation engine is included.
#[derive(Debug)]
pub struct PcodeCacheOnlyTranslator<'a, PcodeTrans: PcodeTranslator> {
    /// addr to index into `pcode_cache`
    cache: BTreeMap<usize, &'a dyn PcodeOp>,
    block_cache: HashMap<usize, (AssemblyOffset, ExecutableBuffer)>,
    pcode_trans: PcodeTrans,
}

impl<'a, PcodeTrans: PcodeTranslator> PcodeCacheOnlyTranslator<'a, PcodeTrans> {
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

impl<'a, PcodeTrans: PcodeTranslator<Reloc = X64Relocation, Mem = MemMappedMemory>>
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