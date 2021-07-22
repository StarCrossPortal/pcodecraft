use std::{collections::HashMap, convert::TryInto, num::TryFromIntError};

use dynasmrt::{relocations::Relocation, Assembler};
use memmap2::{MmapMut};
use thiserror::Error;

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::PcodeCacheOnlyTranslator;

use crate::{Address, OpCode, PcodeOp, Varnode};

/// single pcode translate
pub trait PcodeTranslator: std::fmt::Debug {
    type Reloc: Relocation;
    type Mem: Memory;

    fn int_add(
        &mut self,
        ops: &mut Assembler<Self::Reloc>,
        mem: &mut Self::Mem,
        inputs: &[&dyn Varnode],
        out: &dyn Varnode,
    ) -> Result<()>;
    // todo: other operations..

    fn translate_pcode(
        &mut self,
        ops: &mut Assembler<Self::Reloc>,
        mem: &mut Self::Mem,
        pcode: &dyn PcodeOp,
    ) -> Result<()> {
        use OpCode::*;

        match pcode.opcode() {
            IntAdd => {
                let inputs = pcode.inputs();
                let output = pcode.output();

                // without output, IntAdd takes no effect then
                if output.is_none() {
                    return Ok(());
                }

                let output = output.unwrap();
                self.int_add(ops, mem, &inputs, output)?;
            }
            _ => todo!("other opcodes"),
        }
        todo!()
    }
}

#[derive(Debug, Error)]
pub enum EmuError {
    /// Cache-only translator requires every address is in the cache. If not, this error indicates
    /// that it is unable to continue execution.
    #[error("unable to continue execution as offset {0} is not in cache")]
    NotInCache(usize),
    /// Host addressing is not enough for target machine.
    #[error("Offset is too large to fit into host machine")]
    OffsetTooLarge(#[from] TryFromIntError),
    #[error("IO error")]
    IoError(#[from] std::io::Error),
}

// TODO: implement Error for EmuError

pub type Result<T> = std::result::Result<T, EmuError>;

pub trait Memory: std::fmt::Debug {
    /// This memory's actual addressing
    type MemAddr;

    /// Translate the pcode addr into this memory's addressing
    fn translate_addr(&mut self, addr: &dyn Address) -> Result<Self::MemAddr>;
}

/// Emulator Memory
/// `BlockTranslator` is responsible for translating a single block into executable pcode
pub trait BlockTranslator<Mem: Memory>: std::fmt::Debug {
    fn translate(&mut self, mem: &mut Mem, addr: usize) -> Result<*const u8>;
}

#[derive(Debug)]
pub struct Emulator<Trans, Mem>
where
    Trans: BlockTranslator<Mem>,
    Mem: Memory,
{
    /// translator used to translate the blocks
    trans: Trans,
    /// internal memory implementation
    mem: Mem,
}

impl<Trans, Mem> Emulator<Trans, Mem>
where
    Trans: BlockTranslator<Mem>,
    Mem: Memory,
{
    pub fn new(trans: Trans, mem: Mem) -> Self {
        Self { trans, mem }
    }

    /// Run until the end of the program
    pub fn run(&mut self, entry: usize) -> Result<()> {
        // translate the fall back block then call it.
        // Note that only the first block should be reside in a call, as it can be returned.
        let entry_block = self.trans.translate(&mut self.mem, entry)?;
        let entry_func: extern "C" fn() = unsafe { std::mem::transmute(entry_block) };
        entry_func();
        Ok(())
    }
}

/// Plain memory that gets mapped into the system already.
#[derive(Debug)]
pub struct MemMappedMemory {
    regions: HashMap<String, MmapMut>,
    /// the base of the register
    reg_base: usize,
}

impl MemMappedMemory {
    pub fn new(reg_base: usize) -> Self {
        Self {
            reg_base,
            regions: HashMap::new(),
        }
    }
}

impl Memory for MemMappedMemory {
    type MemAddr = usize;

    fn translate_addr(&mut self, addr: &dyn Address) -> Result<Self::MemAddr> {
        let offset: usize = addr
            .offset()
            .try_into()?;

        let default_size = (offset & (!0xfff)) + 0x2000;

        let region_entry = self.regions.entry(addr.space());
        let region = region_entry.or_insert(MmapMut::map_anon(default_size)?.make_exec()?.make_mut()?);

        if offset >= region.len() {
            // Current region is unable to store the required offset, enlarge it
            let mut new_region = MmapMut::map_anon(default_size)?.make_exec()?.make_mut()?;
            new_region.as_mut().copy_from_slice(region.as_ref());
            let final_addr = new_region.as_ptr() as usize + offset;
            *self.regions.get_mut(&addr.space()).unwrap() = new_region;
            Ok(final_addr)
        } else {
            Ok(region.as_ptr() as usize + offset)
        }
    }
}
