use std::{collections::{BTreeMap, HashMap}};
use dynasmrt::{AssemblyOffset, ExecutableBuffer};
use memmap2::Mmap;

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
use x86_64::*;

use crate::PcodeOp;

#[derive(Debug)]
pub enum EmuError {
    /// Cache-only translator requires every address is in the cache. If not, this error indicates
    /// that it is unable to continue execution.
    NotInCache(usize),
}

pub type Result<T> = std::result::Result<T, EmuError>;

pub trait Memory : std::fmt::Debug {

}

/// Emulator Memory
/// `BlockTranslator` is responisble for translating a single block into executable pcode
pub trait BlockTranslator<Mem: Memory> : std::fmt::Debug {
    fn translate(&mut self, mem: &mut Mem, addr: usize) -> Result<*const u8>;
}

#[derive(Debug)]
pub struct Emulator<Trans, Mem> where Trans: BlockTranslator<Mem>, Mem: Memory {
    /// translator used to translate the blocks
    trans: Trans,
    /// internal memory implementation
    mem: Mem
}

impl<Trans, Mem> Emulator<Trans, Mem> where Trans: BlockTranslator<Mem>, Mem: Memory {
    pub fn new(trans: Trans, mem: Mem) -> Self {
        Self {
            trans, mem
        }
    }

    /// Run until the end of the program
    pub fn run(&mut self, entry: usize) -> Result<()> {
        // translate the fall back block then call it.
        // Note that only the first block should be reside in a call, as it can be returned.
        let entry_block = self.trans.translate(&mut self.mem, entry);
        let entry_func : extern "C" fn () = unsafe {
            std::mem::transmute(entry_block)
        };
        entry_func();
        Ok(())
    }
}

/// Plain memory that gets mapped into the system already.
#[derive(Debug)]
pub struct MemMappedMemory {
    /// vec of (begin, size). All these memories are actually mapped.
    regions: Vec<Mmap>
}


impl Memory for MemMappedMemory {}

/// Pcode cache only block translator that does not translate anything not in the cache.
/// In other words, no actual translation engine is included.
#[derive(Debug, Default)]
pub struct PcodeCacheOnlyTranslator<'a> {
    /// addr to index into `pcode_cache`
    cache: BTreeMap<usize, &'a dyn PcodeOp>,
    block_cache: HashMap<usize, (AssemblyOffset, ExecutableBuffer)>,
}

impl<'a> PcodeCacheOnlyTranslator<'a> {
    fn from_cache(cache: BTreeMap<usize, &'a dyn PcodeOp>) -> Self {
        Self {
            cache,
            block_cache: HashMap::default()
        }
    }

    fn add_pcode(&mut self, pcode: &'a dyn PcodeOp, addr: usize) {
        self.cache.insert(addr, pcode);
    }
}

impl<'a> BlockTranslator<MemMappedMemory> for PcodeCacheOnlyTranslator<'a> {
    fn translate(&mut self, _mem: &mut MemMappedMemory, addr: usize) -> Result<*const u8> {

        let cached_op = match self.cache.get(&addr) {
            Some(op) => op,
            None => return Err(EmuError::NotInCache(addr))
        };

        todo!("implement the op translation")
    }
}