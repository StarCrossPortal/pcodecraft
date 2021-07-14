use std::collections::{BTreeMap, HashMap};
use dynasmrt::{x64, DynasmApi, AssemblyOffset, ExecutableBuffer};
use dynasm::dynasm;
use crate::PcodeOp;
use super::{MemMappedMemory, BlockTranslator, EmuError, Result};

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

        use crate::OpCode::*;

        let ops = x64::Assembler::new().unwrap();

        match cached_op.opcode() {
            IntAdd => {
                todo!("do the actual translation")
            },
            _ => {}
        }

        todo!("implement the op translation")
    }
}