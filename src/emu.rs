use std::{collections::HashMap, convert::TryInto, num::TryFromIntError};

use dynasmrt::{relocations::Relocation, Assembler};
use memmap2::MmapMut;
use thiserror::Error;

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::PcodeCacheOnlyTranslator;

use crate::{Address, OpCode, PcodeOp, Varnode};

macro_rules! def_op {
    ($opname:ident) => {
        fn $opname(
            &mut self,
            _ops: &mut Assembler<Self::Reloc>,
            _mem: &mut Self::Mem,
            _inputs: &[&dyn Varnode],
            _out: Option<&dyn Varnode>,
        ) -> Result<()> {
            todo!()
        }
    };
}

/// single pcode translate
pub trait PcodeTranslator: std::fmt::Debug {
    type Reloc: Relocation;
    type Mem: Memory;

    // ref: https://ghidra.re/courses/languages/html/pcoderef.html
    def_op!(copy);
    def_op!(load);
    def_op!(store);
    def_op!(branch);
    def_op!(cbranch);
    def_op!(branchind);
    def_op!(call);
    def_op!(callind);
    def_op!(userdefined);
    def_op!(return_op);
    def_op!(piece);
    def_op!(subpiece);
    def_op!(int_equal);
    def_op!(int_notequal);
    def_op!(int_less);
    def_op!(int_sless);
    def_op!(int_lessequal);
    def_op!(int_slessequal);
    def_op!(int_zext);
    def_op!(int_sext);
    def_op!(int_add);
    def_op!(int_sub);
    def_op!(int_carry);
    def_op!(int_scarry);
    def_op!(int_sborrow);
    def_op!(int_2comp);
    def_op!(int_negate);
    def_op!(int_xor);
    def_op!(int_and);
    def_op!(int_or);
    def_op!(int_left);
    def_op!(int_right);
    def_op!(int_sright);
    def_op!(int_mult);
    def_op!(int_div);
    def_op!(int_rem);
    def_op!(int_sdiv);
    def_op!(int_srem);
    def_op!(bool_negate);
    def_op!(bool_xor);
    def_op!(bool_and);
    def_op!(bool_or);
    def_op!(float_equal);
    def_op!(float_notequal);
    def_op!(float_less);
    def_op!(float_lessequal);
    def_op!(float_add);
    def_op!(float_sub);
    def_op!(float_mult);
    def_op!(float_div);
    def_op!(float_neg);
    def_op!(float_abs);
    def_op!(float_sqrt);
    def_op!(float_ceil);
    def_op!(float_floor);
    def_op!(float_round);
    def_op!(float_nan);
    def_op!(int2float);
    def_op!(float2float);
    def_op!(trunc);
    def_op!(cpoolref);
    def_op!(new_op);
    // todo: other operations..

    fn translate_pcode(
        &mut self,
        ops: &mut Assembler<Self::Reloc>,
        mem: &mut Self::Mem,
        pcode: &dyn PcodeOp,
    ) -> Result<()> {
        use OpCode::*;

        let inputs = pcode.inputs();
        let output = pcode.output();

        macro_rules! side_effect_free_op {
            ($method:ident) => {{
                self.$method(ops, mem, &inputs, output)?;
            }};
        }

        match pcode.opcode() {
            IntAdd => side_effect_free_op!(int_add),
            Copy => side_effect_free_op!(copy),
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
        let offset: usize = addr.offset().try_into()?;

        let default_size = (offset & (!0xfff)) + 0x2000;

        let region_entry = self.regions.entry(addr.space());
        let region =
            region_entry.or_insert(MmapMut::map_anon(default_size)?.make_exec()?.make_mut()?);

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
