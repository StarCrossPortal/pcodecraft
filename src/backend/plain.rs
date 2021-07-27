use crate::*;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct PlainAddress {
    pub space: String,
    pub offset: u64,
}

impl std::cmp::PartialOrd for PlainAddress {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.space != other.space {
            None
        } else {
            self.offset.partial_cmp(&other.offset)
        }
    }
}

impl Address for PlainAddress {
    fn space(&self) -> String {
        self.space.to_string()
    }

    fn offset(&self) -> u64 {
        self.offset
    }

    fn debug_print(&self) -> String {
        format!("Address {{ space = {}, offset = {}}}", self.space(), self.offset())
    }
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct PlainSeqNum {
    pub uniq: u8,
    pub addr: PlainAddress,
}

impl SeqNum for PlainSeqNum {
    fn uniq(&self) -> u8 {
        self.uniq
    }

    fn addr(&self) -> &dyn Address {
        &self.addr
    }

    fn debug_print(&self) -> String {
        format!("SeqNum {{ uniq = {}, addr = {:?}}}", self.uniq(), self.addr())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainSymbolEntry {
    pub offset: u8
}

impl SymbolEntry for PlainSymbolEntry {
    fn offset(&self) -> u8 {
        self.offset
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainSymbol {
    pub name: String,
    pub map_entry: Vec<PlainSymbolEntry>,
}

impl Symbol for PlainSymbol {
    fn name(&self) -> &str {
        &self.name
    }

    fn map_entry(&self, i: usize) -> &dyn SymbolEntry {
        &self.map_entry[i]
    }

    fn debug_print(&self) -> String {
        format!("Symbol {{name = {}, map_entry = {:?}}}", self.name(), self.map_entry)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainHighVariable {
    pub symbol: Option<PlainSymbol>
}

impl HighVariable for PlainHighVariable {
    fn symbol(&self) -> Option<&dyn Symbol> {
        self.symbol.as_ref().map(|x| x as &dyn Symbol)
    }

    fn debug_print(&self) -> String {
        format!("HighVar {{symbol = {:?}}}", self.symbol())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainVarnode {
    pub addr: PlainAddress,
    pub size: u32,
    pub high_var: Option<PlainHighVariable>
}

impl Varnode for PlainVarnode {
    fn addr(&self) -> &dyn Address {
        &self.addr
    }

    fn size(&self) -> u32 {
        self.size
    }

    fn high_var(&self) -> Option<&dyn HighVariable> {
        self.high_var.as_ref().map(|v| v as &dyn HighVariable)
    }

    fn debug_print(&self) -> String {
        format!("Varnode {{addr = {:?}, size = {}, high_var = {:?}}}", self.addr(), self.size(), self.high_var())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainPcodeOp {
    pub opcode: OpCode,
    pub seq: PlainSeqNum,
    pub inputs: Vec<PlainVarnode>,
    pub output: Option<PlainVarnode>
}

impl PcodeOp for PlainPcodeOp {
    fn opcode(&self) -> OpCode {
        self.opcode
    }

    fn seq(&self) -> &dyn SeqNum {
        &self.seq
    }

    fn inputs(&self) -> Vec<&dyn Varnode> {
        self.inputs.iter().map(|x| x as &dyn Varnode).collect::<Vec<_>>()
    }

    fn output(&self) -> Option<&dyn Varnode> {
        self.output.as_ref().map(|x| x as &dyn Varnode)
    }

    fn debug_print(&self) -> String {
        format!("PcodeOp {{ opcode = {:?}, seq = {:?}, inputs = {:?}, output = {:?}}}", self.opcode(), self.seq(), self.inputs(), self.output())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainBlock {
    pub pcodes: Vec<PlainPcodeOp>
}

impl Block for PlainBlock {
    fn pcodes(&self) -> Vec<&dyn PcodeOp> {
        self.pcodes.iter().map(|x| x as &dyn PcodeOp).collect()
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PlainCfg {
    pub blocks: Vec<PlainBlock>,
    pub outs: Vec<Vec<usize>>,
    pub ins: Vec<Vec<usize>>
}

impl Cfg for PlainCfg {
    fn blocks(&self) -> Vec<&dyn Block> {
        self.blocks.iter().map(|x| x as &dyn Block).collect()
    }

    fn outs(&self, idx: usize) -> Vec<&dyn Block> {
        self.outs[idx].iter().map(|idx| &self.blocks[*idx] as &dyn Block).collect()
    }

    fn ins(&self, idx: usize) -> Vec<&dyn Block> {
        self.ins[idx].iter().map(|idx| &self.blocks[*idx] as &dyn Block).collect()
    }
}

#[macro_export]
macro_rules! plain_pcode {
    ($addr:literal: $uniq:literal| ($out_space:literal, $out_offset:literal, $out_size:literal) = [$opcode:path] $(($in_space:literal, $in_offset:literal, $in_size:literal))+) => {
        PlainPcodeOp {
            opcode: $opcode,
            seq: PlainSeqNum {
                uniq: $uniq,
                addr: PlainAddress {
                    space: "ram".to_string(),
                    offset: $addr
                }
            },
            output: Some(PlainVarnode {
                addr: PlainAddress {
                    space: $out_space.to_string(),
                    offset: $out_offset,
                },
                size: $out_size,
                high_var: None
            }),
            inputs: vec![$(
                PlainVarnode {
                    addr: PlainAddress {
                        space: $in_space.to_string(),
                        offset: $in_offset
                    },
                    size: $in_size,
                    high_var: None
                }
            ),*]
        }
    };
    ($addr:literal: $uniq:literal | [$opcode:path] $($in_space:literal, $in_offset:literal, $in_size:literal)*) => {
        PlainPcodeOp {
            opcode: $opcode,
            seq: PlainSeqNum {
                uniq: $uniq,
                addr: PlainAddress {
                    space: "ram".to_string(),
                    offset: $addr
                }
            },
            output: None,
            inputs: vec![$(
                PlainVarnode {
                    addr: PlainAddress {
                        space: $in_space.to_string(),
                        offset: $in_offset
                    },
                    size: $in_size,
                    high_var: None
                }
            )*]
        }
    }
}