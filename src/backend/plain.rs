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
use crate::*;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
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
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
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

    fn num_entries(&self) -> usize {
        self.map_entry.len()
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
    ($addr:literal: $uniq:literal | [$opcode:path] $(($in_space:literal, $in_offset:literal, $in_size:literal))*) => {
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