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
use crate::{Address, Varnode};
use std::cmp::{
    Ordering,
    PartialEq,
    Eq,
    PartialOrd
};

#[derive(Debug)]
pub struct SeqNum {
    pub uniq: u8,
    pub addr: Address,
}

impl PartialEq for SeqNum {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr && self.uniq == other.uniq
    }
}

impl Eq for SeqNum {}

impl PartialOrd for SeqNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.addr != other.addr {
            None
        } else {
            self.uniq.partial_cmp(&other.uniq)
        }
    }
}

#[derive(Debug)]
#[repr(u8)]
pub enum OpCode {
    Copy = 1,  // Copy one operand to another
    Load = 2,  // Load from a pointer into a specified address space
    Store = 3, // Store at a pointer into a specified address space

    Branch = 4,    // Always branch
    Cbranch = 5,   // Conditional branch
    BranchInd = 6, // Indirect branch (jumptable)

    Call = 7,      // Call to an absolute address
    CallInd = 8,   // Call through an indirect address
    CallOther = 9, // User-defined operation
    Return = 10,   // Return from subroutine

    // Integer/bit operations
    IntEqual = 11,      // Integer comparison, equality (==)
    IntNotEqual = 12,   // Integer comparison, in-equality (!=)
    IntSless = 13,      // Integer comparison, signed less-than (<)
    IntSlessEqual = 14, // Integer comparison, signed less-than-or-equal (<=)
    IntLess = 15,       // Integer comparison, unsigned less-than (<)
    // This also indicates a borrow on unsigned substraction
    IntLessEqual = 16, // Integer comparison, unsigned less-than-or-equal (<=)
    IntZext = 17,      // Zero extension
    IntSext = 18,      // Sign extension
    IntAdd = 19,       // Addition, signed or unsigned (+)
    IntSub = 20,       // Subtraction, signed or unsigned (-)
    IntCarry = 21,     // Test for unsigned carry
    IntSCarry = 22,    // Test for signed carry
    IntSBorrow = 23,   // Test for signed borrow
    Int2Comp = 24,     // Twos complement
    IntNegate = 25,    // Logical/bitwise negation (~)
    IntXor = 26,       // Logical/bitwise exclusive-or (^)
    IntAnd = 27,       // Logical/bitwise and (&)
    IntOr = 28,        // Logical/bitwise or (|)
    IntLeft = 29,      // Left shift (<<)
    IntRight = 30,     // Right shift, logical (>>)
    IntSRight = 31,    // Right shift, arithmetic (>>)
    IntMult = 32,      // Integer multiplication, signed and unsigned (*)
    IntDiv = 33,       // Integer division, unsigned (/)
    IntSDiv = 34,      // Integer division, signed (/)
    IntRem = 35,       // Remainder/modulo, unsigned (%)
    IntSRem = 36,      // Remainder/modulo, signed (%)

    BoolNegate = 37, // Boolean negate (!)
    BoolXor = 38,    // Boolean exclusive-or (^^)
    BoolAnd = 39,    // Boolean and (&&)
    BoolOr = 40,     // Boolean or (||)

    // Floating point operations
    FloatEqual = 41,     // Floating-point comparison, equality (==)
    FloatNotEqual = 42,  // Floating-point comparison, in-equality (!=)
    FloatLess = 43,      // Floating-point comparison, less-than (<)
    FloatLessEqual = 44, // Floating-point comparison, less-than-or-equal (<=)
    // Slot 45 is currently unused
    FloatNan = 46, // Not-a-number test (NaN)

    FloatAdd = 47,  // Floating-point addition (+)
    FloatDiv = 48,  // Floating-point division (/)
    FloatMult = 49, // Floating-point multiplication (*)
    FloatSub = 50,  // Floating-point subtraction (-)
    FloatNeg = 51,  // Floating-point negation (-)
    FloatAbs = 52,  // Floating-point absolute value (abs)
    FloatSqrt = 53, // Floating-point square root (sqrt)

    FloatInt2Float = 54,   // Convert an integer to a floating-point
    FloatFloat2Float = 55, // Convert between different floating-point sizes
    FloatTrunc = 56,       // Round towards zero
    FloatCeil = 57,        // Round towards +infinity
    FloatFloor = 58,       // Round towards -infinity
    FloatRound = 59,       // Round towards nearest

    // Internal opcodes for simplification. Not
    // typically generated in a direct translation.

    // Data-flow operations
    MultiEqual = 60, // Phi-node operator
    Indirect = 61,   // Copy with an indirect effect
    Piece = 62,      // Concatenate
    SubPiece = 63,   // Truncate

    Cast = 64,      // Cast from one data-type to another
    PtrAdd = 65,    // Index into an array ([])
    PtrSub = 66,    // Drill down to a sub-field  (->)
    SegmentOp = 67, // Look-up a \e segmented address
    CPoolRef = 68,  // Recover a value from the \e constant \e pool
    New = 69,       // Allocate a new object (new)
    Insert = 70,    // Insert a bit-range
    Extract = 71,   // Extract a bit-range
    PopCount = 72,  // Count the 1-bits

    Max = 73, // Value indicating the end of the op-code values
}


#[derive(Debug)]
pub struct PcodeOp {
    pub opcode: OpCode,
    pub seq: SeqNum,
    pub inputs: Vec<Varnode>,
    pub output: Option<Varnode>
}