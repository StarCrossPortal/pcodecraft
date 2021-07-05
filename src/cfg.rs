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

use crate::PcodeOp;

/// A basic block
pub trait Block {
    fn pcodes(&self) -> &[&dyn PcodeOp];
}

/// The control flow graph
pub trait Cfg {
    /// all basic blocks
    fn blocks(&self) -> &[&dyn Block];
    /// output blocks
    fn outs(&self) -> &[&dyn Block];
    /// input blocks
    fn ins(&self) -> &[&dyn Block];
}