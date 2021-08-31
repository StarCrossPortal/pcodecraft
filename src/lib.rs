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


// ghidra decompiler interfaces, export them directly
mod addr;
mod cfg;
mod database;
mod varnode;
mod pcode;
#[cfg(feature = "vars")]
mod variable;
mod block;

pub use addr::*;
pub use cfg::*;
pub use database::*;
pub use varnode::*;
pub use pcode::*;
#[cfg(feature = "vars")]
pub use variable::*;
pub use block::*;

pub mod backend;
#[cfg(feature = "emu")]
pub mod emu;