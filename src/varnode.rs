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

use crate::{Address};
#[cfg(feature = "vars")]
use crate::HighVariable;

pub trait Varnode {
    fn addr(&self) -> &dyn Address;
    fn size(&self) -> u32;
    /// Varnode::getHigh()
    #[cfg(feature = "vars")]
    fn high_var(&self) -> Option<&dyn HighVariable>;

    fn debug_print(&self) -> String {
        #[cfg(feature = "vars")]
        {
            format!("Varnode {{addr = {:?}, size = {}, high_var = {:?}}}", self.addr(), self.size(), self.high_var())
        }

        #[cfg(not(feature = "vars"))]
        {
            format!("Varnode {{addr = {:?}, size = {}}}", self.addr(), self.size())
        }
    }
}

impl<'a> std::fmt::Debug for &'a dyn Varnode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_print())
    }
}