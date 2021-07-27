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

pub trait Symbol {
    fn name(&self) -> &str;
    fn map_entry(&self, i: usize) -> &dyn SymbolEntry;
    fn num_entries(&self) -> usize;
    fn debug_print(&self) -> String {
        let mut map_entry = String::new();
        let num = self.num_entries();
        for i in 0..num {
            map_entry.push_str(&format!("{:?}", self.map_entry(i)));
            if i != num - 1 {
                map_entry.push_str(&format!(","));
            }
        }
        format!("Symbol {{name = {}, map_entry = [{:?}]}}", self.name(), map_entry)
    }
}

impl<'a> std::fmt::Debug for &'a dyn Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_print())
    }
}

pub trait SymbolEntry {
    fn offset(&self) -> u8;

    fn debug_print(&self) -> String {
        format!("SymbolEntry {{ offset = {}}}", self.offset())
    }
}

impl<'a> std::fmt::Debug for &'a dyn SymbolEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_print())
    }
}