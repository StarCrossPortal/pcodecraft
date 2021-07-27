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
use std::cmp::{
    PartialEq,
    Eq,
    PartialOrd,
    Ordering
};

pub trait Address {
    fn space(&self) -> String;
    fn offset(&self) -> u64;

    fn equals(&self, other: &dyn Address) -> bool {
        self.space() == other.space() && self.offset() == other.offset()
    }
    fn partial_compare(&self, other: &dyn Address) -> Option<Ordering> {
        if self.space() != other.space() {
            None
        } else {
            self.offset().partial_cmp(&other.offset())
        }
    }
    fn debug_print(&self) -> String {
        format!("Address {{ space = {}, offset = {}}}", self.space(), self.offset())
    }
}

impl<'a> PartialEq for &'a dyn Address {
    fn eq(&self, other: &&dyn Address) -> bool {
        self.equals(*other)
    }
}

impl<'a> Eq for &'a dyn Address {}

impl<'a> PartialOrd for &'a dyn Address {
    fn partial_cmp(&self, other: &&dyn Address) -> Option<Ordering> {
        self.partial_compare(*other)
    }
}

impl<'a> std::fmt::Debug for &'a dyn Address {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_print())
    }
}