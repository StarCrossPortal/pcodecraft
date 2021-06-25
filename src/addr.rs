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
    Ordering,
    PartialEq,
    Eq,
    PartialOrd
};

#[derive(Debug)]
pub struct Address {
    pub space: String,
    pub offset: u64,
}

impl PartialEq for Address {
    fn eq(&self, other: &Self) -> bool {
        self.space == other.space && self.offset == other.offset
    }
}

impl Eq for Address {}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.space != other.space {
            return None;
        }

        self.offset.partial_cmp(&other.offset)
    }
}