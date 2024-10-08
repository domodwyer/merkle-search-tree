#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links, rust_2018_idioms)]
#![allow(clippy::default_constructed_unit_structs)]
#![warn(
    clippy::clone_on_ref_ptr,
    clippy::dbg_macro,
    clippy::explicit_iter_loop,
    clippy::future_not_send,
    clippy::todo,
    clippy::use_self,
    missing_copy_implementations,
    missing_debug_implementations,
    unused_crate_dependencies,
    unreachable_pub,
    missing_docs
)]

//   Copyright 2023 Dominic Dwyer (dom@itsallbroken.com)
//
//   Licensed under the Apache License, Version 2.0 (the "License"); you may not
//   use this file except in compliance with the License. You may obtain a copy
//   of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
//   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
//   License for the specific language governing permissions and limitations
//   under the License.

// Silence unused_crate_dependencies false positive.
#[cfg(test)]
use criterion as _;
#[cfg(test)]
use tracing_subscriber as _;

/// Tracing event/log helpers.
#[macro_use]
mod tracing;

#[cfg(test)]
mod test_assert;

pub mod builder;
pub mod diff;
pub mod digest;
mod node;
mod node_iter;
mod page;
mod tree;
pub mod visitor;

#[cfg(test)]
pub(crate) mod test_util;

pub use node::*;
pub use page::*;
pub use tree::*;
