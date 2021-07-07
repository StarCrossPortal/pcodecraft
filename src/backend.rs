//! Backend is the actual implementation of the objects within the pcodecraft.
//!
//! Normally, the actual backend would be outside of the pcodecraft crate. But
//! for simple usecase, pcodecraft also provides the simple backends which reads
//! the objects from plain text file in different formats. Please refer to 
//! submodules within backend module for more information.
#[cfg(feature = "plain")]
pub mod plain;