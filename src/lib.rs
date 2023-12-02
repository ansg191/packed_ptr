#![no_std]
#![warn(clippy::pedantic, clippy::nursery)]
#![allow(clippy::module_name_repetitions)]

pub mod config;
mod error;
mod packable;
mod ptr;
mod reference;
mod typed_ptr;

pub use error::PackedPtrError;
pub use packable::Packable;
pub use ptr::PackedPtr;
pub use reference::PackedRef;
pub use typed_ptr::TypedPackedPtr;
