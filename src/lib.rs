#![cfg_attr(not(feature = "std"), no_std)]
#![warn(clippy::pedantic, clippy::nursery)]

mod error;
mod packable;
mod reference;
mod targets;
mod typed_ptr;

pub use error::PackedPtrError;
pub use packable::Packable;
pub use reference::PackedRef;
pub use targets::PackedPtr;
pub use typed_ptr::TypedPackedPtr;
