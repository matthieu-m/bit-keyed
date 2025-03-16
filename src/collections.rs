//! Implementations of bit-keyed structures.

//  Design considerations
//
//  #   Why not an alias?
//
//  Type aliases are cool... but they have the unfortunate tendency to _leak_. They leak when the IDE or debugger
//  displays the type, and before you know it the user is submerged with unscruitable types, and despairing.
//
//  #   Why inherent?
//
//  The methods are doubly implement (as inherent methods, and BitSet methods) so they can be called without importing
//  the trait.

pub mod bit_set_core;
pub mod bit_set_inline;

#[cfg(feature = "alloc")]
pub mod bit_set_dynamic;

pub use bit_set_core::BitSetCore;
pub use bit_set_inline::BitSetInline;

#[cfg(feature = "alloc")]
pub use bit_set_dynamic::BitSetDynamic;
