//! Strict Unicode-as-attack-surface conformance for Rust.
//!
//! The crate's public surface is a family of strict text codecs
//! (UTF-8, UTF-16 BE/LE, UTF-32 BE/LE, BOM detection,
//! noncharacter predicate, ASCII identifier predicate) and three
//! refinement types (`Utf8Blob`, `IdentifierUtf8`,
//! `ValidatedUtf8`) that carry their validity claim at the
//! module-boundary level.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod bom;
pub mod identifier;
pub mod noncharacters;
pub mod opaque_blob;
pub mod security;
pub mod strict;
pub mod utf16;
pub mod utf32;
pub mod utf8;
pub mod validated_utf8;

pub use crate::bom::BomKind;
pub use crate::identifier::{
    first_invalid_identifier_continue_from,
    is_identifier_continue_byte,
    is_identifier_start_byte,
    is_valid_identifier_bytes,
    IdentifierUtf8,
};
pub use crate::noncharacters::{all_noncharacters, is_noncharacter};
pub use crate::opaque_blob::{is_utf8_blob, Utf8Blob};
pub use crate::strict::Utf8RejectKind;
pub use crate::utf8::{
    decode_to_codepoints,
    encode_codepoint,
    encode_codepoints,
    first_invalid_utf8_offset,
    is_valid_utf8,
    utf8_decode_step,
    Utf8State,
    Utf8StepResult,
};
pub use crate::validated_utf8::ValidatedUtf8;
