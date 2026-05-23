//! Covert-channel detector family.
//!
//! Detectors for payloads hidden in invisible Unicode codepoints —
//! tag block (U+E0000..U+E007F), variation selectors
//! (U+FE00..U+FE0F + U+E0100..U+E01EF), zero-width characters,
//! surrogate-reassembly bypasses, and unbalanced bidi format
//! controls.

pub mod bidi_control_balance;
pub mod tag_block_payload;
pub mod variation_selector_payload;
pub mod zero_width_payload;
