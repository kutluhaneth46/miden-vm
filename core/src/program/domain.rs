//! Registered domain selectors for protocol-visible hash commitments.
//!
//! This module follows the Miden domain-separation RFC
//! (<https://github.com/0xMiden/crypto/pull/1026>): consensus-critical domains use **registered
//! numeric identifiers** rather than hashed strings, packed as
//!
//! ```text
//! selector = (domain_id << 8) | version
//! ```
//!
//! with `domain_id` a registered 24-bit integer (`>= 1`) and `version` an 8-bit per-domain
//! version (`>= 1`). Eidos incorporates the selector and exact input length into its initial
//! Eidos chaining value through `hash_elements_in_domain`.
//!
//! # Provisional registry entries
//!
//! The RFC's draft registry allocates `0x010000..0x01ffff` to miden-vm, with concrete entries
//! delegated to this repository. This module assigns the following entries within that range:
//!
//! | domain_id  | version | domain |
//! |------------|---------|-------------------------------------------|
//! | `0x010000` | 1       | kernel commitment ([`KERNEL_DOMAIN_TAG`](super::KERNEL_DOMAIN_TAG)) |
//! | `0x010001` | 1       | execution claim ([`CLAIM_DOMAIN_TAG`](super::CLAIM_DOMAIN_TAG)) |
//! | `0x010002` | 1       | proof request key ([`PROOF_REQUEST_DOMAIN_TAG`](super::PROOF_REQUEST_DOMAIN_TAG)) |
//! | `0x010003` | 1       | deferred AND/root fold |
//! | `0x010004` | 1       | deferred framework CHUNKS node |
//! | `0x010005` | 1       | tagged deferred precompile node |
//!
//! Selectors share one Eidos domain namespace with the `merge_in_domain` values used for MAST
//! control-block hashing. Those are opcode-sized (`< 256`) while every registered selector is
//! `>= 257` (`domain_id >= 1`), so those two ranges cannot collide. Distinctness among registered
//! selectors is the registry's responsibility: each `domain_id` is allocated once within its
//! maintainer's range, and the six defined here are pinned distinct by
//! `registry_entries_are_valid_and_distinct_selectors`.

use crate::Felt;

/// Registered domain id for the kernel commitment.
pub const KERNEL_COMMITMENT_DOMAIN_ID: u32 = 0x010000;

/// Registered domain id for the execution-claim commitment.
pub const EXECUTION_CLAIM_DOMAIN_ID: u32 = 0x010001;

/// Registered domain id for the proof-request key.
pub const PROOF_REQUEST_DOMAIN_ID: u32 = 0x010002;

/// Registered domain id for deferred AND nodes and rolling-root folds.
pub const DEFERRED_AND_DOMAIN_ID: u32 = 0x010003;

/// Registered domain id for framework-owned deferred CHUNKS nodes.
pub const DEFERRED_CHUNKS_DOMAIN_ID: u32 = 0x010004;

/// Registered domain id for tagged, precompile-owned deferred nodes.
pub const DEFERRED_NODE_DOMAIN_ID: u32 = 0x010005;

/// Packs a registered domain id and per-domain version into a domain selector.
///
/// The result is a 31-bit integer (`domain_id << 8 | version`), used as the domain element of
/// `hash_elements_in_domain`.
pub const fn domain_selector(domain_id: u32, version: u8) -> Felt {
    assert!(
        domain_id >= 1 && domain_id < (1 << 23),
        "domain_id must be a registered 23-bit id"
    );
    assert!(version >= 1, "per-domain versions start at 1");
    Felt::new_unchecked(((domain_id as u64) << 8) | version as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_entries_are_valid_and_distinct_selectors() {
        use crate::{
            deferred::{DEFERRED_AND_DOMAIN, DEFERRED_CHUNKS_DOMAIN, DEFERRED_NODE_DOMAIN},
            program::{CLAIM_DOMAIN_TAG, KERNEL_DOMAIN_TAG, PROOF_REQUEST_DOMAIN_TAG},
        };

        let entries = [
            (KERNEL_COMMITMENT_DOMAIN_ID, KERNEL_DOMAIN_TAG),
            (EXECUTION_CLAIM_DOMAIN_ID, CLAIM_DOMAIN_TAG),
            (PROOF_REQUEST_DOMAIN_ID, PROOF_REQUEST_DOMAIN_TAG),
            (DEFERRED_AND_DOMAIN_ID, DEFERRED_AND_DOMAIN),
            (DEFERRED_CHUNKS_DOMAIN_ID, DEFERRED_CHUNKS_DOMAIN),
            (DEFERRED_NODE_DOMAIN_ID, DEFERRED_NODE_DOMAIN),
        ];
        for (i, (id, tag)) in entries.iter().enumerate() {
            assert!(*id >= 1 && *id < (1 << 23), "domain id out of the registered range");
            assert_eq!(
                tag.as_canonical_u64(),
                (u64::from(*id) << 8) | 1,
                "tag is not the packed selector"
            );
            for (other_id, other_tag) in entries.iter().skip(i + 1) {
                assert_ne!(id, other_id, "registered domain ids must be unique");
                assert_ne!(tag, other_tag, "registered tags must be unique");
            }
        }
    }

    #[test]
    #[should_panic(expected = "domain_id must be a registered 23-bit id")]
    fn domain_selector_rejects_values_outside_eidos_domain_range() {
        let _ = domain_selector(1 << 23, 1);
    }
}
