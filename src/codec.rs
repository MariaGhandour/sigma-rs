//! Encoding and decoding utilities for Fiat-Shamir and group operations.

pub use crate::duplex_sponge::keccak::KeccakDuplexSponge;
use crate::duplex_sponge::{shake::ShakeDuplexSponge, DuplexSpongeInterface};
use bls12_381::G1Projective;
use ff::PrimeField;
use group::{Group, GroupEncoding};
use num_bigint::BigUint;
use num_traits::identities::One;

/// A trait defining the behavior of a domain-separated codec hashing, which is typically used for [`crate::traits::SigmaProtocol`]s.
///
/// A domain-separated hashing codec is a codec, identified by a domain, which is incremented with successive messages ("absorb"). The codec can then output a bit stream of any length, which is typically used to generate a challenge unique to the given codec ("squeeze"). (See Sponge Construction).
///
/// The output is deterministic for a given set of input. Thus, both Prover and Verifier can generate the codec on their sides and ensure the same inputs have been used in both side of the protocol.
///
/// ## Minimal Implementation
/// Types implementing [`Codec`] must define:
/// - `new`
/// - `prover_message`
/// - `verifier_challenge`
pub trait Codec {
    type Challenge;

    /// Generates an empty codec that can be identified by a domain separator.
    fn new(domain_sep: &[u8]) -> Self;

    /// Allows for precomputed initialization of the codec with a specific IV.
    fn from_iv(iv: [u8; 32]) -> Self;

    /// Absorbs data into the codec.
    fn prover_message(&mut self, data: &[u8]);

    /// Produces a scalar that can be used as a challenge from the codec.
    fn verifier_challenge(&mut self) -> Self::Challenge;
}

fn cardinal<F: PrimeField>() -> BigUint {
    let bytes = (F::ZERO - F::ONE).to_repr();
    BigUint::from_bytes_le(bytes.as_ref()) + BigUint::one()
}

/// A byte-level Schnorr codec that works with any duplex sponge.
///
/// This codec is generic over both the group `G` and the hash function `H`.
/// It can be used with different duplex sponge implementations.
#[derive(Clone)]
pub struct ByteSchnorrCodec<G, H>
where
    G: Group + GroupEncoding,
    H: DuplexSpongeInterface,
{
    hasher: H,
    _marker: core::marker::PhantomData<G>,
}

impl<G, H> Codec for ByteSchnorrCodec<G, H>
where
    G: Group + GroupEncoding,
    H: DuplexSpongeInterface,
{
    type Challenge = <G as Group>::Scalar;

    fn new(domain_sep: &[u8]) -> Self {
        let iv = {
            let mut tmp = H::new([0u8; 32]);
            tmp.absorb(domain_sep);
            tmp.squeeze(32).try_into().unwrap()
        };

        Self::from_iv(iv)
    }

    fn from_iv(iv: [u8; 32]) -> Self {
        Self {
            hasher: H::new(iv),
            _marker: core::marker::PhantomData,
        }
    }

    fn prover_message(&mut self, data: &[u8]) {
        self.hasher.absorb(data);
    }

    fn verifier_challenge(&mut self) -> G::Scalar {
        #[allow(clippy::manual_div_ceil)]
        let scalar_byte_length = (G::Scalar::NUM_BITS as usize + 7) / 8;

        let uniform_bytes = self.hasher.squeeze(scalar_byte_length + 16);
        let scalar = BigUint::from_bytes_be(&uniform_bytes);
        let reduced = scalar % cardinal::<G::Scalar>();

        let mut bytes = vec![0u8; scalar_byte_length];
        let reduced_bytes = reduced.to_bytes_be();
        let start = bytes.len() - reduced_bytes.len();
        bytes[start..].copy_from_slice(&reduced_bytes);
        bytes.reverse();

        let mut repr = <<G as Group>::Scalar as PrimeField>::Repr::default();
        repr.as_mut().copy_from_slice(&bytes);

        <<G as Group>::Scalar as PrimeField>::from_repr(repr).expect("Error")
    }
}

/// Type alias for a Keccak-based ByteSchnorrCodec.
/// This is the codec used for matching test vectors from Sage.
pub type KeccakByteSchnorrCodec<G> = ByteSchnorrCodec<G, KeccakDuplexSponge>;

/// Type alias for a SHAKE-based ByteSchnorrCodec.
pub type ShakeCodec<G> = ByteSchnorrCodec<G, ShakeDuplexSponge>;

#[cfg(test)]
mod codec_tests {
    use super::*;
    use bls12_381::G1Projective;

     #[test]
    fn test_squeeze_zero_behavior_in_sigma_rs() {
    let domain_sep = b"01234567890123456789012345678901";
    let mut codec1 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain_sep);

    codec1.prover_message(b"message test");

    let mut codec2 = codec1.clone();

    let squeezed_zero = codec1.hasher.squeeze(0);
    assert!(squeezed_zero.is_empty(), "squeeze(0) should return an empty vector");

    let output1 = codec1.hasher.squeeze(10);
    let output2 = codec2.hasher.squeeze(10);

    assert_eq!(
        output1, output2,
        "squeeze(0) should not change the state, so outputs must be identical"
    );
} 

    #[test]
    fn test_absorb_squeeze_absorb_consistency() {
        let domain_sep = b"edge-case-test-domain-absorb0000";
        let mut codec1 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain_sep);

        codec1.prover_message(b"first");
        let out1 = codec1.hasher.squeeze(16);
        codec1.prover_message(b"second");
        let out2 = codec1.hasher.squeeze(16);

        // Create a new codec that absorbs "firstsecond" as one block
        let mut codec2 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain_sep);
        codec2.prover_message(b"firstsecond");
        let out_combined = codec2.hasher.squeeze(32);

        assert_eq!(&out1[..], &out_combined[..16], "First squeeze should match");
        assert_eq!(&out2[..], &out_combined[16..], "Second squeeze should match");
    }

    #[test]
    fn test_associativity_of_absorb() {
        let domain_sep = b"absorb-associativity-domain-----";
        let mut codec1 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain_sep);
        codec1.prover_message(&[1, 2, 3, 4]);
        let out1 = codec1.hasher.squeeze(16);

        let mut codec2 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain_sep);
        codec2.prover_message(&[1, 2]);
        codec2.prover_message(&[3, 4]);
        let out2 = codec2.hasher.squeeze(16);

        assert_eq!(out1, out2, "Absorbing in two steps should match combined absorb");
    }

    #[test]
    fn test_tag_affects_output() {
        let domain1 = b"domain-one-differs-here-00000000";
        let domain2 = b"domain-two-differs-here-11111111";

        let mut codec1 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain1);
        let mut codec2 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain2);

        codec1.prover_message(b"input");
        codec2.prover_message(b"input");

        let out1 = codec1.hasher.squeeze(16);
        let out2 = codec2.hasher.squeeze(16);

        assert_ne!(out1, out2, "Different domain separators must yield different outputs");
    }

    #[test]
    fn test_clone_preserves_state() {
        let domain = b"domain-for-clone-test-0000000000";
        let mut codec1 = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain);
        codec1.prover_message(b"hello");

        let mut codec2 = codec1.clone();

        let out1 = codec1.hasher.squeeze(16);
        let out2 = codec2.hasher.squeeze(16);

        assert_eq!(out1, out2, "Cloned codec should produce the same output");
    }

    #[test]
    fn test_absorb_empty_does_not_break() {
        let domain = b"empty-input-absorb-0000000000000";
        let mut codec = ByteSchnorrCodec::<G1Projective, KeccakDuplexSponge>::new(domain);

        codec.prover_message(b""); // no-op

        let out = codec.hasher.squeeze(8);
        assert_eq!(out.len(), 8);
    }
}
