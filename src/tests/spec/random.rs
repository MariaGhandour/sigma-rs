use group::{Group, GroupEncoding};
use num_bigint::BigUint;
use rand::{CryptoRng, Rng};

pub trait SInput: Group + GroupEncoding {
    fn scalar_from_hex_be(hex_str: &str) -> Option<Self::Scalar>;
}

pub trait SRandom: Group {
    fn randint_big(l: &BigUint, h: &BigUint, rng: &mut (impl Rng + CryptoRng)) -> BigUint;

    fn srandom(rng: &mut (impl Rng + CryptoRng)) -> Self::Scalar;

    fn prandom(rng: &mut (impl Rng + CryptoRng)) -> Self;
}
