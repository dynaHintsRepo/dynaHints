#![allow(unused_imports)]
use ark_serialize::CanonicalSerialize;
use ark_ff::{Field, biginteger::BigInteger256};
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
use ark_std::rand::Rng;
use ark_std::{UniformRand, test_rng, ops::*};
use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, CurveGroup, hashing::HashToCurve};
use ark_ec::VariableBaseMSM;
use ark_ec::hashing::curve_maps::wb::WBMap;
use ark_ec::hashing::map_to_curve_hasher::MapToCurveBasedHasher;
use ark_bls12_381::g2::Config as G2Config;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, Projective} ;
use ark_ff::PrimeField;
use ark_ff::field_hashers::DefaultFieldHasher;
use ark_std::Zero;
use hmac::Hmac;

use sha2::{Digest, Sha256};

use crate::kzg::*;


type Curve = Bls12_381;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_381::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

pub type G2AffinePoint = Affine<G2Config>;
pub type G2ProjectivePoint = Projective<G2Config>;


pub const DST_ETHEREUM: &str = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

pub fn hash_to_point(msg: &[u8], dst: &[u8]) -> G2AffinePoint {
    let g2_mapper = MapToCurveBasedHasher::<
        G2ProjectivePoint,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<G2Config>,
    >::new(dst)
    .unwrap();
    let q: G2AffinePoint = g2_mapper.hash(msg).unwrap();
    q
}

pub fn sk_to_pk(sk: F, params: &UniversalParams<Curve>) -> G1 {
    // 1
   // let g = G1AffinePoint::generator();
    // XXX: sk.0 does _not_ yield the correct result!
    let p = params.powers_of_g[0].mul(sk) ;
    p.into() 
}

pub fn bls_sign(message: &[u8],secret_key: F, domain: &[u8]) -> G2 {
    let hasher = hash_to_point(message,domain) ;
    hasher.mul(secret_key).into()

     
}

pub fn bls_verify(message: &[u8], domain: &[u8], public_key: G1, params: &UniversalParams<Curve>, signature: G2) {
    let lhs = <Curve as Pairing>::pairing(params.powers_of_g[0],signature) ;
    let q = hash_to_point(message, domain) ;
    let rhs = <Curve as Pairing>::pairing(public_key,q) ;
    assert_eq!(lhs,rhs)
}

#[test]
fn test_sign() {
    let n = 32 ;
    let message = b"abc" ;
    let dst = b"DST_ETHEREUM" ;
    let mut rng = &mut test_rng();
    let params = KZG::setup(n, rng).expect("Setup failed");
    let secret_key = F::rand(&mut rng) ;
    let public_key = sk_to_pk(secret_key, &params) ;
    let signature = bls_sign(message, secret_key, dst) ;
    bls_verify(message, dst, public_key, &params, signature);

}