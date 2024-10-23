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
use ark_bls12_381::{Bls12_381};
use ark_ec::{pairing::Pairing, CurveGroup, hashing::HashToCurve};
use ark_ec::VariableBaseMSM;
use ark_ec::hashing::curve_maps::wb::WBMap;
use ark_ec::hashing::map_to_curve_hasher::MapToCurveBasedHasher;
use ark_bls12_381::g2::Config as G2Config;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, Projective} ;
use ark_ff::PrimeField;
use ark_ff::{field_hashers::DefaultFieldHasher};
use ark_std::Zero;

use sha2::{Digest, Sha256};

use crate::kzg::*;


type Curve = Bls12_381;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_381::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

type G1Projective = Projective<G1> ;
type G2Projective = Projective<G2> ;

fn bls_sign(message: &[u8],secret_key: F, domain: &[u8]) -> G2 {

    let g2_mapper = MapToCurveBasedHasher::<
    G2Projective,
    DefaultFieldHasher<Sha256, 128>,
    WBMap<G2Config>,
>::new(domain)
.unwrap();
let q: G2AffinePoint = g2_mapper.hash(message).unwrap();
q

    
}