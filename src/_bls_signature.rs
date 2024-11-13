#![allow(unused_imports)]
#![allow(dead_code)]
use ark_bls12_377::G1Affine;
use ark_poly::domain;
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
use crate::utils::* ;


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

pub fn bls_sign_with_dleq(message: &[u8], secret_key: F, domain: &[u8], params: &UniversalParams<Curve>, public_key: G1)-> (G2,F,F) {
    let hasher = hash_to_point(message,domain) ;
    let signature = hasher.mul(secret_key).into();
    let mut rng = test_rng();
    let r = F::rand(&mut rng);
    let g = params.powers_of_g[0];
   
    let alpha = g.mul(r).into() ;
    let beta = hasher.mul(r).into();
    let c = random_oracle_c(g,hasher,public_key,signature,alpha,beta);
    let s = r + (secret_key * c) ;
    (signature, c, s)
}

pub fn bls_verify_with_dleq(message: &[u8], domain: &[u8], public_key: G1, params: &UniversalParams<Curve>, signature: G2, c:F, s:F) {
    let g = params.powers_of_g[0];
    let h = hash_to_point(message, domain);

     let x_power_c = public_key.mul(-c) ;
    //  assert_eq!(x_power_c, g.mul(sk * (-c)));
    //  assert_eq!(x_power_c+g.mul(s), g.mul(r));
     let y_power_c = signature.mul(-c);
    // assert_eq!(y_power_c, h.mul(sk*(-c)));
    let alpha = (g.mul(s) + x_power_c).into();
    let beta = (h.mul(s) + y_power_c).into();
    let c_1 = random_oracle_c(g, h, public_key, signature, alpha, beta);
    assert_eq!(c,c_1)
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

pub fn aggregate(signatures: Vec<G2>) -> G2 {
   
    // 1 & 2
    let mut aggregate = signatures[0];

    // 3
    for signature in signatures.iter().skip(1) {
        // 6
        aggregate = aggregate.add(signature).into();
    }
    // 7 & 8
    aggregate
}

pub fn aggregate_verify(
    public_keys: Vec<G1>,
    message: &[u8],
    signature: G2,
    domain: &[u8],
    params: &UniversalParams<Curve>
)  {
    let mut apk = public_keys[0] ;
    for pk in public_keys.iter().skip(1) {
        apk = apk.add(pk).into() ;

    }
    bls_verify(message, domain, apk, params, signature);

   
}

fn random_oracle_c(
    g: G1,
    h: G2,
    x: G1,
    y: G2,
    alpha: G1,
    beta: G2,
) -> F {

    let mut serialized_data = Vec::new();
    g.serialize_compressed(&mut serialized_data).unwrap();
    h.serialize_compressed(&mut serialized_data).unwrap();
    x.serialize_compressed(&mut serialized_data).unwrap();
    y.serialize_compressed(&mut serialized_data).unwrap();
    alpha.serialize_compressed(&mut serialized_data).unwrap();
    beta.serialize_compressed(&mut serialized_data).unwrap();
    
    


    let mut hash_result = Sha256::digest(serialized_data.as_slice());
    hash_result[31] = 0u8; //this makes sure we get a number below modulus
    let hash_bytes = hash_result.as_slice();

    let mut hash_values: [u64; 4] = [0; 4];
    hash_values[0] = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
    hash_values[1] = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());
    hash_values[2] = u64::from_le_bytes(hash_bytes[16..24].try_into().unwrap());
    hash_values[3] = u64::from_le_bytes(hash_bytes[24..32].try_into().unwrap());
    //hash_values[3] = u64::from(0u64);

    let bi = BigInteger256::new(hash_values);

    //let input: [u8; 32] = [0u8; 32];
    F::try_from(bi).unwrap()
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
    let (sig, c, s) = bls_sign_with_dleq(message, secret_key, dst, &params, public_key);
    bls_verify_with_dleq(message, dst, public_key, &params, sig, c, s);
    let signature = bls_sign(message, secret_key, dst) ;
    // let (c,s,r) = dleq_prove(secret_key, signature, public_key, &params);
    // dleq_verify(signature, public_key, &params, c, s, secret_key,r,message,dst);
    bls_verify(message, dst, public_key, &params, signature);

}