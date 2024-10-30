//use std::ptr::metadata;
#![allow(unused_imports)]
use std::time::Instant;
use std::sync::Arc;
use serde::{Serialize, Deserialize,};
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Write, Seek, SeekFrom, Read};

//use pprof::ProfilerGuard;

//use rand::SeedableRng;
use sha2::{Digest, Sha256};
use hex ;
use std::collections::HashSet;

use vrf::openssl::{CipherSuite, ECVRF};
use vrf::VRF;

//use rand_chacha ;

use aes::Aes128;
use aes::cipher::{BlockEncrypt, KeyInit,
    generic_array::GenericArray,
};

use ark_serialize::{CanonicalSerialize, SerializationError, CanonicalDeserialize, Compress, Valid, Validate};
use ark_ff::{Field, biginteger::BigInteger256};
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
//use ark_std::rand::Rng;
use ark_std::{UniformRand, test_rng, ops::*};
use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ec::VariableBaseMSM;

use _bls_signature as bls;
//use pippengerTesting::* ;

//use w3f_bls::{Keypair,ZBLS,Message,Signed};

use kzg::*;

mod utils;
mod kzg;
mod hintgen;
mod _bls_signature;
//mod pippengerTesting;

type Curve = Bls12_381;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_381::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

///partial bls signature structure 
struct PartialSig {
    sigma: G2,
    i: usize,
}

/// hinTS proof structure
struct Proof {
    /// aggregate public key (aPK_signer in the paper)
    agg_pk: G1,
    ///aggregated signature
    agg_sigma: G2,
    ///aggregate public key of the committee (aPK_com in the paper)
   // agg_pk_committee: G1,
    /// aggregate weight (w in the paper)
    agg_weight: F,
    ///..................//
    /// commitments regarding committee
    ///commitment to the committee bit vector 
    b_committee_of_tau: G1,
    ///commitment to the Q_x_com 
    //qx_of_tau_committee: G1,
    ///committee to the Q_x_com.x 
   // qx_of_tau_mul_tau_committee: G1,
    /// commitment to the Q_Z_com
    //qz_of_tau_committee: G1,
    ///.....................///
    /// commitments regarding signers 
    /// commitment to the bitmap polynomial ([B(τ)]_1 in the paper)
    b_signer_of_tau: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ)]_1 in the paper)
    qx_of_tau_signer: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ) . τ ]_1 in the paper)
    qx_of_tau_mul_tau_signer: G1,
    /// commitment to the Q_z polynomial ([Q_z(τ)]_1 in the paper)
    qz_of_tau_signer: G1,
    ///.....................///
    b_sub_of_tau: G1,
    /// commitment to the ParSum_sub
    parsum_sub_of_tau_com: G1,
    ///commitment to the ParSum_sub well-formedness quotient polynomials 
    // q1_sub_of_tau_com: G1,
    //  /// commitment to the ParSum _sub check at omega^{n-1} quotient polynomial
    //  q3_sub_of_tau_com: G1,
    //  /// commitment to the bitmap well-formedness quotient polynomial
    //  q2_sub_of_tau_com: G1,
    //  /// commitment to the bitmap check at omega^{n-1} quotient polynomial
    //  q4_sub_of_tau_com: G1,
     //batching 
     q_sub_of_tau_com: G1,
    /// commitment to the ParSum_signer polynomial ([ParSum(τ)]_1 in the paper)
    parsum_signer_of_tau_com: G1,

    /// commitment to the parsum_signer well-formedness quotient polynomial
    //q1_of_tau_com: G1,
    /// commitment to the ParSum check at omega^{n-1} quotient polynomial
    //q3_of_tau_com: G1,
    /// commitment to the bitmap well-formedness quotient polynomial
    //q2_of_tau_com: G1,
    /// commitment to the bitmap check at omega^{n-1} quotient polynomial
   // q4_of_tau_com: G1,
    ///batching 
    q_of_tau_com: G1,

    /// merged opening proof for all openings at x = r
    opening_proof_r: G1,
    /// proof for the ParSum opening at x = r / ω
    opening_proof_r_div_ω: G1,

    /// polynomial evaluation of ParSum(x) at x = r
    parsum_signer_of_r: F,
    /// polynomial evaluation of ParSum(x) at x = r / ω
    parsum_signer_of_r_div_ω: F,
    /// polynomial evaluation of W(x) at x = r
    w_of_r: F,
    /// polynomial evaluation of bitmap B(x) at x = r
    b_signer_of_r: F,
    /// polynomial evaluation of quotient Q1(x) at x = r
    //q1_of_r: F,
    /// polynomial evaluation of quotient Q3(x) at x = r
    //q3_of_r: F,
    /// polynomial evaluation of quotient Q2(x) at x = r
    //q2_of_r: F,
    /// polynomial evaluation of quotient Q4(x) at x = r
    //q4_of_r: F,
    ///batching 
    q_of_r: F,

    /// polynomial evaluation of ParSum_sub(x) at x = r
    parsum_sub_of_r: F,
    /// polynomial evaluation of ParSum_sub(x) at x = r / ω
    parsum_sub_of_r_div_ω: F,
    /// polynomial evaluation of W_sub(x) at x = r
    w_sub_of_r: F,
    /// polynomial evaluation of bitmap B_sub(x) at x = r
    b_sub_of_r: F,
    /// polynomial evaluation of quotient Q1(x) at x = r
    // q1_sub_of_r: F,
    // /// polynomial evaluation of quotient Q3(x) at x = r
    // q3_sub_of_r: F,
    // /// polynomial evaluation of quotient Q2(x) at x = r
    // q2_sub_of_r: F,
    // /// polynomial evaluation of quotient Q4(x) at x = r
    // q4_sub_of_r: F,
    q_sub_of_r: F,
}

/// Hint contains all material output by a party during the setup phase
#[allow(dead_code)]

#[derive(CanonicalSerialize, CanonicalDeserialize,Clone,Debug, PartialEq, Eq)]
//#[derive(Serialize, Deserialize, Debug)]
struct Hint {
    /// index in the address book
    i: usize,
    /// public key pk = [sk]_1
    pk_i: G1,
    /// [ sk_i L_i(τ) ]_1
    sk_i_l_i_of_tau_com_1: G1,
    /// [ sk_i L_i(τ) ]_2
    sk_i_l_i_of_tau_com_2: G2,
    /// qz_i_terms[i] = [ sk_i * ((L_i^2(τ) - L_i(τ)) / Z(τ)) ]_1
    /// \forall j != i, qz_i_terms[j] = [ sk_i * (L_i(τ) * L_j(τ) / Z(τ)) ]_1
    qz_i_terms: Vec<G1>,
    /// [ sk_i ((L_i(τ) - L_i(0)) / τ ]_1
    qx_i_term: G1,
    /// [ sk_i ((L_i(τ) - L_i(0))]_1
    qx_i_term_mul_tau: G1,
}

//hint independent one time setup computations
#[derive(CanonicalSerialize, CanonicalDeserialize,Clone,Debug, PartialEq, Eq)]
struct HintIndependentSetupElements {
    i: usize,
    /// public key pk = [sk]_1
   // pk_i: G1,
    /// [ sk_i L_i(τ) ]_1
    //sk_i_l_i_of_tau_com_1: G1,
    /// [ sk_i L_i(τ) ]_2
    l_i_of_tau_com_2: G2,
    /// qz_i_terms[i] = [ sk_i * ((L_i^2(τ) - L_i(τ)) / Z(τ)) ]_1
    /// \forall j != i, qz_i_terms[j] = [ sk_i * (L_i(τ) * L_j(τ) / Z(τ)) ]_1
    qz_i_terms: Vec<G2>,
    /// [ sk_i ((L_i(τ) - L_i(0)) / τ ]_1
    qx_i_term: G2,
    /// [ sk_i ((L_i(τ) - L_i(0))]_1
    qx_i_term_mul_tau: G2,

}

/// AggregationKey contains all material needed by Prover to produce a hinTS proof
struct AggregationKey {
    /// number of parties plus one (must be a power of 2)
    n: usize,
    c: usize,
    /// weights has all parties' weights, where weights[i] is party i's weight
    weights: Vec<F>,
    /// pks contains all parties' public keys, where pks[i] is g^sk_i
    pks: Vec<G1>,
    /// qz_terms contains pre-processed hints for the Q_z polynomial.
    /// qz_terms[i] has the following form:
    /// [sk_i * (L_i(\tau)^2 - L_i(\tau)) / Z(\tau) + 
    /// \Sigma_{j} sk_j * (L_i(\tau) L_j(\tau)) / Z(\tau)]_1
    qz_terms : Vec<G1>,
    /// qx_terms contains pre-processed hints for the Q_x polynomial.
    /// qx_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) / x ]_1
    qx_terms : Vec<G1>,
    /// qx_mul_tau_terms contains pre-processed hints for the Q_x * x polynomial.
    /// qx_mul_tau_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) ]_1
    qx_mul_tau_terms : Vec<G1>,
}

struct VerificationKey {
    /// the universe has n - 1 parties (where n is a power of 2)
    n: usize,
    //the committee has c-1 parties 
    c : usize,
    /// first G1 element from the KZG CRS (for zeroth power of tau)
    g_0: G1,
    /// first G2 element from the KZG CRS (for zeroth power of tau)
    h_0: G2,
    /// second G1 element from the KZG CRS (for first power of tau)
    h_1: G2,
    /// commitment to the L_{n-1} polynomial
    l_n_minus_1_of_tau_com: G1,
    /// commitment to the W polynomial
    w_of_tau_com: G1,
    /// commitment to the SK polynomial
    sk_of_tau_com: G2,
    /// commitment to the vanishing polynomial Z(x) = x^n - 1
    z_of_tau_com: G2,
    /// commitment to the f(x) = x, which equals [\tau]_2
    tau_com: G2
}
//u64::rand(&mut rng)

fn sample_weights(n: usize) -> Vec<F> {
    //let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(1)).collect()
}

/// n is the size of the bitmap, and probability is for true or 1.
// fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
//     let rng = &mut test_rng();
//     let mut bitmap = vec![];
//     for _i in 0..n {
//         //let r = u64::rand(&mut rng);
//         let bit = rng.gen_bool(probability);
//         bitmap.push(F::from(bit));
//     }
//     bitmap
// }

fn create_committee(com_size: usize, universe_size: usize, vrf_output: &Vec<u8>) -> Vec<F> {
    
 
     //putting the vrf output as key into aes
     let mut result = HashSet::new();
     let beta1 = &vrf_output.clone() ;
     let key:[u8;16] = [beta1[0],beta1[1],beta1[2],beta1[3],beta1[4],
                       beta1[5],beta1[6],beta1[7],beta1[8],beta1[9],
                       beta1[10],beta1[11],beta1[12],beta1[13],beta1[14],
                       beta1[15]] ;
 
                       
     let cipher = Aes128::new(&GenericArray::from_slice(&key));
     
 
     let mut counter: u128 = 0; // 128-bit counter
 
     while result.len() < com_size {
        //println!("result length {}",result.len()) ;
         let mut block = GenericArray::clone_from_slice(&counter.to_be_bytes());
         //println!("create committee block is {:?}",block) ;
         cipher.encrypt_block(&mut block);

         //convert the block in to 128 bit 
         let encrypted_value = u128::from_be_bytes(block.as_slice().try_into().expect("Incorrect length"));
         //println!("create committee encrypted_value is {:?}",encrypted_value) ;
         //map the encrypted value in the range of the universe size
         let random_number = (encrypted_value % (universe_size as u128)) as u128 ;
         result.insert(random_number as u32);
         //println!("After insert result length {}",result.len()) ;
         counter += 1;
     }
     let comm: Vec<u32> = result.into_iter().collect() ;
     //println!("The positions are {:?}",comm) ;
 
     let mut bitmap_com = Vec::with_capacity(universe_size) ;
     for _i in 0..universe_size {
         bitmap_com.push(F::from(0)) ;
     }
     for &value in &comm {
         let temp = value as usize ;
         if temp < universe_size {
             bitmap_com[temp] = F::from(1) ;
         }    
     }
     bitmap_com
     
     
}

fn create_subset_bitmap(n: usize, bmap: &Vec<F>, thresh: usize)-> Vec<F> {
    let mut sub_map = Vec::with_capacity(n);
    let mut t = thresh.clone() ;
    //let rng = &mut test_rng() ;
    for i in 0..n {
        if bmap[i] == F::from(0) {
            sub_map.push(F::from(0)) ;

        }
        else {
            if t > 0 {
                sub_map.push(F::from(1));
                t = t-1 ;
            }
            else {
                sub_map.push(F::from(0)) ;
            }
           
        }

    }

    sub_map

}

fn verify_committee(com_size: usize, universe_size: usize, b_com_of_tau: G1,vrf_instan: &mut ECVRF,vrf_message: &[u8], vrf_proof: &Vec<u8>, vrf_pk: &Vec<u8>,params: &UniversalParams<Curve>) {
    //let mut vrf = ECVRF::from_suite(CipherSuite::SECP256K1_SHA256_TAI).unwrap() ;
    //let message = vrf_message.clone() ;
    //let bitmap_committee = b_com.clone() ;
    let pi = vrf_proof.clone() ;
    let pk = vrf_pk.clone() ;
    let hash = vrf_instan.proof_to_hash(&pi).unwrap();
    //println!("verify committee hash is {:?}",hash) ;
    let beta = vrf_instan.verify(&pk, &pi, &vrf_message);
    match beta.as_ref() {
        Ok(beta) => {
            println!("VRF proof is valid!");
            assert_eq!(&hash, beta);
        }
        Err(e) => {
            println!("VRF proof is not valid: {}", e);
        }
    }
    let mut result = HashSet::new();
   
     let beta1 = &beta.unwrap().clone() ;
     let key:[u8;16] = [beta1[0],beta1[1],beta1[2],beta1[3],beta1[4],
                       beta1[5],beta1[6],beta1[7],beta1[8],beta1[9],
                       beta1[10],beta1[11],beta1[12],beta1[13],beta1[14],
                       beta1[15]] ;
 
                       
     let cipher = Aes128::new(&GenericArray::from_slice(&key));
 
     let mut counter: u128 = 0; // 128-bit counter
 
     while result.len() < com_size {
         let mut block = GenericArray::clone_from_slice(&counter.to_be_bytes());
         //println!("verify committee block is {:?}",block) ;
         cipher.encrypt_block(&mut block);
         //convert the block in to 128 bit 
         let encrypted_value = u128::from_be_bytes(block.as_slice().try_into().expect("Incorrect length"));
         //println!("verify committee encrypted_value is {:?}",encrypted_value) ;
         //map the encrypted value in the range of the universe size
         let random_number = (encrypted_value % (universe_size as u128)) as u128 ;
         result.insert(random_number as u32);
         counter += 1;
     }
     let comm: Vec<u32> = result.into_iter().collect() ;
     //println!("The positions are {:?}",comm) ;
 
     let mut bitmap_com = Vec::with_capacity(universe_size) ;
     for _i in 0..universe_size {
         bitmap_com.push(F::from(0)) ;
     }
     for &value in &comm {
         let temp = value as usize ;
         if temp < universe_size {
             bitmap_com[temp] = F::from(1) ;
         }    
     }
     bitmap_com.push(F::from(1));
     let bitmap_com_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_com);
     let bitmap_com_of_tau = KZG::commit_g1(&params, &bitmap_com_of_x).unwrap() ;
     assert_eq!(bitmap_com_of_tau , b_com_of_tau) ;
     //assert_eq!(bitmap_com, bitmap_committee) ;
    //  if bitmap_com == bitmap_committee {
    //     true
    //  }
    //  else {
    //     false    
    //  }
    
}

fn partial_signatures_gen(universe_size: usize,sk: &Vec<F>,bitmap_signer: &Vec<F>,message: &Vec<u8>,dst: &Vec<u8>)-> Vec<PartialSig> {
    let mut partial_sig_vec = vec![] ;
    for i in 0..universe_size {
        if bitmap_signer[i] == F::from(1) {
            let p_sig = PartialSig {
                sigma: bls::bls_sign( message,sk[i], dst),
                i: i,
            } ;
            partial_sig_vec.push(p_sig) ;

        }

    }
    partial_sig_vec
}

fn partial_signatures_verification(partial_sig_vec: &Vec<PartialSig>,message: &Vec<u8>,dst: &Vec<u8>,pks: &Vec<G1>,params: &UniversalParams<Curve>) {
    for j in 0..partial_sig_vec.len() {
        let p_sig = &partial_sig_vec[j] ; 
        bls::bls_verify(&message, dst, pks[p_sig.i], params, p_sig.sigma) ;
    }

}

// fn write_structs_to_file(file_path: &str, structs: &[Hint]) -> io::Result<()> {
//     let file = File::create(file_path)?;
//     let writer = BufWriter::new(file);
//     serde_json::to_writer(writer, &structs)?;
//     Ok(())
// }
#[allow(dead_code)]
fn write_hints_to_file(hints: &Vec<Hint>, path: &str, _n:usize) -> Result<(), SerializationError> {
    //let mut file = File::create(path).map_err(|_| SerializationError::IoError) ;
   //let mut file = BufReader::new(File::open(path).map_err(SerializationError::IoError)?);
    let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;


    // let mut file = File::options()
    //         .write(true)
    //         .create(true)
    //         .open(path)
    //         .map_err(SerializationError::IoError)?;
    // let mut buffer = [0; 1];
    // let is_empty = match file.read(&mut buffer) {
    //         Ok(0) => true,   // If no bytes were read, the file is empty
    //         Ok(_) => false,  // If any bytes were read, the file has content
    //         Err(e) => return Err(SerializationError::IoError(e)),
    // };

    //     // If the file is not empty, check the hint count stored at the start of the file
    // if !is_empty {
    //         // Seek to the start of the file to read the stored hint count
    //         file.seek(SeekFrom::Start(0)).map_err(SerializationError::IoError)?;
    //         let stored_hint_count = u64::deserialize_uncompressed(&mut file)? as usize;

    //         // If the hint count matches `n`, skip writing to the file
    //         if stored_hint_count == n {
    //             println!("The file already contains the required number of hints. Skipping write.");
    //             return Ok(());
    //         }
    // }
       println!("Writing hints") ;
        // Clear the file before writing new data if necessary
        // file.set_len(0).map_err(SerializationError::IoError)?;

        // // Seek back to the start of the file for writing
        // file.seek(SeekFrom::Start(0)).map_err(SerializationError::IoError)?;

        // Write the number of `Hint` structs at the beginning of the file
        (hints.len() as u64).serialize_uncompressed(&mut file)?;

        // Serialize each `Hint` in the vector
        for hint in hints {
            hint.i.serialize_uncompressed(&mut file)?;
            hint.pk_i.serialize_uncompressed(&mut file)?;
            hint.sk_i_l_i_of_tau_com_1.serialize_uncompressed(&mut file)?;
            hint.sk_i_l_i_of_tau_com_2.serialize_uncompressed(&mut file)?;

            // Serialize `qz_i_terms` vector length and elements
            (hint.qz_i_terms.len() as u64).serialize_uncompressed(&mut file)?;
            for term in &hint.qz_i_terms {
                term.serialize_uncompressed(&mut file)?;
            }

            hint.qx_i_term.serialize_uncompressed(&mut file)?;
            hint.qx_i_term_mul_tau.serialize_uncompressed(&mut file)?;
        }

        Ok(())
    }



fn read_hints_from_file(path: &str) -> Result<Vec<Hint>, SerializationError> {
    let mut file = File::open(path).map_err(SerializationError::IoError)?;
    

    let hint_count = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut hints = Vec::with_capacity(hint_count);

    // Deserialize each field from the file
    for _ in 0..hint_count {
        let i = usize::deserialize_uncompressed(&mut file)?;
    let pk_i = G1::deserialize_uncompressed(&mut file)?;
    let sk_i_l_i_of_tau_com_1 = G1::deserialize_uncompressed(&mut file)?;
    let sk_i_l_i_of_tau_com_2 = G2::deserialize_uncompressed(&mut file)?;

    // Deserialize the length of `qz_i_terms` and then each element
    let qz_i_terms_len = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut qz_i_terms = Vec::with_capacity(qz_i_terms_len);
    for _ in 0..qz_i_terms_len {
        qz_i_terms.push(G1::deserialize_uncompressed(&mut file)?);
    }

    let qx_i_term = G1::deserialize_uncompressed(&mut file)?;
    let qx_i_term_mul_tau = G1::deserialize_uncompressed(&mut file)?;

    hints.push(Hint{
        i,
        pk_i,
        sk_i_l_i_of_tau_com_1,
        sk_i_l_i_of_tau_com_2,
        qz_i_terms,
        qx_i_term,
        qx_i_term_mul_tau,
    })


    }

   
    
    Ok(hints)
}

fn main() {
    //universe size is n 
    let n = 128;
    println!("n = {}", n);

    //committee size is c
    let c = 16;
    println!("c={}",c) ;

    //threshold is t
    let t: usize = 5;
    println!("T={}",t) ;

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let start = Instant::now();
    let params: UniversalParams<ark_ec::bls12::Bls12<ark_bls12_381::Config>> = KZG::setup(n, rng).expect("Setup failed");
    let params = Arc::new(params) ;
    let duration = start.elapsed();
    println!("Time elapsed in KZG setup is: {:?}", duration);

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk = hintgen::read_secret_keys("secret_keys.bin").unwrap() ;
   
    let start = Instant::now();
    let all_parties_setup = read_hints_from_file("hints_test_data.bin").unwrap() ;
    let duration = start.elapsed();
    println!("Time elapsed in hint generation is: {:?}", duration);
    //sample random weights for each party
    //let weights = sample_weights(n - 1);

    let start = Instant::now();
    let all_parties_independent_setup = read_hints_independent_compu_from_file("setup_requirements.bin").unwrap() ;
    let duration = start.elapsed();
    println!("Time elapsed in hint independent computation is: {:?}", duration);
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    let start = Instant::now();
    let (vk, ak) = setup(n, c,&params, &weights,  &all_parties_setup, &all_parties_independent_setup);
    let duration = start.elapsed();
    println!("Time elapsed in setup is: {:?}", duration);

    //generate hints for all the parties
    //let hint_i: Vec<Hint> = Vec::new() ;
    // let start = Instant::now();
    // let hint_i = setup(n, &params, &sk) ;
    // let duration = start.elapsed();
    // println!("Time elapsed in setup is: {:?}", duration);

    // -------------- perform universe preprocess ---------------
    //run universe preprocess
    // let start = Instant::now();
    // let (vk, ak) = preprocess(n,c, &params, &weights, &hint_i);
    // let duration = start.elapsed();
    // println!("Time elapsed in preprocess is: {:?}", duration);

    // -------------- sample proof specific values ---------------
    //have to use PRF to get c no of positions and also look for repititions
    let mut vrf = ECVRF::from_suite(CipherSuite::SECP256K1_SHA256_TAI).unwrap() ;
    let secret_key =
        hex::decode("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721").unwrap();
    let public_key = vrf.derive_public_key(&secret_key).unwrap();
    let vrf_message: &[u8] = b"samplec" ;
    let pi = vrf.prove(&secret_key, &vrf_message).unwrap();

    let beta = vrf.verify(&public_key, &pi, &vrf_message);

   
    let bitmap_com = create_committee(c, n-1, &beta.unwrap()) ;
    // let mut bitmap_signer = Vec::with_capacity(n);
    // for i in 0..n-1 {
    //     if i < t {
    //         bitmap_signer.push(F::from(1)) ;
    //     }
    //     else {
    //         bitmap_signer.push(F::from(0)) ;
    //     }
       

    // }
    let bitmap_signer = create_subset_bitmap(n - 1, &bitmap_com,t) ;
    // println!("bitmap_com is {:?}",bitmap_com) ;
    // println!("bitmap_signer is {:?}",bitmap_signer) ;


    let mut no_of_signers: usize = 0;

    for i in 0..bitmap_signer.len() {
        if bitmap_signer[i] == F::from(1) {
            no_of_signers = no_of_signers+1 ;
        }
    }

    println!("No. of signers is {}",no_of_signers) ;

    let message = "message to sign".as_bytes().to_vec();
    let dst = bls::DST_ETHEREUM.as_bytes().to_vec();

    let sig_vec = partial_signatures_gen(n-1, &sk, &bitmap_signer, &message, &dst) ;

   //assert_eq!( bls::point_to_pubkey(ak.pks[1]), bls::sk_to_pk(sk[1]));



    let start = Instant::now();
    let π = prove(&params, t,&ak, &vk, &bitmap_com, &bitmap_signer,&sig_vec, &message, &dst);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);
    

    let start = Instant::now();
    verify(&vk, &π,t, &message, &dst,&mut vrf,&vrf_message, &pi, &public_key,&params);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
}

fn setup(
    n: usize,
    c: usize,
    params: &UniversalParams<Curve>,
    w: &Vec<F>,
    //sk: &Vec<F>,
    all_parties_setup: &Vec<Hint>,
    all_parties_independent_setup: &Vec<HintIndependentSetupElements>,
) -> (VerificationKey, AggregationKey)
{
    let mut weights = w.clone();
   // let  sk = sk.clone();

    //last element must be 0
   // sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut qz_contributions : Vec<Vec<G1>> = vec![Default::default(); n];
    let mut qx_contributions : Vec<G1> = vec![Default::default(); n];
    let mut qx_mul_tau_contributions : Vec<G1> = vec![Default::default(); n];
    let mut pks : Vec<G1> = vec![Default::default(); n];
    let mut sk_l_of_tau_coms: Vec<G2> = vec![Default::default(); n];
    
    //collect the setup phase material from all parties
    // let all_parties_setup = crossbeam::scope(|s| {
    //     let mut threads = Vec::new();
    //     for i in 0..n {
    //         //let idx = i.clone();
    //         //let n = n.clone();
    //         let sk = sk[i];
    //        // println!("Spawning thread for index: {}", i) ;
    //         let thread_i = s.spawn(move |_| hint_gen(&params, n, i, &sk));
    //         threads.push(thread_i);
    //     }

    //     threads.into_iter().map(|t| t.join().unwrap()).collect::<Vec<_>>()
    // }).unwrap();

    for i in 0..n {
        verify_hint(params, &all_parties_setup[i], &all_parties_independent_setup[i]);
    }

    for hint in all_parties_setup {
        //verify hint
        //verify_hint(params, &hint);
        //extract necessary items for pre-processing
        qz_contributions[hint.i] = hint.qz_i_terms.clone();
        qx_contributions[hint.i] = hint.qx_i_term.clone();
        qx_mul_tau_contributions[hint.i] = hint.qx_i_term_mul_tau.clone();
        pks[hint.i] = hint.pk_i.clone();
        sk_l_of_tau_coms[hint.i] = hint.sk_i_l_i_of_tau_com_2.clone();
    }


    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);

    let vp = VerificationKey {
        n: n,
        c: c,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_tau_com: KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap(),
        w_of_tau_com: w_of_x_com,
        // combine all sk_i l_i_of_x commitments to get commitment to sk(x)
        sk_of_tau_com: add_all_g2(&params, &sk_l_of_tau_coms),
        z_of_tau_com: KZG::commit_g2(&params, &z_of_x).unwrap(),
        tau_com: KZG::commit_g2(&params, &x_monomial).unwrap(),
    };

    let pp = AggregationKey {
        n: n,
        c: c,
        weights: w.clone(),
        pks: pks,
        qz_terms: preprocess_qz_contributions(&qz_contributions),
        qx_terms: qx_contributions,
        qx_mul_tau_terms: qx_mul_tau_contributions,
    };

    (vp, pp)

}

//RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q)
fn random_oracle_r(
    sk_com: G2,
    w_com: G1,
    b_com: G1,
    parsum_com: G1,
    qx_com_signer: G1,
    qz_com_signer: G1,
    qx_mul_x_com_signer: G1,
    //qx_com_commitee: G1,
   // qz_com_committee: G1,
    //qx_mul_x_com_committee: G1,
    q_com: G1,
    q_sub_com: G1,
) -> F {

    let mut serialized_data = Vec::new();
    sk_com.serialize_compressed(&mut serialized_data).unwrap();
    w_com.serialize_compressed(&mut serialized_data).unwrap();
    b_com.serialize_compressed(&mut serialized_data).unwrap();
    parsum_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qz_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qx_mul_x_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    // qx_com_commitee.serialize_compressed(&mut serialized_data).unwrap();
    // qz_com_committee.serialize_compressed(&mut serialized_data).unwrap();
    // qx_mul_x_com_committee.serialize_compressed(&mut serialized_data).unwrap();
    // q1_com.serialize_compressed(&mut serialized_data).unwrap();
    // q2_com.serialize_compressed(&mut serialized_data).unwrap();
    // q3_com.serialize_compressed(&mut serialized_data).unwrap();
    // q4_com.serialize_compressed(&mut serialized_data).unwrap();
    q_com.serialize_compressed(&mut serialized_data).unwrap();
    q_sub_com.serialize_compressed(&mut serialized_data).unwrap();
    
    


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

fn random_oracle_v(
    sk_com: G2,
    w_com: G1,
    b_com: G1,
    parsum_com: G1,
    qx_com_signer: G1,
    qz_com_signer: G1,
    qx_mul_x_com_signer: G1,
) -> F {

    let mut serialized_data = Vec::new();
    sk_com.serialize_compressed(&mut serialized_data).unwrap();
    w_com.serialize_compressed(&mut serialized_data).unwrap();
    b_com.serialize_compressed(&mut serialized_data).unwrap();
    parsum_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qz_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qx_mul_x_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    // qx_com_commitee.serialize_compressed(&mut serialized_data).unwrap();
    // qz_com_committee.serialize_compressed(&mut serialized_data).unwrap();
    // qx_mul_x_com_committee.serialize_compressed(&mut serialized_data).unwrap();
    // q1_com.serialize_compressed(&mut serialized_data).unwrap();
    // q2_com.serialize_compressed(&mut serialized_data).unwrap();
    // q3_com.serialize_compressed(&mut serialized_data).unwrap();
    // q4_com.serialize_compressed(&mut serialized_data).unwrap();

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

fn prove(
    params: &UniversalParams<Curve>,
    t: usize,
    ak: &AggregationKey,
    vk: &VerificationKey,
    bitmap_com: &Vec<F>,
    bitmap_signer: &Vec<F>,
    signature_vector: &Vec<PartialSig>,
    message: &Vec<u8>,
    dst: &Vec<u8>) -> Proof {
    // compute the nth root of unity
    let n = ak.n;

    //adjust the weights and bitmap polynomials
    let mut weights = ak.weights.clone();
    //compute sum of weights of active signers
    let total_active_weight = bitmap_signer
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    //println!("total active weight is {:?}",total_active_weight) ;
    //weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap_signer = bitmap_signer.clone();
    let mut bitmap_com = bitmap_com.clone() ;
   
   
    //compute B_com(x)-B_signer(x) to prove that B_signer is a subset of B_com
    let mut bitmap_sub = Vec::with_capacity(n) ;

    for (b1 ,b2) in bitmap_com.iter().zip(bitmap_signer.iter()) {
        if b1 != b2 {
            bitmap_sub.push(b1+b2) ;
        }
        else {
            bitmap_sub.push(F::from(0)) ;
        }
       
    }

    // let weight_of_b_sub = bitmap_sub
    // .iter()
    // .zip(weights.iter())
    // .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
   // println!("weight of b_sub is {:?}",weight_of_b_sub) ;
    //weight vector for bitmap_sub 
    let mut sub_weights = ak.weights.clone() ;
    //sub_weight's last element must the additive inverse of weight_of_b_sub
    sub_weights.push(F::from(0) - F::from((ak.c-t ) as i128));

    //bitmap's last element must be 1
    bitmap_signer.push(F::from(1));
    bitmap_com.push(F::from(1));
    bitmap_sub.push(F::from(1)) ;

    //verify the partial signatures
    partial_signatures_verification(signature_vector, message, dst, &ak.pks, params) ;
    let agg_sigma = compute_agg_sig(signature_vector, n) ;

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover
    let z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_signer);
    let b_committee_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_com) ;
    let b_sub_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_sub) ;
    let psw_of_x = compute_psw_poly(&weights, &bitmap_signer);
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);


    //more polynomials to prove B_signer is a subset of B_com 
    let w_sub_of_x = utils::interpolate_poly_over_mult_subgroup(&sub_weights) ;
    let psw_sub_of_x = compute_psw_poly(&sub_weights, &bitmap_sub) ;
    let psw_sub_of_x_div_ω = utils::poly_domain_mult_ω(&psw_sub_of_x, &ω_inv) ;
    //ParSumSubW_sub(x)=ParSumSubW_sub(X/ω) + W_sub(X).b_sub(X) + Z(X).Q1_sub(X)
    let t_of_x = psw_sub_of_x.sub(&psw_sub_of_x_div_ω).sub(&w_sub_of_x.mul(&b_sub_of_x));
    let psw_sub_wff_q_of_x = t_of_x.div(&z_of_x);
    //L_{n−1}(X) · ParSumSubW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_sub_of_x);
    let psw_sub_check_q_of_x = t_of_x.div(&z_of_x);
    //b_sub(X) · b_sub(X) − b_sub(X) = Z(X) · Q3(X)
    let t_of_x = b_sub_of_x.mul(&b_sub_of_x).sub(&b_sub_of_x);
    let b_sub_wff_q_of_x = t_of_x.div(&z_of_x);
    //L_{n−1}(X) · (b_sub(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_sub_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_sub_check_q_of_x = t_of_x.div(&z_of_x);



    //ParSumSignerW(X) = ParSumSignerW(X/ω) + W(X) · b_signer(X) + Z(X) · Q1(X)
    let t_of_x = psw_of_x.sub(&psw_of_x_div_ω).sub(&w_of_x.mul(&b_signer_of_x));
    let psw_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_of_x);
    let psw_check_q_of_x = t_of_x.div(&z_of_x);

    //b_signer(X) · b_signer(X) − b_signer(X) = Z(X) · Q3(X)
    let t_of_x = b_signer_of_x.mul(&b_signer_of_x).sub(&b_signer_of_x);
    let b_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · (b_signer(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_signer_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_check_q_of_x = t_of_x.div(&z_of_x);

    let parsum_signer_of_tau_com = KZG::commit_g1(&params, &psw_of_x).unwrap();
    let b_signer_of_tau = KZG::commit_g1(&params, &b_signer_of_x).unwrap();
    let b_committee_of_tau = KZG::commit_g1(&params, &b_committee_of_x).unwrap() ;
    let qz_com_signer = filter_and_add(&params, &ak.qz_terms, &bitmap_signer);
    let qx_com_signer = filter_and_add(&params, &ak.qx_terms, &bitmap_signer);
    let qx_mul_tau_com_signer = filter_and_add(&params, &ak.qx_mul_tau_terms, &bitmap_signer);

    let b_sub_of_tau = KZG::commit_g1(&params, &b_sub_of_x).unwrap() ;
    let parsum_sub_of_tau_com = KZG::commit_g1(&params, &psw_sub_of_x).unwrap();

//have to implemet taking v as random and computing q(x) = q1(x) + v q2(x) + v^2 q3(x) + v^3 q4(x)
let v1 = random_oracle_v(
    vk.sk_of_tau_com, 
    vk.w_of_tau_com,
    b_signer_of_tau,
    parsum_signer_of_tau_com,
    qx_com_signer,
    qz_com_signer,
    qx_mul_tau_com_signer,
    // qx_com_committee,
    // qz_com_committee,
    // qx_mul_tau_com_committee,
    // q1_of_tau_com,
    // q2_of_tau_com,
    // q3_of_tau_com,
    // q4_of_tau_com
);

let v2 = random_oracle_v(
    vk.sk_of_tau_com, 
    vk.w_of_tau_com,
    b_sub_of_tau,
    parsum_sub_of_tau_com,
    qx_com_signer,
    qz_com_signer,
    qx_mul_tau_com_signer,
    // qx_com_committee,
    // qz_com_committee,
    // qx_mul_tau_com_committee,
    // q1_of_tau_com,
    // q2_of_tau_com,
    // q3_of_tau_com,
    // q4_of_tau_com
);
   
   //let v = F::from(2) ;
   let mut q_of_x = psw_wff_q_of_x.clone()  ;
   for i in 0..(q_of_x.degree()+1) {
    q_of_x.coeffs[i] = q_of_x.coeffs[i] + v1 * b_wff_q_of_x.coeffs[i] + v1*v1 * psw_check_q_of_x.coeffs[i]
                      + v1 *v1*v1 * b_check_q_of_x.coeffs[i]

   } ;
   let q_of_tau_com = KZG::commit_g1(&params, &q_of_x).unwrap() ;

   let mut q_sub_of_x = psw_sub_wff_q_of_x.clone()  ;
   for i in 0..(q_sub_of_x.degree()+1) {
    q_sub_of_x.coeffs[i] = q_sub_of_x.coeffs[i] + v2 * b_sub_wff_q_of_x.coeffs[i] + v2*v2* psw_sub_check_q_of_x.coeffs[i]
                      + v2 *v2*v2 * b_sub_check_q_of_x.coeffs[i]

   } ;
   let q_sub_of_tau_com = KZG::commit_g1(&params, &q_sub_of_x).unwrap() ;



    //let qz = filter_and_add(&params, &ak.qz_terms, &bitmap) ;
    //computing the quotient polynomial for the signer sumcheck 
    
    let agg_pk = compute_apk(&ak, &bitmap_signer);

    //computing the quotient polynomial for the committee sumcheck
    // let qz_com_committee = filter_and_add(&params, &ak.qz_terms, &bitmap_com);
    // let qx_com_committee = filter_and_add(&params, &ak.qx_terms, &bitmap_com);
    // let qx_mul_tau_com_committee = filter_and_add(&params, &ak.qx_mul_tau_terms, &bitmap_com);
    // let agg_pk_committee = compute_apk(&ak, &bitmap_com);
     

    //required polynomials for the sub vector 
   
   // let b_signer_of_tau = KZG::commit_g1(&params, &b_signer_of_x).unwrap();
    // let q1_sub_of_tau_com = KZG::commit_g1(&params, &psw_sub_wff_q_of_x).unwrap();
    // let q2_sub_of_tau_com = KZG::commit_g1(&params, &b_sub_wff_q_of_x).unwrap();
    // let q3_sub_of_tau_com = KZG::commit_g1(&params, &psw_sub_check_q_of_x).unwrap();
    // let q4_sub_of_tau_com = KZG::commit_g1(&params, &b_sub_check_q_of_x).unwrap();


   
    // let q1_of_tau_com = KZG::commit_g1(&params, &psw_wff_q_of_x).unwrap();
    // let q2_of_tau_com = KZG::commit_g1(&params, &b_wff_q_of_x).unwrap();
    // let q3_of_tau_com = KZG::commit_g1(&params, &psw_check_q_of_x).unwrap();
    // let q4_of_tau_com = KZG::commit_g1(&params, &b_check_q_of_x).unwrap();

    // RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
    let r = random_oracle_r(
        vk.sk_of_tau_com, 
        vk.w_of_tau_com,
        b_signer_of_tau,
        parsum_signer_of_tau_com,
        qx_com_signer,
        qz_com_signer,
        qx_mul_tau_com_signer,
        // qx_com_committee,
        // qz_com_committee,
        // qx_mul_tau_com_committee,
        // q1_of_tau_com,
        // q2_of_tau_com,
        // q3_of_tau_com,
        // q4_of_tau_com
        q_of_tau_com,
        q_sub_of_tau_com
    );
    let r_div_ω: F = r / ω;

    

    let psw_of_r_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r).unwrap();
    let w_of_r_proof = KZG::compute_opening_proof(&params, &w_of_x, &r).unwrap();
    let b_signer_of_r_proof = KZG::compute_opening_proof(&params, &b_signer_of_x, &r).unwrap();
    // let psw_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_wff_q_of_x, &r).unwrap();
    // let psw_check_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_check_q_of_x, &r).unwrap();
    // let b_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &b_wff_q_of_x, &r).unwrap();
    // let b_check_q_of_r_proof = KZG::compute_opening_proof(&params, &b_check_q_of_x, &r).unwrap();
    let q_of_r_proof = KZG::compute_opening_proof(&params, &q_of_x, &r).unwrap();
    let q_sub_of_r_proof = KZG::compute_opening_proof(&params, &q_sub_of_x, &r).unwrap();


    //for sub vector 
    let psw_sub_of_r_proof = KZG::compute_opening_proof(&params, &psw_sub_of_x, &r).unwrap();
    let w_sub_of_r_proof = KZG::compute_opening_proof(&params, &w_sub_of_x, &r).unwrap();
    let b_sub_of_r_proof = KZG::compute_opening_proof(&params, &b_sub_of_x, &r).unwrap();

    //for r_div_ω
    let psw_sub_of_r_div_ω_proof = KZG::compute_opening_proof(&params, &psw_sub_of_x, &r_div_ω).unwrap();
    let psw_of_r_div_ω_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r_div_ω).unwrap() ;

    let merged_proof: G1 = (psw_of_r_proof
        + w_of_r_proof.mul(r.pow([1]))
        + b_signer_of_r_proof.mul(r.pow([2]))
        + q_of_r_proof.mul(r.pow([3]))
        +psw_sub_of_r_proof.mul(r.pow([4]))
        + w_sub_of_r_proof.mul(r.pow([5]))
        + b_sub_of_r_proof.mul(r.pow([6]))
        + q_sub_of_r_proof.mul(r.pow([7]))).into();
    
    let merged_proof_at_r_div_ω : G1= (psw_sub_of_r_div_ω_proof
        + psw_of_r_div_ω_proof.mul(r_div_ω.pow([1]))).into() ;


    Proof {
        agg_pk: agg_pk.clone(),
        agg_sigma: agg_sigma.clone(),
        //agg_pk_committee: agg_pk_committee.clone(),
        agg_weight: total_active_weight,
        
        parsum_signer_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        parsum_sub_of_r_div_ω: psw_sub_of_x.evaluate(&r_div_ω),
        opening_proof_r_div_ω: merged_proof_at_r_div_ω,

        parsum_signer_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_signer_of_r: b_signer_of_x.evaluate(&r),
        q_of_r: q_of_x.evaluate(&r),

        parsum_sub_of_r: psw_sub_of_x.evaluate(&r),
        w_sub_of_r: w_sub_of_x.evaluate(&r),
        q_sub_of_r: q_sub_of_x.evaluate(&r),
        b_sub_of_r: b_sub_of_x.evaluate(&r),

        
        opening_proof_r: merged_proof.into(),

        parsum_signer_of_tau_com: parsum_signer_of_tau_com,
        b_signer_of_tau: b_signer_of_tau,
        q_of_tau_com: q_of_tau_com,

        parsum_sub_of_tau_com: parsum_sub_of_tau_com,
        b_sub_of_tau: b_sub_of_tau,
        q_sub_of_tau_com: q_sub_of_tau_com,
        qz_of_tau_signer: qz_com_signer,
        qx_of_tau_signer: qx_com_signer,
        qx_of_tau_mul_tau_signer: qx_mul_tau_com_signer,

        b_committee_of_tau: b_committee_of_tau,
        // qz_of_tau_committee: qz_com_committee,
        // qx_of_tau_committee: qx_com_committee,
        // qx_of_tau_mul_tau_committee: qx_mul_tau_com_committee,
    }
}

// fn verify_opening(
//     vp: &VerificationKey, 
//     commitment: &G1,
//     point: &F, 
//     evaluation: &F,
//     opening_proof: &G1) {
//     let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
//     let point_com: G2 = vp.h_0.clone().mul(point).into();

//     let lhs = <Curve as Pairing>::pairing(commitment.clone() - eval_com, vp.h_0);
//     let rhs = <Curve as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
//     assert_eq!(lhs, rhs);
// }

fn verify_openings_in_proof(vp: &VerificationKey, π: &Proof, r: F, t: usize) {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_tau_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_tau_com + adjustment_com).into();

    let adjustment_sub = F::from(0) - F::from((vp.c-t) as u64);
    let adjustment_sub_com = vp.l_n_minus_1_of_tau_com.mul(adjustment_sub);
    let w_sub_of_x_com: G1 = (vp.w_of_tau_com + adjustment_sub_com).into();

    let psw_sub_of_r_argument = π.parsum_sub_of_tau_com - vp.g_0.clone().mul(π.parsum_sub_of_r).into_affine();
    let w_sub_of_r_argument = w_sub_of_x_com - vp.g_0.clone().mul(π.w_sub_of_r).into_affine();
    let b_sub_of_r_argument = π.b_sub_of_tau - vp.g_0.clone().mul(π.b_sub_of_r).into_affine();
    // let psw_sub_wff_q_of_r_argument = π.q1_sub_of_tau_com - vp.g_0.clone().mul(π.q1_sub_of_r).into_affine();
    // let psw_sub_check_q_of_r_argument = π.q3_sub_of_tau_com - vp.g_0.clone().mul(π.q3_sub_of_r).into_affine();
    // let b_sub_wff_q_of_r_argument = π.q2_sub_of_tau_com - vp.g_0.clone().mul(π.q2_sub_of_r).into_affine();
    // let b_sub_check_q_of_r_argument = π.q4_sub_of_tau_com - vp.g_0.clone().mul(π.q4_sub_of_r).into_affine();
    let q_sub_of_r_argument =  π.q_sub_of_tau_com - vp.g_0.clone().mul(π.q_sub_of_r).into_affine();

    let psw_of_r_argument = π.parsum_signer_of_tau_com - vp.g_0.clone().mul(π.parsum_signer_of_r).into_affine();
    let w_of_r_argument = w_of_x_com - vp.g_0.clone().mul(π.w_of_r).into_affine();
    let b_signer_of_r_argument = π.b_signer_of_tau - vp.g_0.clone().mul(π.b_signer_of_r).into_affine();
    // let psw_wff_q_of_r_argument = π.q1_of_tau_com - vp.g_0.clone().mul(π.q1_of_r).into_affine();
    // let psw_check_q_of_r_argument = π.q3_of_tau_com - vp.g_0.clone().mul(π.q3_of_r).into_affine();
    // let b_wff_q_of_r_argument = π.q2_of_tau_com - vp.g_0.clone().mul(π.q2_of_r).into_affine();
    // let b_check_q_of_r_argument = π.q4_of_tau_com - vp.g_0.clone().mul(π.q4_of_r).into_affine();
    let q_of_r_argument =  π.q_of_tau_com - vp.g_0.clone().mul(π.q_of_r).into_affine();

    let merged_argument: G1 = (psw_of_r_argument
        + w_of_r_argument.mul(r.pow([1]))
        + b_signer_of_r_argument.mul(r.pow([2]))
        + q_of_r_argument.mul(r.pow([3]))
        +psw_sub_of_r_argument.mul(r.pow([4]))
        + w_sub_of_r_argument.mul(r.pow([5]))
        + b_sub_of_r_argument.mul(r.pow([6]))
        + q_sub_of_r_argument.mul(r.pow([7]))).into_affine();

    let lhs = <Curve as Pairing>::pairing(
        merged_argument, 
        vp.h_0);
    let rhs = <Curve as Pairing>::pairing(
        π.opening_proof_r, 
        vp.h_1 - vp.h_0.clone().mul(r).into_affine());
    assert_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;

    let psw_sub_of_r_div_ω_argument = π.parsum_sub_of_tau_com - vp.g_0.clone().mul(π.parsum_sub_of_r_div_ω).into_affine();
    let psw_of_r_div_ω_argument = π.parsum_signer_of_tau_com - vp.g_0.clone().mul(π.parsum_signer_of_r_div_ω).into_affine();

    let merged_argument_at_r_div_ω : G1= (psw_sub_of_r_div_ω_argument
        + psw_of_r_div_ω_argument.mul(r_div_ω.pow([1]))).into() ;

        let lhs = <Curve as Pairing>::pairing(
            merged_argument_at_r_div_ω, 
            vp.h_0);
        let rhs = <Curve as Pairing>::pairing(
            π.opening_proof_r_div_ω, 
            vp.h_1 - vp.h_0.clone().mul(r_div_ω).into_affine());
        assert_eq!(lhs, rhs);

    // verify_opening(vp, 
    //     &π.parsum_signer_of_tau_com, 
    //     &r_div_ω, 
    //     &π.parsum_signer_of_r_div_ω, 
    //     &π.opening_proof_r_div_ω);
}

fn verify(vp: &VerificationKey, π: &Proof, t: usize, message: &Vec<u8>, dst: &Vec<u8>,vrf_instan: &mut ECVRF, vrf_message: &[u8], vrf_proof: &Vec<u8>, vrf_pk: &Vec<u8>,params: &UniversalParams<Curve>) {
    verify_committee(vp.c, vp.n-1, π.b_committee_of_tau,vrf_instan, vrf_message, vrf_proof, vrf_pk,params) ;

    // compute root of unity
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    //RO(SK, W, B, parsum_signer, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
    let r = random_oracle_r(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_signer_of_tau,
        π.parsum_signer_of_tau_com,
        π.qx_of_tau_signer,
        π.qz_of_tau_signer,
        π.qx_of_tau_mul_tau_signer,
        // π.qx_of_tau_committee,
        // π.qz_of_tau_committee,
        // π.qx_of_tau_mul_tau_committee,
        π.q_of_tau_com,
        π.q_sub_of_tau_com,
    );

    let v1 = random_oracle_v(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_signer_of_tau,
        π.parsum_signer_of_tau_com,
        π.qx_of_tau_signer,
        π.qz_of_tau_signer,
        π.qx_of_tau_mul_tau_signer,
        // π.qx_of_tau_committee,
        // π.qz_of_tau_committee,
        // π.qx_of_tau_mul_tau_committee,
    );

    let v2 = random_oracle_v(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_sub_of_tau,
        π.parsum_sub_of_tau_com,
        π.qx_of_tau_signer,
        π.qz_of_tau_signer,
        π.qx_of_tau_mul_tau_signer,
        // π.qx_of_tau_committee,
        // π.qz_of_tau_committee,
        // π.qx_of_tau_mul_tau_committee,
    );


    // verify the polynomial openings at r and r / ω
    verify_openings_in_proof(vp, π, r,t);

    let n: u64 = vp.n as u64;
    // this takes logarithmic computation, but concretely efficient
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n-1]);
    let l_n_minus_1_of_r = (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (r - ω_pow_n_minus_1));


    //assert polynomial identity B_sig(x) SK(x) = ask + Q_z(x) Z(x) + Q_x(x) x
    let lhs = <Curve as Pairing>::pairing(&π.b_signer_of_tau, &vp.sk_of_tau_com);
    let x1 = <Curve as Pairing>::pairing(&π.qz_of_tau_signer, &vp.z_of_tau_com);
    let x2 = <Curve as Pairing>::pairing(&π.qx_of_tau_signer, &vp.tau_com);
    let x3 = <Curve as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    assert_eq!(lhs, rhs);


    //assert checks on the public part

    let rhs = π.q_of_r * vanishing_of_r ;
    let lhs = (π.parsum_signer_of_r - π.parsum_signer_of_r_div_ω - π.w_of_r * π.b_signer_of_r)
                                                        + v1 * (π.b_signer_of_r * π.b_signer_of_r - π.b_signer_of_r)
                                                        + v1*v1*(l_n_minus_1_of_r * π.parsum_signer_of_r)
                                                        + v1*v1*v1*(l_n_minus_1_of_r * (π.b_signer_of_r - F::from(1))) ;
    assert_eq!(lhs,rhs) ;


    //..........................// for sub vector
    let rhs = π.q_sub_of_r * vanishing_of_r ;
    let lhs = (π.parsum_sub_of_r - π.parsum_sub_of_r_div_ω - π.w_sub_of_r * π.b_sub_of_r)
                                                        + v2 * (π.b_sub_of_r * π.b_sub_of_r - π.b_sub_of_r)
                                                        + v2*v2*(l_n_minus_1_of_r * π.parsum_sub_of_r)
                                                        + v2*v2*v2*(l_n_minus_1_of_r * (π.b_sub_of_r - F::from(1))) ;
    assert_eq!(lhs,rhs) ;

    //run the degree check e([Qx(τ)]_1, [τ]_2) ?= e([Qx(τ)·τ]_1, [1]_2)
    let lhs = <Curve as Pairing>::pairing(&π.qx_of_tau_signer, &vp.h_1);
    let rhs = <Curve as Pairing>::pairing(&π.qx_of_tau_mul_tau_signer, &vp.h_0);
    assert_eq!(lhs, rhs);

    //run the aggregated bls check 
    // let agg_pk = bls::point_to_pubkey(π.agg_pk) ;
    // let agg_sig = bls::point_to_signature(π.agg_sigma) ;
    // let b = bls::verify(&agg_pk, message, &agg_sig, dst) ;
    // assert_eq!(b,true) ;
    bls::bls_verify(message, dst, π.agg_pk, &params, π.agg_sigma);

}


fn compute_apk(
    pp: &AggregationKey, 
    bitmap: &Vec<F>) -> G1 {
    let n = bitmap.len();
    let mut exponents: Vec<F> = vec![];
    let n_inv = F::from(1) / F::from(n as u64);
    for i in 0..n {
        //let l_i_of_x = cache.lagrange_polynomials[i].clone();
        //let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let l_i_of_0 = n_inv;
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Curve as Pairing>::G1 as VariableBaseMSM>
        ::msm(&pp.pks[..], &exponents).unwrap().into_affine()
}

fn compute_agg_sig(
    partial_sig_vec: &Vec<PartialSig>,
    universe_size: usize,
) -> G2 {
    let mut exponents: Vec<F> = vec![];
    let mut temp = vec![] ;
    let n_inv = F::from(1) / F::from(universe_size as u64);
    for i in 0..partial_sig_vec.len() {
        exponents.push(n_inv) ;
        temp.push(partial_sig_vec[i].sigma) ;
    }
    


    <<Curve as Pairing>::G2 as VariableBaseMSM>
        ::msm(&temp[..], &exponents).unwrap().into_affine() 

}

fn preprocess_qz_contributions(
    q1_contributions: &Vec<Vec<G1>>
) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        // extract party i's hints, from which we extract the term for i.
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                // extract party j's hints, from which we extract cross-term for party i
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        // the aggregation key contains a single term that 
        // is a product of all cross-terms and the ith term
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G1>, 
    bitmap: &Vec<F>) -> G1 {
    let mut com = get_zero_poly_com_g1(&params);
    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            com = com.add(elements[i]).into_affine();
        }
    }
    com
}

fn add_all_g2(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G2>) -> G2 {
    let mut com = get_zero_poly_com_g2(&params);
    for i in 0..elements.len() {
        com = com.add(elements[i]).into_affine();
    }
    com
}

fn get_zero_poly_com_g1(params: &UniversalParams<Curve>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Curve>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&params, &zero_poly).unwrap()
}



fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = weights.len();
    let mut parsum = F::from(0);
    let mut evals = vec![];
    for i in 0..n {
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()    
}

fn hint_independent_computation(n:usize,params: &UniversalParams<Curve>,i:usize)-> HintIndependentSetupElements {
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let l_i_of_tau_com = KZG::commit_g2(&params, &l_i_of_x).expect("commitment failed");
    let mut cross_terms = Vec::new();
    for j in 0..n+1 {
        if j != i {
            let l_j_of_x = utils::lagrange_poly(n, j);
            cross_terms.push((l_j_of_x.mul(&l_i_of_x)).div(&z_of_x)) ;
        }
        else {
            cross_terms.push((l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x)).div(&z_of_x)) ;
        }
    }
    //to compute commitments to the cross terms 
    let mut cross_terms_com = Vec::with_capacity(n) ;
    for j in 0..n+1 {
            cross_terms_com.push(KZG::commit_g2(&params, &cross_terms[j]).expect("commitment failed"));
               
    }
    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let l_i_sub_l_i_zero = l_i_of_x.sub(&l_i_of_0_poly);
    //denominator is x
    let den = x_monomial.clone();

    //qx_term = (l_i(x) - l_i(0)) / x
    let qx_term = &&l_i_sub_l_i_zero.div(&den);
    //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    let qx_term_com = KZG::commit_g2(&params, &qx_term).expect("commitment failed");
    // let lhs = <Curve as Pairing>::pairing(hint.qx_i_term, params.powers_of_h[0]);
    // let rhs = <Curve as Pairing>::pairing(hint.pk_i, qx_term_com);
    // assert_eq!(lhs, rhs);

    //qx_term_mul_tau = (l_i(x) - l_i(0))
    let qx_term_mul_tau = &l_i_sub_l_i_zero;
    //qx_term_mul_tau_com = [ (l_i(τ) - l_i(0)) ]_1
    let qx_term_mul_tau_com = KZG::commit_g2(&params, &qx_term_mul_tau).expect("commitment failed");
    HintIndependentSetupElements{
        i: i,
        l_i_of_tau_com_2: l_i_of_tau_com,
        qz_i_terms: cross_terms_com,
        qx_i_term: qx_term_com,
        qx_i_term_mul_tau: qx_term_mul_tau_com,
    }


}

#[allow(dead_code)]
fn verify_hint(params: &UniversalParams<Curve>, hint: &Hint, hint_independents: &HintIndependentSetupElements) {
    let n = hint.qz_i_terms.len() ;
    //take n+3 no of random numbers to compute a random linear combination
    let mut random_numbers = Vec::with_capacity(n+3) ;
    let mut rng = ark_std::test_rng();
    let mut random_integer = u64::rand(&mut rng) ;
    for _j in 0..n+3 {
        random_numbers.push(F::from(random_integer)) ;
        random_integer = random_integer * random_integer ;
        
    }
    let mut hints_linear_comb_left = vec![] ;
    hints_linear_comb_left.push(hint.sk_i_l_i_of_tau_com_1) ;
    hints_linear_comb_left.push(hint.qx_i_term) ;
    hints_linear_comb_left.push(hint.qx_i_term_mul_tau) ;
    for i in 0..n {
        hints_linear_comb_left.push(hint.qz_i_terms[i]) ;
    }

    let mut hints_linear_comb_right = vec![] ;
    hints_linear_comb_right.push(hint_independents.l_i_of_tau_com_2) ;
    hints_linear_comb_right.push(hint_independents.qx_i_term) ;
    hints_linear_comb_right.push(hint_independents.qx_i_term_mul_tau) ;
    for i in 0..n {
        hints_linear_comb_right.push(hint_independents.qz_i_terms[i]) ;
    }


   let lhs_pipenger = <<Curve as Pairing>::G1 as VariableBaseMSM>
    ::msm(&hints_linear_comb_left[..], &random_numbers).unwrap().into_affine() ;

    let rhs_pipenger =  <<Curve as Pairing>::G2 as VariableBaseMSM>
    ::msm(&hints_linear_comb_right[..], &random_numbers).unwrap().into_affine() ;

    let lhs =  <Curve as Pairing>::pairing(lhs_pipenger, params.powers_of_h[0]);
    let rhs = <Curve as Pairing>::pairing(hint.pk_i, rhs_pipenger);

    assert_eq!(lhs,rhs) ;

}
#[allow(dead_code)]
fn generate_hints_independent_compu_and_write (
    params: &UniversalParams<Curve>,
    n: usize,  
    path: &str) -> Result<(), SerializationError> {
        let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
        let params = Arc::new(params) ;
        let hints_independent_elements = crossbeam::scope(|s| {
            let mut threads = Vec::new();
            for i in 0..n {
                //let idx = i.clone();
                //let n = n.clone();
                //let sk = sk[i];
                let params = Arc::clone(&params) ;
               // println!("Spawning thread for index: {}", i) ;
                let thread_i = s.spawn(move |_| hint_independent_computation( n, &params, i));
                threads.push(thread_i);
            }
    
            threads.into_iter().map(|t| t.join().unwrap()).collect::<Vec<_>>()
        }).unwrap();

        (hints_independent_elements.len() as u64).serialize_uncompressed(&mut file)?;

        // Serialize each `Hint` in the vector
        for temp in hints_independent_elements {
            temp.i.serialize_uncompressed(&mut file)?;
            temp.l_i_of_tau_com_2.serialize_uncompressed(&mut file)?;
            temp.qx_i_term.serialize_uncompressed(&mut file)?;
            temp.qx_i_term_mul_tau.serialize_uncompressed(&mut file)?;

            // Serialize `qz_i_terms` vector length and elements
            ((temp.qz_i_terms).len() as u64).serialize_uncompressed(&mut file)?;
            for term in &temp.qz_i_terms {
                term.serialize_uncompressed(&mut file)?;
            }
        }

        Ok(())

    }

        fn read_hints_independent_compu_from_file(path: &str) -> Result<Vec<HintIndependentSetupElements>, SerializationError> {
            let mut file = File::open(path).map_err(SerializationError::IoError)?;
            
        
            let hint_ind_count = u64::deserialize_uncompressed(&mut file)? as usize;
            let mut hints_independent_compu = Vec::with_capacity(hint_ind_count);
        
            // Deserialize each field from the file
            for _ in 0..hint_ind_count {
                let i = usize::deserialize_uncompressed(&mut file)?;
                let l_i_of_tau_com_2 = G2::deserialize_uncompressed(&mut file)?;
                let qx_i_term = G2::deserialize_uncompressed(&mut file)?;
                let qx_i_term_mul_tau = G2::deserialize_uncompressed(&mut file)?;
            // Deserialize the length of `qz_i_terms` and then each element
            let qz_i_terms_len = u64::deserialize_uncompressed(&mut file)? as usize;
            let mut qz_i_terms = Vec::with_capacity(qz_i_terms_len);
            for _ in 0..qz_i_terms_len {
                qz_i_terms.push(G2::deserialize_uncompressed(&mut file)?);
            }
        
            hints_independent_compu.push(HintIndependentSetupElements{
                i,
                l_i_of_tau_com_2,
                qz_i_terms,
                qx_i_term,
                qx_i_term_mul_tau,
            })
        
        
            }
        
           
            
            Ok(hints_independent_compu)
        }
    

#[cfg(test)]
mod tests {
    use ark_ec::short_weierstrass::Affine;

    use super::*;

    fn aggregate_sk(sk: &Vec<F>, bitmap: &Vec<F>) -> F {
        let n = sk.len();
        let mut agg_sk = F::from(0);
        for i in 0..sk.len() {
            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            agg_sk += bitmap[i] * sk[i] * l_i_of_0;
        }
        agg_sk
    }

    fn sanity_test_poly_domain_mult(
        f_of_x: &DensePolynomial<F>, 
        f_of_ωx: &DensePolynomial<F>, 
        ω: &F) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let ωr: F = ω.clone() * r;
        assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
    }

    fn sanity_test_b(
        b_signer_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_signer_of_x.degree() + 1) as u64;
    
        let b_signer_of_r = b_signer_of_x.evaluate(&r);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let left = b_signer_of_r * b_signer_of_r - b_signer_of_r;
        let right = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(left, right);
    
    }
    
    fn sanity_test_psw(
        w_of_x: &DensePolynomial<F>,
        b_signer_of_x: &DensePolynomial<F>,
        psw_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_signer_of_x.degree() + 1) as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;
        let ω_pow_n_minus_1: F = ω.pow([n-1]);
        let ωr: F = ω * r;
    
        let psw_of_r = psw_of_x.evaluate(&r);
        let psw_of_ωr = psw_of_x.evaluate(&ωr);
        let w_of_ωr = w_of_x.evaluate(&ωr);
        let b_of_ωr = b_signer_of_x.evaluate(&ωr);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
        let tmp2 = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(tmp1, tmp2);
    
        //ParSumW(ωn−1) = 0
        let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
        //println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
        assert_eq!(psw_of_ω_pow_n_minus_1, F::from(0));
    
        //b(ωn−1) = 1
        let b_of_ω_pow_n_minus_1 = b_signer_of_x.evaluate(&ω_pow_n_minus_1);
        assert_eq!(b_of_ω_pow_n_minus_1, F::from(1));
    
    }

    #[test]
    fn sanity_test_public_part() {
        // compute the nth root of unity
        //println!("The nth root of unity is: {:?}", ω);
        //println!("The omega_n_minus_1 of unity is: {:?}", ω.pow([n-1]));
        //println!("The omega_n of unity is: {:?}", ω_pow_n_minus_1 * ω);

        let weights: Vec<F> = vec![
            F::from(2), 
            F::from(3), 
            F::from(4), 
            F::from(5), 
            F::from(4), 
            F::from(3), 
            F::from(2), 
            F::from(0)-F::from(15)
        ];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n: u64 = bitmap.len() as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;

        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

        let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let b_of_ωx = utils::poly_domain_mult_ω(&b_signer_of_x, &ω);

        let psw_of_x = compute_psw_poly(&weights, &bitmap);
        let psw_of_ωx = utils::poly_domain_mult_ω(&psw_of_x, &ω);

        //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
        let t_of_x = psw_of_ωx.sub(&psw_of_x).sub(&w_of_ωx.mul(&b_of_ωx));
        let z_of_x = utils::compute_vanishing_poly(n as usize); //returns Z(X) = X^n - 1
        let q2_of_x = t_of_x.div(&z_of_x);

        let t_of_x = b_signer_of_x.mul(&b_signer_of_x).sub(&b_signer_of_x);
        let q1_of_x = t_of_x.div(&z_of_x);
        
        sanity_test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
        sanity_test_poly_domain_mult(&b_signer_of_x, &b_of_ωx, &ω);
        sanity_test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

        sanity_test_psw(&w_of_x, &b_signer_of_x, &psw_of_x, &q2_of_x);
        sanity_test_b(&b_signer_of_x, &q1_of_x);
    }

    fn sanity_test_pssk(
        sk_of_x: &DensePolynomial<F>,
        b_signer_of_x: &DensePolynomial<F>,
        q1_of_x: &DensePolynomial<F>,
        q2_of_x: &DensePolynomial<F>,
        agg_sk: &F
    ) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let n: u64 = (sk_of_x.degree() + 1) as u64;

        //SK(x) · B(x) − aSK = Q1(x) · Z(x) + Q2(x) · x
        let sk_of_r = sk_of_x.evaluate(&r);
        let b_signer_of_r = b_signer_of_x.evaluate(&r);
        let q1_of_r = q1_of_x.evaluate(&r);
        let z_of_r: F = r.pow([n]) - F::from(1);
        let q2_of_r = q2_of_x.evaluate(&r);

        let left = sk_of_r * b_signer_of_r;
        let right = (q1_of_r * z_of_r) + (q2_of_r * r) + agg_sk;
        assert_eq!(left, right);
    
    }
    #[test]
    fn bls_signature() {
        let n = 32 ;
        let rng = &mut test_rng();
        let params = KZG::setup(n, rng).expect("Setup failed");
    
    
        let sks: Vec<F> = hintgen::sample_secret_keys(n-1) ;
        let mut pks: Vec<G1> = vec![] ;
        for i in 0..n-1 {
            let sk_as_poly = utils::compute_constant_poly(&sks[i]) ;
            let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed") ;
            pks.push(pk) ;
        }

    }

    #[test]
    fn sanity_test_secret_part() {
        //let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n = bitmap.len();

        let mut secret_keys: Vec<F> = hintgen::sample_secret_keys(n - 1);
        secret_keys.push(F::from(0));

        let agg_sk = aggregate_sk(&secret_keys, &bitmap);
        let sk_of_x = utils::interpolate_poly_over_mult_subgroup(&secret_keys);
        let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let q1_of_x = compute_pssk_q1_poly(&secret_keys, &bitmap);
        let q2_of_x = compute_pssk_q2_poly(&secret_keys, &bitmap);

        sanity_test_pssk(&sk_of_x, &b_signer_of_x, &q1_of_x, &q2_of_x, &agg_sk);
    }

    fn compute_pssk_q1_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let z_of_x = utils::compute_vanishing_poly(n);
        //Li(x) · Li(x) − Li(x) / Z(x)
        let mut q1 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let num = l_i_of_x.mul(&l_i_of_x).sub(&l_i_of_x);
            //let num = num.sub(&l_i_of_x);
            let f_i = num.div(&z_of_x);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q1 = q1.add(sk_i_f_i);

            let mut q1_inner = utils::compute_constant_poly(&F::from(0));
            for j in 0..n {
                if i == j { continue; } //i != j

                let l_j_of_x = utils::lagrange_poly(n, j);
                let num = l_j_of_x.mul(&l_i_of_x);
                let f_j = num.div(&z_of_x);
                let sk_j_f_j = utils::poly_eval_mult_c(&f_j, &sk[j]);

                q1_inner = q1_inner.add(sk_j_f_j);
            }

            q1 = q1.add(q1_inner);
        }
        q1
    }

    fn compute_pssk_q2_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let x_monomial = utils::compute_x_monomial();

        let mut q2 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            let l_i_of_0 = utils::compute_constant_poly(&l_i_of_0);
            let num = l_i_of_x.sub(&l_i_of_0);
            let den = x_monomial.clone();
            let f_i = num.div(&den);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q2 = q2.add(sk_i_f_i);
        }
        q2
    }
    #[test]
    fn test_pipenger() {
        let n = 1024; 
        let mut rng = ark_std::test_rng();
        let params = KZG::setup(n, &mut rng).expect("Setup failed");
        let mut random_numbers = Vec::with_capacity(n+3) ;
        
    
        let sk = F::rand(&mut rng) ;
        //let hint = hint_gen(&params,n,1,&sk) ;
        let mut hints_linear_comb_left = vec![] ;
        let g = params.powers_of_g[0];
        hints_linear_comb_left.push((g.mul(F::from(1))).into()) ;
        hints_linear_comb_left.push((g.mul(F::from(2))).into()) ;
        hints_linear_comb_left.push((g.mul(F::from(3))).into() );
        for i in 0..n {
            hints_linear_comb_left.push(g) ;
        }
    
    //     let l_i_of_x = utils::lagrange_poly(n, 1);
    //     let z_of_x = utils::compute_vanishing_poly(n);
    
    //     let l_i_of_tau_com = KZG::commit_g2(&params, &l_i_of_x).expect("commitment failed");
    //     // let lhs = <Curve as Pairing>::pairing(hint.sk_i_l_i_of_tau_com_1, params.powers_of_h[0]);
    //     // let rhs = <Curve as Pairing>::pairing(hint.pk_i, l_i_of_tau_com);
    //     // assert_eq!(lhs, rhs);
    
    //     //l_i^2-l_i
    //     //let l_i_mult_l_i_sub_l_i = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
    //     //(l_i^2-l_i)/Z())
    //    // let l_i_mult_l_i_sub_l_i_sub_z = l_i_mult_l_i_sub_l_i.div(&z_of_x) ;
    //     //[(l_i^2-l_i)/Z())]
    //     //let l_i_mult_l_i_sub_l_i_sub_z_com = KZG::commit_g2(&params, &l_i_mult_l_i_sub_l_i_sub_z).expect("commitment failed");
    //     //now to calculate the cross terms and for i=j l_i^2-l_i
    //     let mut cross_terms = Vec::new();
    //     for j in 0..n+1 {
    //         if j != 1 {
    //             let l_j_of_x = utils::lagrange_poly(n, j);
    //             cross_terms.push((l_j_of_x.mul(&l_i_of_x)).div(&z_of_x)) ;
    //         }
    //         else {
    //             cross_terms.push((l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x)).div(&z_of_x)) ;
    //         }
    //     }
    //     //to compute commitments to the cross terms 
    //     let mut cross_terms_com = Vec::with_capacity(n) ;
    //     for j in 0..n+1 {
    //             cross_terms_com.push(KZG::commit_g2(&params, &cross_terms[j]).expect("commitment failed"));
                   
    //     }
    
    //     let x_monomial = utils::compute_x_monomial();
    //     let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    //     let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    
    //     //numerator is l_i(x) - l_i(0)
    //     let l_i_sub_l_i_zero = l_i_of_x.sub(&l_i_of_0_poly);
    //     //denominator is x
    //     let den = x_monomial.clone();
    
    //     //qx_term = (l_i(x) - l_i(0)) / x
    //     let qx_term = &&l_i_sub_l_i_zero.div(&den);
    //     //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    //     let qx_term_com = KZG::commit_g2(&params, &qx_term).expect("commitment failed");
    //     // let lhs = <Curve as Pairing>::pairing(hint.qx_i_term, params.powers_of_h[0]);
    //     // let rhs = <Curve as Pairing>::pairing(hint.pk_i, qx_term_com);
    //     // assert_eq!(lhs, rhs);
    
    //     //qx_term_mul_tau = (l_i(x) - l_i(0))
    //     let qx_term_mul_tau = &l_i_sub_l_i_zero;
    //     //qx_term_mul_tau_com = [ (l_i(τ) - l_i(0)) ]_1
    //     let qx_term_mul_tau_com = KZG::commit_g2(&params, &qx_term_mul_tau).expect("commitment failed");
    
        // let mut hints_linear_comb_right = vec![] ;
        // hints_linear_comb_right.push(l_i_of_tau_com) ;
        // hints_linear_comb_right.push(qx_term_com) ;
        // hints_linear_comb_right.push(qx_term_mul_tau_com) ;
        // for i in 0..n {
        //     hints_linear_comb_right.push(cross_terms_com[i]) ;
        // }

        let mut hints_linear_comb_right = vec![] ;
        let h = params.powers_of_h[0];
        hints_linear_comb_right.push((h.mul(F::from(1))).into()) ;
        hints_linear_comb_right.push((h.mul(F::from(2))).into()) ;
        hints_linear_comb_right.push((h.mul(F::from(3))).into() );
        for i in 0..n {
            hints_linear_comb_right.push(h) ;
        }
    

        let mut random_integer = F::rand(&mut rng) ;
        for _j in 0..n+3 {
            random_numbers.push(random_integer) ;
            random_integer = F::from((random_integer * random_integer))  ;
        }
    let start = Instant::now() ;
     for i in 0..10 {
        
            let lhs_pipenger = <<Curve as Pairing>::G1 as VariableBaseMSM>
            ::msm(&hints_linear_comb_left[..], &random_numbers).unwrap().into_affine() ;
        
            let rhs_pipenger =  <<Curve as Pairing>::G2 as VariableBaseMSM>
            ::msm(&hints_linear_comb_right[..], &random_numbers).unwrap().into_affine() ;
        }
     let duration = start.elapsed();
     println!("pippenger time is {:?}",duration) ;

       
    }
   
   #[test]
    fn generate_hints_and_sks_for_32() {
        let n = 32;
        let rng = &mut test_rng() ;
        hintgen::write_secret_keys(n, "secret_keys.bin");
        let sk = hintgen::read_secret_keys("secret_keys.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data.bin") ;
        generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
    
    }
    #[test]
    fn generate_hints_independents_32() {
        let n = 32;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
    
    }

    #[test]
    fn generate_hints_and_sks_for_64() {
        let n = 64;
        let rng = &mut test_rng() ;
        hintgen::write_secret_keys(n, "secret_keys.bin");
        let sk = hintgen::read_secret_keys("secret_keys.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
         let start = Instant::now() ;

        hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    

    }
    #[test]
    fn generate_hints_independents_64() {
        let n = 64;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
        let duration = start.elapsed();
        println!("time to compute hints independent setup elements is {:?}",duration);
    
    }
    #[test]
    fn generate_hints_and_sks_for_128() {
        let n = 128;
        let rng = &mut test_rng() ;
        hintgen::write_secret_keys(n, "secret_keys.bin");
        let sk = hintgen::read_secret_keys("secret_keys.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data.bin") ;
        let start = Instant::now() ;
        let hints = read_hints_from_file("hints_test_data.bin");
        let duration = start.elapsed();
        println!("time to read hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_128() {
        let n = 128;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints independent computations are {:?}",duration);
    
    }
    #[test]
    fn generate_hints_and_sks_for_256() {
        let n = 256;
        let rng = &mut test_rng() ;
        hintgen::write_secret_keys(n, "secret_keys.bin");
        let sk = hintgen::read_secret_keys("secret_keys.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data.bin") ;
        let start = Instant::now() ;
        let hints = read_hints_from_file("hints_test_data.bin");
        let duration = start.elapsed();
        println!("time to read hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_256() {
        let n = 256;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints independent computations are {:?}",duration);
    
    }

}
