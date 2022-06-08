
use crate::protocol::GKR;
use ark_bls12_381::Fr;

#[test]
#[ignore]
// TODO: more complicated gate types
fn test_lanczos_gkr() {
    let mut verifier = GKR::<Fr>::gkr_process_circuit("./src/test/lanczos2_112_N=16_circuit.txt");
    let result = verifier.verify();
    assert_eq!(result, true);
}