

use ark_ff::{Field, Zero, One};
use crate::protocol::GKR;
use crate::protocol::gkrprover::GKRProver;
use ark_bls12_381::Fr;
use crate::datastructures::{InputLayer, Layer, Circuit};


fn simple_circuit<F: Field>() -> Circuit<F> {
    let one = F::one();
    let input_gate_zero = (3 as usize, 0 as usize, (one, one));
    let input_gate_one = (3 as usize, 1 as usize, (one, one));
    let input_gate_two = (3 as usize, 2 as usize, (one, one));
    let input_gate_three = (3 as usize, 3 as usize, (one, one));
    let layer_zero = InputLayer {
        gates: vec![input_gate_zero, input_gate_one, input_gate_two, input_gate_three],
        num_gates: 4,
    };
    let layer_dummy = Layer {
        gates: vec![(3 as usize, 0 as usize, (1 as usize, 1 as usize)), (3 as usize, 1 as usize, (1 as usize, 1 as usize)), 
                     (3 as usize, 2 as usize, (1 as usize, 1 as usize)), (3 as usize, 3 as usize, (1 as usize, 1 as usize))],
        num_gates: 4,
    };
    let layer_one = Layer {
        gates: vec![(0 as usize, 0 as usize, (0 as usize, 1 as usize)), (1 as usize, 1 as usize, (2 as usize, 3 as usize))],
        num_gates: 2,
    };
    let output_layer = Layer {
        gates: vec![(1 as usize, 0 as usize, (0 as usize, 1 as usize))],
        num_gates: 1,
    };
    Circuit {
        input_layer: layer_zero,
        topology: vec![layer_dummy, layer_one, output_layer],
        num_layers: 3,
    }
}


#[test]
fn test_evaluation() {
    let circuit = simple_circuit::<Fr>();
    let verifier = GKR::gkr_init(&circuit);
    let layered_circuit = verifier.circuit;
    let mut gkrprover = GKRProver::prover_init(&layered_circuit);
    let result = gkrprover.evaluate();
    let expected = vec![(0 as usize, Fr::one() + Fr::one()), 
                        (1 as usize, Fr::zero()), ];
    assert_eq!(result, expected);
}

#[test]
fn test_simple_circuit() {
    let circuit = simple_circuit::<Fr>();
    let mut verifier = GKR::gkr_init(&circuit);
    let result = verifier.verify();
    assert_eq!(result, true);
}

#[test]
fn test_circuit_from_file() {
    let mut verifier = GKR::<Fr>::gkr_process_circuit("./src/test/test_circuit.txt");
    let result = verifier.verify();
    assert_eq!(result, true);
}

