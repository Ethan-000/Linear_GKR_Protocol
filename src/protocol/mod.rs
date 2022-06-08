pub mod gkrprover;
pub mod gkrverifier;


use crate::datastructures::{Circuit, LayeredCircuit, LayerProcessed};
use crate::protocol::gkrverifier::GKRVerifier;
use std::collections::HashMap;
use ark_ff::Field;

use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

pub struct GKR<F: Field> {
    pub circuit: LayeredCircuit<F>,
}

impl<F: Field> GKR<F>{

    // read circuit from code
    pub fn gkr_init(circuit: &Circuit<F>) -> GKRVerifier<F> {
        let mut layered_circuit = LayeredCircuit {
            circuit: Vec::new(),
        };

        // process a layer
        for i in 0..circuit.num_layers {
            let mut process_layer = LayerProcessed {
                add: Vec::new(),
                mult: Vec::new(),
                gates: HashMap::new(),
                gate_id: Vec::new(),
                bitlength: 0,
            };

            let n = circuit.topology[i].num_gates;
            let mut max_gate = 0;

            // process gates in a layer
            for j in 0..n {
                let ty = circuit.topology[i].gates[j].0;
                let g = circuit.topology[i].gates[j].1;
                let u = circuit.topology[i].gates[j].2.0;
                let v = circuit.topology[i].gates[j].2.1;
                if g > max_gate {
                    max_gate = g;
                }
                process_layer.gates.insert(g, (ty, (u, v)));
                process_layer.gate_id.push(g);
            }

            // count the number of bits(variables) in a layer
            let mut cnt = 0;
            while max_gate != 0 {
                cnt += 1;
                max_gate = max_gate >> 1;
            }
            max_gate = 1;
            while cnt != 0 {
                max_gate = max_gate << 1;
                cnt -= 1;
            }
            let mut mx_gate = max_gate;
            while mx_gate != 0 {
                cnt += 1;
                mx_gate = mx_gate >> 1;
            }
            if n == 1 {
                process_layer.gate_id.push(max_gate);
                process_layer.gates.insert(max_gate, (2, (0, 0)));
                process_layer.bitlength = cnt;
            } else {
                process_layer.bitlength = cnt - 1;
            }
            layered_circuit.circuit.push(process_layer.clone());
        }
        let verifier = GKRVerifier::verifier_init(layered_circuit);
        verifier
    }

    // read circuit from file
    pub fn gkr_process_circuit(file_name: &str) -> GKRVerifier<F>  {

        let mut layered_circuit = LayeredCircuit {
            circuit: Vec::new(),
        };

        let mut data: Vec<Vec<i64>> = Vec::new();

        if let Ok(lines) = read_lines(file_name) {
            // Consumes the iterator, returns an (Optional) String
            for line in lines {
                if let Ok(ip) = line {
                    let d:Vec<i64> = ip.split(char::is_whitespace).filter(|x|  (x != &"")).
                            map(|number| number.parse::<i64>().unwrap()).collect();
                    data.push(d);
                }
            }
        } else {
            println!("Could not open file");
        }

        // total number of layers
        let d = data[0][0] as usize;


        for i in 1..d+1 {
            let mut process_layer = LayerProcessed {
                add: Vec::new(),
                mult: Vec::new(),
                gates: HashMap::new(),
                gate_id: Vec::new(),
                bitlength: 0,
            };

            // total number of gates in a layer
            let n = data[i][0];
            let mut max_gate = 0;

            for j in 1..n+1 {
                let index = (4 * (j - 1) + 1) as usize;
                let ty = data[i][index] as usize;
                let g = data[i][index + 1] as usize;
                let u = data[i][index + 2] as usize;
                let v = data[i][index + 3] as usize;
                if g > max_gate {
                    max_gate = g;
                }
                process_layer.gates.insert(g, (ty, (u, v)));
                process_layer.gate_id.push(g);
            }

            // count the number of bits(variables) in a layer
            let mut cnt = 0;
            while max_gate != 0 {
                cnt += 1;
                max_gate = max_gate >> 1;
            }
            max_gate = 1;
            while cnt != 0 {
                max_gate = max_gate << 1;
                cnt -= 1;
            }
            let mut mx_gate = max_gate;
            while mx_gate != 0 {
                cnt += 1;
                mx_gate = mx_gate >> 1;
            }
            if n == 1 {
                process_layer.gate_id.push(max_gate);
                process_layer.gates.insert(max_gate, (2, (0, 0)));
                process_layer.bitlength = cnt;
            } else {
                process_layer.bitlength = cnt - 1;
            }
            layered_circuit.circuit.push(process_layer.clone());
        }
        let verifier = GKRVerifier::verifier_init(layered_circuit);
        verifier
    }
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}