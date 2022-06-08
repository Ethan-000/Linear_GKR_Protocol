


use ark_ff::Field;
use crate::datastructures::LayeredCircuit;
use crate::protocol::gkrprover::GKRProver;
use rand::RngCore;


pub struct GKRVerifier<F: Field> {
    pub circuit: LayeredCircuit<F>,
}

impl <F: Field> GKRVerifier<F> {

    pub fn verifier_init(circuit: LayeredCircuit<F>) -> Self {
        GKRVerifier {
            circuit: circuit,
        }
    }

    pub fn verify(&mut self) -> bool {

        // initialize the prover
        let mut prover = GKRProver::prover_init(&self.circuit);

        // evaluate the circuit
        let result = prover.evaluate();

        let mut alpha = F::one();
        let mut beta = F::zero();

        let mut rng = ark_std::rand::thread_rng();
        let l = self.circuit.circuit[self.circuit.circuit.len() - 1].bitlength;
        let mut r_0 = self.generate_randomness(&mut rng, l);
        let mut r_1 = self.generate_randomness(&mut rng, l);

        // compute the multilinear extension of the input layer with
        // randomness from verifier
        let mut a0 = prover.v_res(&r_0, &result);
        a0 = a0 * alpha;

        let a1 = beta.clone();

        let mut alpha_beta_sum = a0 + a1;

        for i in (1..self.circuit.circuit.len()).rev() {
            prover.sumcheck_init(
                i, 
                self.circuit.circuit[i].bitlength,
                self.circuit.circuit[i - 1].bitlength,
                self.circuit.circuit[i - 1].bitlength,
                alpha.clone(),
                beta.clone(),
                r_0.clone(),
                r_1.clone()
            );
            prover.sumcheck_phase1_init();
            let mut previous_random = F::zero();
            let r_u = self.generate_randomness(&mut rng, self.circuit.circuit[i-1].bitlength);
            let r_v = self.generate_randomness(&mut rng, self.circuit.circuit[i-1].bitlength);
    
    
            for j in 0..self.circuit.circuit[i-1].bitlength {
                let poly = prover.sumcheck_phase1_update(&previous_random);
                previous_random = r_u[j].clone();
                if poly.eval(F::zero()) + poly.eval(F::one()) != alpha_beta_sum {
                    return false;
                } 
                alpha_beta_sum = poly.eval(r_u[j]);
            }
        
            prover.sumcheck_phase2_init(&previous_random, &r_u);
            let mut previous_random = F::zero();
            for j in 0..self.circuit.circuit[i-1].bitlength {
                let poly = prover.sumcheck_phase2_update(&previous_random);
                previous_random = r_v[j].clone();
                if poly.eval(F::zero()) + poly.eval(F::one()) != alpha_beta_sum {
                    println!("phase2 falied");
                    return false;
                } 
                alpha_beta_sum = poly.eval(r_v[j]);
            }

            let v_u:F;
            let v_v:F;
            (v_u, v_v) = prover.sumcheck_finalize(&previous_random);

            let mult_value = self.mult(i, &r_0, &r_u, &r_v) * alpha + self.mult(i, &r_1, &r_u, &r_v) * beta;
            let add_value = self.add(i, &r_0, &r_u, &r_v) * alpha + self.add(i, &r_1, &r_u, &r_v) * beta;
            
            if alpha_beta_sum != add_value * (v_u + v_v) + mult_value * v_u * v_v
            {
                return false;
            }
            alpha = self.generate_randomness(&mut rng, 1)[0];
            beta = self.generate_randomness(&mut rng, 1)[0];
            alpha_beta_sum = alpha * v_u + beta * v_v;
            r_0 = r_u;
            r_1 = r_v;
        }

        let mut input:Vec<(usize, F)> = vec![];
        for i in 0..self.circuit.circuit[0].gate_id.len() {
            let g = self.circuit.circuit[0].gate_id[i].clone();
            if self.circuit.circuit[0].gates[&g].0 == 3
            {
                input.push((g, F::from(self.circuit.circuit[0].gates[&g].1.0.clone() as u32)));
            }
        }
        let input_0 = self.v_in(&r_0, &input);
        let input_1 = self.v_in(&r_1, &input);
        if alpha_beta_sum != input_0 * alpha + input_1 * beta
        {
            return false;
        }
        true
    }

    pub fn add(&self, depth: usize, z: &Vec<F>, r_u: &Vec<F>, r_v: &Vec<F>) -> F {
        let mut ret = F::zero();
        for i in 0..self.circuit.circuit[depth].gate_id.len() {
            let mut g = self.circuit.circuit[depth].gate_id[i].clone();
            let ty = self.circuit.circuit[depth].gates[&g].0;
            let mut cur = F::one();
            if ty == 0 {
                let mut u = self.circuit.circuit[depth].gates[&g].1.0;
                let mut v = self.circuit.circuit[depth].gates[&g].1.1;
                for j in 0..self.circuit.circuit[depth].bitlength as usize {
                    if (g & 1) == 0{
                        cur = cur * (F::one() - z[j]);
                    } else {
                        cur = cur * z[j];
                    }
                    g >>= 1;
                }
                for j in 0..self.circuit.circuit[depth-1].bitlength as usize {
                    if (u & 1) == 0{
                        cur = cur * (F::one() - r_u[j]);
                    } else {
                        cur = cur * r_u[j];
                    }
                    u >>= 1;
                }
                for j in 0..self.circuit.circuit[depth-1].bitlength as usize {
                    if (v & 1) == 0{
                        cur = cur * (F::one() - r_v[j]);
                    } else {
                        cur = cur * r_v[j];
                    }
                    v >>= 1;
                }
                ret = ret + cur;
            }
        }
        ret
    }

    pub fn mult(&self, depth: usize, z: &Vec<F>, r_u: &Vec<F>, r_v: &Vec<F>) -> F {
        let mut ret = F::zero();
        for i in 0..self.circuit.circuit[depth].gate_id.len() {
            let mut g = self.circuit.circuit[depth].gate_id[i].clone();
            let ty = self.circuit.circuit[depth].gates[&g].0;
            let mut cur = F::one();
            if ty == 1 {
                let mut u = self.circuit.circuit[depth].gates[&g].1.0;
                let mut v = self.circuit.circuit[depth].gates[&g].1.1;
                for j in 0..self.circuit.circuit[depth].bitlength as usize {
                    if (g & 1) == 0{
                        cur = cur * (F::one() - z[j]);
                    } else {
                        cur = cur * z[j];
                    }
                    g >>= 1;
                }
                for j in 0..self.circuit.circuit[depth-1].bitlength as usize {
                    if (u & 1) == 0{
                        cur = cur * (F::one() - r_u[j]);
                    } else {
                        cur = cur * r_u[j];
                    }
                    u >>= 1;
                }
                for j in 0..self.circuit.circuit[depth-1].bitlength as usize {
                    if (v & 1) == 0{
                        cur = cur * (F::one() - r_v[j]);
                    } else {
                        cur = cur * r_v[j];
                    }
                    v >>= 1;
                }
                ret = ret + cur;
            }
        }
        ret
    }

    pub fn v_in(&self, r: &Vec<F>, output: &Vec<(usize, F)>) -> F {
        let mut output = output.clone();
        for i in 0..r.len() {
            let mut tmp: Vec<(usize, F)> = vec![];
            let mut cnt = 0;
            let mut last_gate = 0;
            for j in 0..output.len() {
                let mut m = r[i];
                if (output[j].0 & 1) == 0
                {
                    m = F::one() - m;
                }
                if j == 0
                {
                    tmp.push((output[j].0 >> 1, output[j].1 * m));
                    last_gate = output[j].0 >> 1;
                    cnt += 1;
                }
                else
                {
                    if (output[j].0 >> 1) == last_gate
                    {
                        tmp[cnt - 1] = (last_gate, tmp[cnt - 1].1 + output[j].1 * m);
                    }
                    else
                    {
                        last_gate = output[j].0 >> 1;
                        tmp.push((output[j].0 >> 1, output[j].1 * m));
                        cnt += 1;
                    }
                }
            }
            output = tmp.clone();
        }
        assert_eq!(output.len(), 1);
        output[0].1  
    }

    pub fn generate_randomness<R: RngCore>(&self, rng: &mut R, l: usize) -> Vec<F> {
        let mut r = vec![];
        for _ in 0..l {
            r.push(F::rand(rng));
        }
        r
    }
}
