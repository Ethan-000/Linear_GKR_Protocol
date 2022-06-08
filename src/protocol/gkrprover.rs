


use ark_ff::{Field};
use itertools::Itertools;
use std::collections::{HashMap, BTreeMap};
use crate::datastructures::{LayeredCircuit, LinearPolynomial, QuadraticPolynomial};

#[derive(Clone)]
pub struct GKRProver<F: Field> {
    pub v_u: F,
    pub v_v: F,
    pub current_sumcheck_gates: Vec<usize>,
    pub circuit: LayeredCircuit<F>,
    pub circuit_value: Vec<HashMap<usize, F>>,

    pub sumcheck_layer_id: usize,
    pub length_g: usize,
    pub length_u: usize,
    pub length_v: usize,
    pub randomness_from_verifier: Vec<F>,
    pub alpha: F,
    pub beta: F,
    pub r_0: Vec<F>,
    pub r_1: Vec<F>,

    pub mult_array: HashMap<usize, LinearPolynomial<F>>,
    pub addv_array: HashMap<usize, LinearPolynomial<F>>,
    pub add_array: HashMap<usize, LinearPolynomial<F>>,
    pub v_mult: HashMap<usize, LinearPolynomial<F>>,
    pub v_add: HashMap<usize, LinearPolynomial<F>>,
}


impl<F: Field> GKRProver<F> {
    
    pub fn prover_init(circuit: &LayeredCircuit<F>) -> Self {
        GKRProver {
            v_u: F::zero(),
            v_v: F::zero(),
            current_sumcheck_gates: Vec::new(),
            circuit: circuit.clone(),
            circuit_value: vec![],
            sumcheck_layer_id: 0,
            length_g: 0,
            length_u: 0,
            length_v: 0,
            randomness_from_verifier: vec![],
            alpha: F::zero(),
            beta: F::zero(),
            r_0: vec![],
            r_1: vec![],
            mult_array: HashMap::new(),
            addv_array: HashMap::new(),
            add_array: HashMap::new(),
            v_mult: HashMap::new(),
            v_add: HashMap::new(),
        }
    }

    pub fn sumcheck_init(&mut self, layer_id: usize, length_g: usize, length_u: usize, length_v: usize,
         alpha: F, beta: F, r_0: Vec<F>, r_1: Vec<F>) {
        self.r_0 = r_0;
        self.r_1 = r_1;
        self.alpha = alpha;
        self.beta = beta;
        self.randomness_from_verifier = vec![];
        self.sumcheck_layer_id = layer_id;
        self.length_g = length_g;
        self.length_u = length_u;
        self.length_v = length_v;
    }

    // prepare the layer from evaluations
    pub fn sumcheck_phase1_init(&mut self) {
        self.mult_array = HashMap::new();
        self.v_mult = HashMap::new();
        for i in 0..self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id.len() {
            let g = self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id[i].clone();
            self.mult_array.insert(g, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            let temp_v = self.circuit_value[self.sumcheck_layer_id - 1].get(&g).unwrap().clone();
            self.v_mult.insert(g, LinearPolynomial::<F>::new(F::zero(), temp_v));
        }
        self.dfs_m(0, 0, &F::one(), &F::one(), 1);
        self.addv_array = HashMap::new();
        self.add_array = HashMap::new();
        self.v_add = HashMap::new();
        for i in 0..self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id.len() {
            let g = self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id[i].clone();
            self.addv_array.insert(g, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            self.add_array.insert(g, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            let temp_v = self.circuit_value[self.sumcheck_layer_id - 1].get(&g).unwrap().clone();
            self.v_add.insert(g, LinearPolynomial::<F>::new(F::zero(), temp_v));
        }
        self.dfs_a(0, 0, &F::one(), &F::one(), 0);
        self.dfs_add(0, 0, &F::one(), &F::one(), 0);
        self.current_sumcheck_gates = self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id.clone();
    }

    // calculate multilinear extension based on r_u randomness from verifier
    pub fn sumcheck_phase1_update(&mut self, previous_random: &F) -> QuadraticPolynomial<F> {
        let mut nxt_gate_id = vec![];
        for i in 0..self.current_sumcheck_gates.len() {
            let g = self.current_sumcheck_gates[i].clone();
            let target_g = g >> 1;
            nxt_gate_id.push(target_g);
        }
        nxt_gate_id = nxt_gate_id.into_iter().dedup().collect();
        let mut ret = QuadraticPolynomial::<F>::new(F::zero(), F::zero(), F::zero());
        let mut mult_addv:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut v:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        for i in 0..nxt_gate_id.len() {
            let g = nxt_gate_id[i].clone();
            let mut zero_value:F ;
            let mut one_value:F ;
            let g_zero = g << 1;
            let g_one = g << 1 | 1;
            if self.mult_array.contains_key(&g_zero) {
                zero_value = self.mult_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.mult_array.contains_key(&g_one) {
                one_value = self.mult_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            mult_addv.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.v_mult.contains_key(&g_zero) {
                zero_value = self.v_mult[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.v_mult.contains_key(&g_one) {
                one_value = self.v_mult[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            v.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));
            ret = ret + mult_addv[&g].clone() * v[&g].clone() ;
        }

        self.mult_array = mult_addv.clone();
        self.v_mult = v.clone();
        let mut mult_addv:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut v:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut new_add:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        for i in 0..nxt_gate_id.len() {
            let g = nxt_gate_id[i].clone();
            let mut zero_value:F ;
            let mut one_value:F ;
            let g_zero = g << 1;
            let g_one = g << 1 | 1;
            if self.addv_array.contains_key(&g_zero) {
                zero_value = self.addv_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.addv_array.contains_key(&g_one) {
                one_value = self.addv_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            mult_addv.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.v_add.contains_key(&g_zero){
                zero_value = self.v_add[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.v_add.contains_key(&g_one) {
                one_value = self.v_add[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            v.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.add_array.contains_key(&g_zero) {
                zero_value = self.add_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.add_array.contains_key(&g_one) {
                one_value = self.add_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            new_add.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));
            ret = ret + new_add[&g].clone() * v[&g].clone() + 
            QuadraticPolynomial::<F>::new(F::zero(), mult_addv[&g].a, mult_addv[&g].b);
        }
        self.addv_array = mult_addv.clone();
        self.v_add = v.clone();
        self.add_array = new_add.clone();
        self.current_sumcheck_gates = nxt_gate_id.clone();
        ret
    }

    pub fn sumcheck_phase2_init(&mut self, previous_random: &F, r_u: &Vec<F>)  {
        self.v_u = self.v_add[&0].eval(*previous_random);
        let circuit_value = self.circuit_value.clone();

        let mut beta_g_r0:HashMap<usize, F> = HashMap::new();
        let mut beta_g_r1:HashMap<usize, F> = HashMap::new();
        let mut beta_u:HashMap<usize, F> = HashMap::new();
        
        self.dfs_betag(&mut beta_g_r0, &self.r_0, 0, 0, F::one(), 1);
        self.dfs_betag(&mut beta_g_r1, &self.r_1, 0, 0, F::one(), 1);
        self.dfs_betau(&mut beta_u, r_u, 0, 0, F::one(), 1);

        self.mult_array = HashMap::new();
        self.v_mult = HashMap::new();
        self.add_array = HashMap::new();
        self.addv_array = HashMap::new();
        self.v_add = HashMap::new();

        for i in 0..self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id.len() {
            let v = self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id[i].clone();
            self.mult_array.insert(v, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            self.add_array.insert(v, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            self.addv_array.insert(v, LinearPolynomial::<F>::new(F::zero(), F::zero()));
            self.v_mult.insert(v, LinearPolynomial::<F>::new(F::zero(),circuit_value[self.sumcheck_layer_id - 1][&v].clone()));
            self.v_add.insert(v, LinearPolynomial::<F>::new(F::zero(),circuit_value[self.sumcheck_layer_id - 1][&v].clone()));
        }

        for i in 0..self.circuit.circuit[self.sumcheck_layer_id].gate_id.len() {
            let g = self.circuit.circuit[self.sumcheck_layer_id].gate_id[i].clone();
            let gates = self.circuit.circuit[self.sumcheck_layer_id].gates.clone();
            let ty = gates[&g].0;
            let u = gates[&g].1.0;
            let v = gates[&g].1.1;
            if ty == 1 
            {
                *self.mult_array.entry(v).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = self.mult_array[&v].clone() + 
                LinearPolynomial::<F>::new(F::zero(), 
                (beta_g_r0[&g] * beta_u[&u] * self.alpha + beta_g_r1[&g] * beta_u[&u] * self.beta) * self.v_u);    
            }
        }

        let mut beta_g_r0:HashMap<usize, F> = HashMap::new();
        let mut beta_g_r1:HashMap<usize, F> = HashMap::new();
        let mut beta_u:HashMap<usize, F> = HashMap::new();

        self.dfs_betag(&mut beta_g_r0, &self.r_0, 0, 0, F::one(), 0);
        self.dfs_betag(&mut beta_g_r1, &self.r_1, 0, 0, F::one(), 0);
        self.dfs_betau(&mut beta_u, r_u, 0, 0, F::one(), 0);

        for i in 0..self.circuit.circuit[self.sumcheck_layer_id].gate_id.len() {
            let g = self.circuit.circuit[self.sumcheck_layer_id].gate_id[i].clone();
            let gates = self.circuit.circuit[self.sumcheck_layer_id].gates.clone();
            let ty = gates[&g].0;
            let u = gates[&g].1.0;
            let v = gates[&g].1.1;
            if ty == 0
            {
                *self.add_array.entry(v).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = self.add_array[&v].clone() + 
                LinearPolynomial::<F>::new(F::zero(), beta_g_r0[&g] * beta_u[&u] * self.alpha + beta_g_r1[&g] * beta_u[&u] * self.beta);
                *self.addv_array.entry(v).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = self.addv_array[&v].clone() + 
                LinearPolynomial::<F>::new(F::zero(), beta_g_r0[&g] * beta_u[&u] * self.alpha + beta_g_r1[&g] * beta_u[&u] * self.beta);
            }
        }
        self.current_sumcheck_gates = self.circuit.circuit[self.sumcheck_layer_id - 1].gate_id.clone();
    }

    // calculate multilinear extension based on r_v randomness from verifier
    pub fn sumcheck_phase2_update(&mut self, previous_random: &F) -> QuadraticPolynomial<F> {
        let mut nxt_gate_id = vec![];
        for i in 0..self.current_sumcheck_gates.len() {
            let g = self.current_sumcheck_gates[i].clone();
            let target_g = g >> 1;
            nxt_gate_id.push(target_g);
        }
        nxt_gate_id = nxt_gate_id.into_iter().dedup().collect();
        let mut ret = QuadraticPolynomial::<F>::new(F::zero(), F::zero(), F::zero());
        let mut mult_addv:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut v:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        for i in 0..nxt_gate_id.len() {
            let g = nxt_gate_id[i].clone();
            let mut zero_value:F ;
            let mut one_value:F ;
            let g_zero = g << 1;
            let g_one = g << 1 | 1;
            if self.mult_array.contains_key(&g_zero) {
                zero_value = self.mult_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.mult_array.contains_key(&g_one) {
                one_value = self.mult_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            mult_addv.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.v_mult.contains_key(&g_zero) {
                zero_value = self.v_mult[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.v_mult.contains_key(&g_one) {
                one_value = self.v_mult[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            v.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));
            ret = ret + mult_addv[&g].clone()  * v[&g].clone() ;
        }

        self.mult_array = mult_addv.clone();
        self.v_mult = v.clone();
        let mut mult_addv:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut v:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        let mut new_add:HashMap<usize, LinearPolynomial<F>> = HashMap::new();
        for i in 0..nxt_gate_id.len() {
            let g = nxt_gate_id[i].clone();
            let mut zero_value:F ;
            let mut one_value:F ;
            let g_zero = g << 1;
            let g_one = g << 1 | 1;
            if self.addv_array.contains_key(&g_zero) {
                zero_value = self.addv_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.addv_array.contains_key(&g_one) {
                one_value = self.addv_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            mult_addv.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.v_add.contains_key(&g_zero) {
                zero_value = self.v_add[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.v_add.contains_key(&g_one){
                one_value = self.v_add[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            v.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));

            if self.add_array.contains_key(&g_zero) {
                zero_value = self.add_array[&g_zero].eval(*previous_random);
            } else {
                zero_value = F::zero();
            } 
            if self.add_array.contains_key(&g_one) {
                one_value = self.add_array[&g_one].eval(*previous_random);
            } else {
                one_value = F::zero();
            }
            new_add.insert(g, LinearPolynomial::<F>::new(one_value - zero_value, zero_value));
            ret = ret + new_add[&g].clone() * v[&g].clone() + 
            QuadraticPolynomial::<F>::new(F::zero(), mult_addv[&g].a, mult_addv[&g].b);
        }
        self.addv_array = mult_addv.clone();
        self.v_add = v.clone();
        self.add_array = new_add.clone();
        self.current_sumcheck_gates = nxt_gate_id.clone();
        ret
    }

    pub fn sumcheck_finalize(&mut self, previous_random: &F) -> 
    (F,F) {
        let v_u = self.v_u.clone();
        self.v_v = self.v_add[&0].eval(*previous_random);
        (v_u, self.v_v.clone())
    }

    // compute the multilinear extension of the input layer with
    // randomness from verifier
    pub fn v_res(&self, r: &Vec<F>, output: &Vec<(usize, F)>) -> F {
        let mut output = output.clone();
        for i in 0..r.len() {
            let mut tmp: Vec<(usize, F)> = vec![];
            let mut last_gate = 0;
            let mut cnt = 0;
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
        assert!(output.len() == 1);
        output[0].1  
    }

    pub fn dfs_m(&mut self, g: usize, depth: usize,
            alpha_value: &F, beta_value: &F, gate_type: usize) {
        if depth == self.length_g {
            if self.circuit.circuit[self.sumcheck_layer_id].gates[&g].0 != gate_type {
                return ;
            } 
            let u = self.circuit.circuit[self.sumcheck_layer_id].gates[&g].1.0.clone();
            let v = self.circuit.circuit[self.sumcheck_layer_id].gates[&g].1.1.clone();
            let temp_v = LinearPolynomial::new(F::zero(), self.circuit_value[self.sumcheck_layer_id - 1].get(&v).unwrap().clone()
            * (*alpha_value * self.alpha + *beta_value * self.beta));
            *self.mult_array.entry(u).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = 
            self.mult_array[&u].clone() + temp_v;
        } else {
            let mut g_temp = g.clone() as i64;
            g_temp &= (-1) ^ (1 << depth as i64);
            let mut g = g_temp as usize;
            self.dfs_m(g, depth + 1, 
                &(*alpha_value * (F::one() - self.r_0[depth])), &(*beta_value * (F::one() - self.r_1[depth])), gate_type);
            g |= 1 << depth;
            self.dfs_m(g, depth + 1, &(*alpha_value * self.r_0[depth]), &(*beta_value * self.r_1[depth]), gate_type);
        }
    }

    pub fn dfs_a(&mut self, g: usize, depth: usize,
        alpha_value: &F, beta_value: &F, gate_type: usize) {
        if depth == self.length_g {
            if self.circuit.circuit[self.sumcheck_layer_id].gates[&g].0 != gate_type {
                return ;
            } 
            let u = self.circuit.circuit[self.sumcheck_layer_id].gates[&g].1.0.clone();
            let v = self.circuit.circuit[self.sumcheck_layer_id].gates[&g].1.1.clone();
            let temp_v = LinearPolynomial::new(F::zero(), self.circuit_value[self.sumcheck_layer_id - 1].get(&v).unwrap().clone()
            * (*alpha_value * self.alpha + *beta_value * self.beta));
            *self.add_array.entry(u).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = 
            self.add_array[&u].clone() + temp_v;
        } else {
            let mut g_temp = g.clone() as i64;
            g_temp &= (-1) ^ (1 << depth as i64);
            let mut g = g_temp as usize;
            self.dfs_a(g, depth + 1, 
                &(*alpha_value * (F::one() - self.r_0[depth])), &(*beta_value * (F::one() - self.r_1[depth])), gate_type);
            g |= 1 << depth;
            self.dfs_a(g, depth + 1, &(*alpha_value * self.r_0[depth]), &(*beta_value * self.r_1[depth]), gate_type);
        }
    }

    pub fn dfs_add(&mut self, g: usize, depth: usize,
        alpha_value: &F, beta_value: &F, gate_type: usize){
        if depth == self.length_g {
            if self.circuit.circuit[self.sumcheck_layer_id].gates[&g].0 != gate_type {
                return ;
            } 
            let u = self.circuit.circuit[self.sumcheck_layer_id].gates[&g].1.0.clone();
            let temp_v = LinearPolynomial::new(F::zero(), *alpha_value * self.alpha + *beta_value * self.beta);
            *self.addv_array.entry(u).or_insert(LinearPolynomial::new(F::zero(), F::zero())) = 
            self.addv_array[&u].clone() + temp_v;
        } else {
            let mut g_temp = g.clone() as i64;
            g_temp &= (-1) ^ (1 << depth as i64);
            let mut g = g_temp as usize;
            self.dfs_add(g, depth + 1, 
                &(*alpha_value * (F::one() - self.r_0[depth])), &(*beta_value * (F::one() - self.r_1[depth])), gate_type);
            g |= 1 << depth;
            self.dfs_add(g, depth + 1, &(*alpha_value * self.r_0[depth]), &(*beta_value * self.r_1[depth]), gate_type);
        }
    }

    pub fn dfs_betag(&self, arr: &mut HashMap<usize, F>, r: &Vec<F>, 
        g: usize, depth: usize, value: F, gate_type: usize) {
        let length_g = self.length_g.clone();
        if depth == length_g {
            *arr.entry(g).or_insert(F::zero()) = value;
        } else {
            let mut g_temp = g.clone() as i64;
            g_temp &= (-1) ^ (1 << depth as i64);
            let mut g = g_temp as usize;
            self.dfs_betag(arr, r, g, depth + 1, value * (F::one() - r[depth]), gate_type);
            g |= 1 << depth;
            self.dfs_betag(arr, r, g, depth + 1, value * r[depth], gate_type);
        }
    }

    pub fn dfs_betau(&self, arr: &mut HashMap<usize, F>, r: &Vec<F>, 
        u: usize, depth: usize, value: F, gate_type: usize)  {
        let length_u = self.length_u.clone();
        if depth == length_u {
            *arr.entry(u).or_insert(F::zero()) = value;
        } else {
            let mut u_temp = u.clone() as i64;
            u_temp &= (-1) ^ (1 << depth as i64);
            let mut u = u_temp as usize;
            self.dfs_betau(arr, r, u, depth + 1, value * (F::one() - r[depth]), gate_type);
            u |= 1 << depth;
            self.dfs_betau(arr, r, u, depth + 1, value * r[depth], gate_type);
        }
    }

    // get output of the circuit
    pub fn evaluate(&mut self) -> Vec<(usize, F)> {
        let circuit = &self.circuit.circuit.clone();

        let mut circuit_value: Vec<HashMap<usize, F>> = vec![];
        let mut input_values: HashMap<usize, F> = HashMap::new();
        for i in 0..circuit[0].gate_id.len() {
            let ty: usize;  
            let g:usize;
            let u:usize;
            g = circuit[0].gate_id[i];
            (ty, (u, _)) = circuit[0].gates[&g];
            assert!(ty == 3 as usize);
            input_values.insert(g, F::from(u as u32));
        }
        circuit_value.push(input_values);
        for i in 1..circuit.len() {
            let mut layer_value: HashMap<usize, F> = HashMap::new();
            let mut ty: usize;  
            let mut g:usize;
            let mut u:usize;
            let mut v: usize;
            for j in 0..circuit[i].gate_id.len() {
                g = circuit[i].gate_id[j];
                (ty, (u, v)) = circuit[i].gates[&g];
                if ty == 0 as usize {
                    layer_value.insert(g, *circuit_value[i-1].get(&u).unwrap() + *circuit_value[i-1].get(&v).unwrap());
                } else if ty == 1 as usize  {
                    layer_value.insert(g, *circuit_value[i-1].get(&u).unwrap() * *circuit_value[i-1].get(&v).unwrap());
                } else if ty == 2 as usize {
                    layer_value.insert(g, F::zero());
                } else if ty == 3 as usize {
                    layer_value.insert(g, F::from(u as u32));
                } else {
                    panic!("unexpected gate type");
                }
            }
            circuit_value.push(layer_value);
        }
        self.circuit_value = circuit_value.clone();
        let res = circuit_value.last().unwrap().clone();
        self.circuit_value = circuit_value;
        let a = hashmap_to_treemap(&res);
        let b = treemap_to_tuples(&a);
        b
    }

}

fn hashmap_to_treemap<F: Field>(map: &HashMap<usize, F>) -> BTreeMap<usize, F> {
    BTreeMap::from_iter(map.iter().map(|(i, v)| (*i, *v)))
}

fn treemap_to_tuples<F: Field>(map: &BTreeMap<usize, F>) -> Vec<(usize, F)> {
    map.iter().map(|(i, v)| (*i, *v)).collect::<Vec<(usize, F)>>()
}


