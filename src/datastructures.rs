

use ark_ff::Field;
use std::collections::HashMap;
use ark_std::ops::{Add, Mul};


#[derive(Clone, Debug)]
pub struct LayerProcessed<F: Field> {
    pub add: Vec<F>,
    pub mult: Vec<F>,
    pub gates: HashMap<usize, (usize, (usize, usize))>,
    pub gate_id: Vec<usize>,
    pub bitlength: usize,
}

#[derive(Clone, Debug)]
pub struct LayeredCircuit<F: Field> {
    pub circuit: Vec<LayerProcessed<F>>,
}


pub type InputGate<F> = (usize, usize, (F, F));
pub type Gate = (usize, usize, (usize, usize));

#[derive(Clone)]
pub struct InputLayer<F: Field> {
    pub gates: Vec<InputGate<F>>,
    pub num_gates: usize,
}

#[derive(Clone)]
pub struct Layer {
    pub gates: Vec<Gate>,
    pub num_gates: usize,
}

#[derive(Clone)]
pub struct Circuit<F: Field> {
    pub input_layer: InputLayer<F>,
    pub topology: Vec<Layer>,
    pub num_layers: usize,
}

#[derive(Clone, PartialEq, Debug)]
pub struct LinearPolynomial<F: Field> {
    pub a: F,
    pub b: F,
}

impl<F: Field> LinearPolynomial<F> {
    pub fn new(a: F, b: F) -> Self {
        LinearPolynomial {
            a: a,
            b: b,
        }
    }

    pub fn eval(&self, x: F) -> F {
        self.a * x + self.b
    }
}

impl<F: Field> Add for LinearPolynomial<F> {
    type Output = LinearPolynomial<F>;

    fn add(self, other: LinearPolynomial<F>) -> Self {
        LinearPolynomial {
            a: self.a + other.a,
            b: self.b + other.b,
        }
    }
}

impl<F: Field> Mul for LinearPolynomial<F> {
    type Output = QuadraticPolynomial<F>;

    fn mul(self, other: LinearPolynomial<F>) -> QuadraticPolynomial<F> {
        QuadraticPolynomial {
            a: self.a * other.a,
            b: self.a * other.b + self.b * other.a,
            c: self.b * other.b,
        }
    }
}

#[derive(Clone, Debug)]
pub struct QuadraticPolynomial<F: Field> {
    pub a: F,
    pub b: F,
    pub c: F,
}

impl<F: Field> QuadraticPolynomial<F> {
    pub fn new(a: F, b: F, c: F) -> Self {
        QuadraticPolynomial {
            a: a,
            b: b,
            c: c,
        }
    }

    pub fn mul(self, other: LinearPolynomial<F>) -> CubicPolynomial<F> {
        CubicPolynomial {
            a: self.a * other.a,
            b: self.a * other.b + self.b * other.a,
            c: self.b * other.b + self.c * other.a,
            d: self.c * other.b,
        }
    }

    pub fn eval(&self, x: F) -> F {
        return self.a * x * x + self.b * x + self.c;
    }
}

impl<F: Field> Add for QuadraticPolynomial<F> {
    type Output = QuadraticPolynomial<F>;

    fn add(self, other: QuadraticPolynomial<F>) -> Self {
        QuadraticPolynomial {
            a: self.a + other.a,
            b: self.b + other.b,
            c: self.c + other.c,
        }
    }
}

// impl<F: Field> Mul for QuadraticPolynomial<F> {
//     type Output = CubicPolynomial<F>;

//     fn mul(self, other: LinearPolynomial<F>) -> CubicPolynomial<F> {
//         CubicPolynomial {
//             a: self.a * other.a,
//             b: self.a * other.b + self.b * other.a,
//             c: self.b * other.b + self.c * other.a,
//             d: self.c * other.b,
//         }
//     }
// }


#[derive(Clone)]
pub struct CubicPolynomial<F: Field> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub d: F,
}

impl<F: Field> CubicPolynomial<F> {
    pub fn new(a: F, b: F, c: F, d: F) -> Self {
        CubicPolynomial {
            a: a,
            b: b,
            c: c,
            d: d,
        }
    }

    pub fn eval(&self, x: F) -> F {
        self.a * x * x * x + self.b * x * x + self.c * x + self.d
    }
}

impl<F: Field> Add for CubicPolynomial<F> {
    type Output = CubicPolynomial<F>;

    fn add(self, other: CubicPolynomial<F>) -> Self {
        CubicPolynomial {
            a: self.a + other.a,
            b: self.b + other.b,
            c: self.c + other.c,
            d: self.d + other.d,
        }
    }
}







