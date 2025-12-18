use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisMode};
use ark_std::*; 
use rand::RngCore;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_ff::Fp256;
use core::prelude::v1;
use std::{collections::{HashMap, BTreeMap}, f32::consts::E, process::Output};
use std::io::{BufRead,BufReader as StdBufReader};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use ark_ff::BigInteger;

use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable, LinearCombination}, 
};


type Wire = u64; 

#[allow(non_snake_case)]
#[derive(Clone)]
pub struct Parser<F: PrimeField> {
    pub numWires: usize,
    pub wireUseCounters: HashMap<Wire, usize>,
    pub variables: HashMap<Wire, Variable>,
    pub wireLinearCombinations: HashMap<Wire, LinearCombination<F>>,
    pub wireValues: HashMap<Wire, F>,
    pub toClean: Vec<Wire>,
	pub inputWireIds: Vec<Wire>,
	pub nizkWireIds: Vec<Wire>,
	pub outputWireIds: Vec<Wire>,
    pub path: String,
    pub path_input: String,
    pub numInputs: usize,
    pub numNizkInputs: usize, 
    pub numOutputs: usize,
    pub flag: bool,
    pub fake: Option<F>,
}

impl <F:PrimeField> Parser<F>{
    pub fn new(path: String, path_input: String) -> Self {

        let mut flag = true;
        if path_input == ""{
            flag = false;
        }

        Self {
            numWires: 0,
            wireUseCounters: HashMap::new(),
            variables: HashMap::new(),
            wireValues: HashMap::new(),
            wireLinearCombinations: HashMap::new(),
            toClean: Vec::new(),
            inputWireIds: Vec::new(),
            nizkWireIds: Vec::new(),
            outputWireIds: Vec::new(),
            path: path.into(),
            path_input: path_input.into(),
            numInputs: 0,
            numNizkInputs: 0, 
            numOutputs: 0,
            flag: flag,
            fake: Some(F::one()),
        }
    }


    pub fn align_abc(
        a: &Vec<Vec<(F, usize)>>,
        b: &Vec<Vec<(F, usize)>>,
        c: &Vec<Vec<(F, usize)>>,
    ) -> (
        Vec<(usize, usize, F)>, 
        Vec<(usize, usize, F)>, 
        Vec<(usize, usize, F)>, 
    ) {
        let mut merged: BTreeMap<(usize, usize), (F, F, F)> = BTreeMap::new();

        for (r, row) in a.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.0 += val;
                }
            }
        }
        
        for (r, row) in b.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.1 += val;
                }
            }
        }
   
        for (r, row) in c.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.2 += val;
                }
            }
        }


        let mut A_aligned = Vec::with_capacity(merged.len());
        let mut B_aligned = Vec::with_capacity(merged.len());
        let mut C_aligned = Vec::with_capacity(merged.len());

        eprintln!("Aligned len: {}", merged.len());

        for (&(r, c), &(aval, bval, cval)) in merged.iter() {

            A_aligned.push((r, c, aval));
            B_aligned.push((r, c, bval));
            C_aligned.push((r, c, cval));
        }

        (A_aligned, B_aligned, C_aligned)
    }

    pub fn obtain_num_var_to_pad(&self, cs: ConstraintSystemRef<F>) -> usize {
        //let ics: ConstraintSystemRef<F> = ConstraintSystem::new_ref();
        //self.clone().generate_constraints(ics.clone()).unwrap();
        let matrix = cs.to_matrices().unwrap();

        let mut merged: BTreeMap<(usize, usize), (F, F, F)> = BTreeMap::new();

        let a = &matrix.a;
        let b = &matrix.b;
        let c = &matrix.c;

        for (r, row) in a.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.0 += val;
                   
                }
            }
        }
        
        for (r, row) in b.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.1 += val;
                }
            }
        }
   
        for (r, row) in c.iter().enumerate() {
            for &(val, col) in row {
                if !val.is_zero() {
                    let e = merged.entry((r, col)).or_insert((F::zero(), F::zero(), F::zero()));
                    e.2 += val;
                }
            }
        }

        //eprintln!("Count A: {}, Count B: {}, Count C: {}", count_a, count_b, count_c);
        //assert!(count_a == count_b && count_b == count_c);
        merged.len()

    }


    pub fn transform(&self, c: Parser<F>) -> Result<(Vec<(usize, usize, F)>, Vec<(usize, usize, F)>, Vec<(usize, usize, F)>, usize, usize, usize, Vec<F>, Vec<F>), SynthesisError> {
        let pcs = ConstraintSystem::new_ref();
        let ics: ConstraintSystemRef<F> = ConstraintSystem::new_ref();
        pcs.set_mode(SynthesisMode::Prove{
            construct_matrices: true,
        });
        c.clone().generate_constraints(pcs.clone())?;
        let (formatted_input_assignment, witness_assignment) = {
            let pcs = pcs.borrow().unwrap();
            (
                pcs.instance_assignment.as_slice().to_vec(),
                pcs.witness_assignment.as_slice().to_vec(),
            )
        };

        c.generate_constraints(ics.clone())?;
        let matrix = ics.to_matrices().unwrap();
        let num_var = ics.num_witness_variables(); // + ics.num_instance_variables(); -> devo inserirlo o no?
        let num_cons = ics.num_constraints();
        let num_input = ics.num_instance_variables();

        

        let (a_aligned, b_aligned, c_aligned) = Self::align_abc(&matrix.a, &matrix.b, &matrix.c);
        Ok((a_aligned, b_aligned, c_aligned, num_var, num_cons, num_input, formatted_input_assignment, witness_assignment))
    }


    fn open_reader(path: &str) -> io::Result<StdBufReader<std::fs::File>> {
        let f = std::fs::File::open(path)?;
        Ok(StdBufReader::new(f))
    }

    pub fn parsing(&mut self) -> Result<(), SynthesisError> {

        if self.flag{
            let reader_input = Self::open_reader(&self.path_input).map_err(|e| {
                eprintln!("Input file not found");
                SynthesisError::Unsatisfiable
            })?;
            let mut lines_input = reader_input.lines().enumerate();
            for (i,line_t) in lines_input.by_ref(){

                let line = line_t.map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
                let line = line.splitn(2, '#').next().unwrap().trim_end();
                let line = line.trim();

                if!(line.starts_with("#") || line.is_empty()){

                    let mut line = line.split_whitespace();
                    let wire_str = line.next().ok_or_else(|| {eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
                    let wire_id: Wire = wire_str
                    .parse()
                    .map_err(|_| ark_relations::r1cs::SynthesisError::Unsatisfiable)?;

                    let value_str = line.next().ok_or_else(|| {eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;

                    let value = BigUint::parse_bytes(value_str.trim().as_bytes(),16)
                        .ok_or_else(|| {eprintln!("Invalid HEX format"); SynthesisError::Unsatisfiable})?;

                    let field_value = F::from_be_bytes_mod_order(&value.to_bytes_be());
                    self.wireValues.insert(wire_id, field_value);
                    
                }
            }
        }

        let reader = Self::open_reader(&self.path).map_err(|e| {
            eprintln!("File not found");
            SynthesisError::Unsatisfiable
        })?;
        let lines = reader.lines().enumerate();

        for (i,line_t) in lines{

            let line = line_t.map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
            let line = line.splitn(2, '#').next().unwrap().trim_end();
            let line = line.trim();

            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            else if i == 0{
                if let Some(line_i) = line.strip_prefix("total ") {
                    self.numWires = line_i.trim().parse::<usize>().map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
                }
                else {
                    eprintln!("File not conforming -> First line without total count");
                    return Err(SynthesisError::Unsatisfiable);
                } 
                
            }

           else if let Some(line_i) = line.strip_prefix("input ") {
                self.numInputs += 1;
                let w: Wire = line_i.trim().parse().map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
                self.inputWireIds.push(w);
            }

            else if let Some(line_i) = line.strip_prefix("nizkinput ") {
                self.numNizkInputs += 1;
                let w: Wire = line_i.trim().parse().map_err(|e| { eprintln!("Error reading line {} ", i); SynthesisError::Unsatisfiable })?;
                self.nizkWireIds.push(w);
            }

            else if let Some(line_i) = line.strip_prefix("output ") {
                self.numOutputs += 1;
                let w: Wire = line_i.trim().parse().map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
                self.outputWireIds.push(w);
                let c: &mut usize = self.wireUseCounters.entry(w).or_default();
                *c += 1; 
            }
            
            else {

                let (op, after_op) = line.split_once(" in ").ok_or_else(|| { eprintln!("Missing *IN* for operation, line {}", i); SynthesisError::Unsatisfiable })?;
                let (in_blk, after_inputs) = after_op.split_once(" out ").ok_or_else(|| { eprintln!("Missing *OUT* for operation, line {}", i); SynthesisError::Unsatisfiable })?;
                    
                let input_str = in_blk
                    .split_once('<')
                    .and_then(|(_, r)| r.split_once('>'))
                    .map(|(ids, _)| ids)
                    .unwrap_or("");

                let output_str = after_inputs
                    .split_once('<')
                    .and_then(|(_, r)| r.split_once('>'))
                    .map(|(ids, _)| ids)
                    .unwrap_or("");

            

                let input_ids: Vec<Wire> = input_str
                .split_whitespace()
                .map(|t| t.parse().map_err(|_| SynthesisError::Unsatisfiable))
                .collect::<Result<_, _>>()?;

                let output_ids: Vec<Wire> = output_str
                .split_whitespace()
                .map(|t| t.parse().map_err(|_| SynthesisError::Unsatisfiable))
                .collect::<Result<_, _>>()?;

                for &w in &input_ids {
                    *self.wireUseCounters.entry(w).or_default() += 1;
                }

                if self.flag{
                    if op == "add"{
                        if output_ids.len() != 1 || input_ids.len() < 2 {
                            eprintln!("ADD non conforme, linea: {}", i);
                            return Err(SynthesisError::Unsatisfiable);
                        }
                        
                        let mut value: F = F::zero();
                        for &w in &input_ids {
                            let v = self.wireValues.get(&w).ok_or_else(|| {eprintln!("Missing value for wire {}", w); SynthesisError::Unsatisfiable})?;
                            value += *v;
                        }
                        self.wireValues.insert(output_ids[0], value);
                    }
                    else if op == "mul"{
                        let input_1 = input_ids[0];
                        let input_2 = input_ids[1];
                        let output = output_ids[0];

                        let v1 = self.wireValues.get(&input_1).ok_or_else(|| {eprintln!("Missing value for wire {}", input_1); SynthesisError::Unsatisfiable})?;
                        let v2 = self.wireValues.get(&input_2).ok_or_else(|| {eprintln!("Missing value for wire {}", input_2); SynthesisError::Unsatisfiable})?;
                        let value = *v1 * *v2;
                        self.wireValues.insert(output, value);
                    }
                    else if op == "xor"{
                        let input_1 = input_ids[0];
                        let input_2 = input_ids[1];
                        let output = output_ids[0];

                        let v1 = self.wireValues.get(&input_1).ok_or_else(|| {eprintln!("Missing value for wire {}", input_1); SynthesisError::Unsatisfiable})?;
                        let v2 = self.wireValues.get(&input_2).ok_or_else(|| {eprintln!("Missing value for wire {}", input_2); SynthesisError::Unsatisfiable})?;

                        let v1_norm = Self::fe_to_biguint_canonical(&v1);
                        let v2_norm = Self::fe_to_biguint_canonical(&v2);
                        let two = F::one() + F::one();
                        
                        let out_val = *v1 + *v2 - two * (*v1) * (*v2);
                        if v1_norm != BigUint::from(0u8) && v1_norm != BigUint::from(1u8) {
                            eprintln!("Non-boolean value for xor operation, wire {}", input_1);
                        }
                        if v2_norm != BigUint::from(0u8) && v2_norm != BigUint::from(1u8) {
                            eprintln!("Non-boolean value for xor operation, wire {}", input_2);
                        }

                        self.wireValues.insert(output, out_val);


                    }
                    else if op == "or"{
                        let input_1 = input_ids[0];
                        let input_2 = input_ids[1];
                        let output = output_ids[0];

                        let v1 = self.wireValues.get(&input_1).ok_or_else(|| {eprintln!("Missing value for wire {}", input_1); SynthesisError::Unsatisfiable})?;
                        let v2 = self.wireValues.get(&input_2).ok_or_else(|| {eprintln!("Missing value for wire {}", input_2); SynthesisError::Unsatisfiable})?;

                        let out_val = *v1 + *v2 - (*v1) * (*v2);
                        self.wireValues.insert(output, out_val);

                    }
                    else if op == "assert"{
                        continue;
                    }
                    else if op == "zerop"{


                        // NOTE: in the original code, output_1 was not used (an other witness variable was allocated. This looks strange to me,
                        // since it looks like the first output is never used and it is designed to contain either the inverse of input (if not zero)
                        // or a random value (if zero)) -> if input != 0, output2 = 1; otherwise, output2 = 0. I will be using the output_1 as container to
                        // allocate one less variable

                        let input      = input_ids[0];
                        let output_1  = output_ids[0];
                        let output_2   = output_ids[1];

                        let v = *self.wireValues.get(&input).ok_or_else(|| {eprintln!("Missing value for wire {}", input); SynthesisError::Unsatisfiable})?;

                        if v == F::zero(){
                            self.wireValues.insert(output_2, F::zero());
                            self.wireValues.insert(output_1, F::zero()); //zero is as good as any number
                        }
                        else{
                            self.wireValues.insert(output_2, F::one());
                            self.wireValues.insert(output_1, v.inverse().unwrap_or(F::zero()));
                        }

                    }
                    else if op == "split"{
                        let n = output_ids.len();
                        let input = input_ids[0];
                        let value = self.wireValues.get(&input).ok_or_else(|| {eprintln!("Missing value for wire {}", input); SynthesisError::Unsatisfiable})?;

                        let v = Parser::<F>::fe_to_biguint_canonical(&value);

                        for (i, &w) in output_ids.iter().enumerate() {
                            let bit = ((&v>>i) & BigUint::from(1u8)).to_u64().unwrap() as u64;
                            self.wireValues.insert(w, F::from(bit));

                        }

                        
                        
                    }

                    else if op == "pack"{

                        let n = input_ids.len();

                        let output = output_ids[0];
                        let input_1 = input_ids[0];
                        if self.variables.contains_key(&output) {
                            eprintln!("PACK: output already defined");
                            return Err(SynthesisError::Unsatisfiable);
                        }

                        let value_ref = self.wireValues.get(&input_1).ok_or_else(|| {eprintln!("Missing value for wire {}", input_1); SynthesisError::Unsatisfiable})?;
                        let mut value = *value_ref;
                        
                        let mut two_i: F = F::one();

                        for &bit_w in &input_ids[1..] {
                            let value_bit = *self.wireValues.get(&bit_w).ok_or_else(|| {eprintln!("Missing value for wire {}", bit_w); SynthesisError::Unsatisfiable})?;
                            let value_norm = Self::fe_to_biguint_canonical(&value_bit);
                            if value_norm != BigUint::from(0u8) && value_norm != BigUint::from(1u8) {
                                eprintln!("Non-boolean value in pack operation for wire {}", bit_w);
                            }
                            two_i += two_i;
                            value = value + value_bit * two_i;
                        }

                        self.wireValues.insert(output, value);

                    }

                    else if let Some(hexstr) = op.strip_prefix("const-mul-neg-"){
                       let big = BigUint::parse_bytes(hexstr.trim().as_bytes(),16)
                        .ok_or_else(|| {eprintln!("Wrong hex format"); SynthesisError::Unsatisfiable})?;
                        let constant = F::from_be_bytes_mod_order(&big.to_bytes_be());
                        let input = input_ids[0];
                        let value = self.wireValues.get(&input).ok_or_else(|| {eprintln!("Missing value for wire {}", input); SynthesisError::Unsatisfiable})?;
                        let output = output_ids[0];
                        let final_value = -*value * constant;
                        self.wireValues.insert(output, final_value);
                    }

                    else if let Some(hexstr) = op.strip_prefix("const-mul-"){
                        let big = BigUint::parse_bytes(hexstr.trim().as_bytes(),16)
                        .ok_or_else(|| {eprintln!("Wrong hex format"); SynthesisError::Unsatisfiable})?;
                        let constant = F::from_be_bytes_mod_order(&big.to_bytes_be());
                        let input = input_ids[0];
                        let value = self.wireValues.get(&input).ok_or_else(|| {eprintln!("Missing value for wire {}", input); SynthesisError::Unsatisfiable})?;
                        let output = output_ids[0];
                        let final_value = *value * constant;
                        self.wireValues.insert(output, final_value);
                    }

                    else {
                        eprintln!("Error at line {}, unknown operation {}", i, op);
                    }

                    
                
                }

                else{
                    if op == "assert" {
                        if let Some(&w0) = output_ids.first() {
                        *self.wireUseCounters.entry(w0).or_default() += 1;
                        }
                    }

                    else if op == "add" || op == "mul" || op == "xor" || op == "or" || op == "split" || op == "pack" || op == "zerop" {
                        continue;
                    } 
                    
                    else if op.starts_with("const-mul-") {
                        continue;
                    
                    } 
                    else {
                        eprintln!("Wrong file format");
                        return Err(SynthesisError::Unsatisfiable);
                    }
                }
            }

        }

        
        Ok(())

    }

    pub fn fe_to_biguint_canonical(x: &F) -> BigUint {
        let mut bytes = Vec::new();
        x.serialize_uncompressed(&mut bytes).unwrap();
        BigUint::from_bytes_le(&bytes)
    }

    pub fn find(&mut self, wire: Wire, cs: ConstraintSystemRef<F>) -> Result<LinearCombination<F>, SynthesisError> {

        let out_var: Variable = if let Some(&v) = self.variables.get(&wire) {
            v 
                                     
        } else {
            if self.flag{
                let value = self.wireValues.get(&wire).ok_or_else(|| {eprintln!("Missing value for wire {}", wire); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.variables.insert(wire, v);
                self.numNizkInputs += 1;
                v
            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.variables.insert(wire, v);
                self.numNizkInputs += 1;
                v
            }
           
        };

        if let Some(c) = self.wireUseCounters.get_mut(&wire) { 

            *c -= 1;
            if *c == 0
            {
                self.toClean.push(wire);
            }
        }


        let lc: LinearCombination<F> = if let Some(existing) = self.wireLinearCombinations.get(&wire) {
            existing.clone()
        } else {
            let new_lc: LinearCombination<F> = out_var.into(); 
            self.wireLinearCombinations.insert(wire, new_lc.clone());
            new_lc
        };
        

        Ok(self.wireLinearCombinations[&wire].clone())
    }

    pub fn clean(&mut self) {
        for w in self.toClean.drain(..) {
            self.wireLinearCombinations.remove(&w);
        }
    }

    
    pub fn handle_addition(&mut self, cs:ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        let output = output_ids[0];
        if self.variables.contains_key(&output) {
            eprintln!("ADD: output already defined");
            return Err(SynthesisError::Unsatisfiable);
        }

        let input_1: Wire = input_ids[0];
        let mut s: LinearCombination<F> = self.find(input_1, cs.clone())?;
        for &w in &input_ids[1..] {
            let l = self.find(w, cs.clone())?;
            s = s + l; 
        }
        
        self.wireLinearCombinations.insert(output, s);
        Ok(())
    }


    pub fn add_mul_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        
        let input_1 = input_ids[0];
        let input_2 = input_ids[1];
        let output = output_ids[0];

        
        let l1: LinearCombination<F> = self.find(input_1, cs.clone())?;
        let l2: LinearCombination<F> = self.find(input_2, cs.clone())?;

        
        let out_var: Variable;
        if let Some(&v) = self.variables.get(&output) {
            out_var = v; 
        } else {

            if self.flag{
                let value = self.wireValues.get(&output).ok_or_else(|| {eprintln!("Missing value for wire {}", output); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }  
        }
        cs.enforce_constraint(l1, l2, out_var.into())?;

        Ok(())
    }

    pub fn add_xor_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        
        
        let input_1 = input_ids[0];
        let input_2 = input_ids[1];
        let output = output_ids[0];

        
        let l1: LinearCombination<F> = self.find(input_1, cs.clone())?;
        let l2: LinearCombination<F> = self.find(input_2, cs.clone())?;

        let two: F = F::one() + F::one(); 

        let out_var: Variable;
        if let Some(&v) = self.variables.get(&output) {
            out_var = v; 
        } else {

            if self.flag{
                let value = self.wireValues.get(&output).ok_or_else(|| {eprintln!("Missing value for wire {}", output); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }
        }

        let first = l1.clone()*two;
        let second = l2.clone();
        let last = l1.clone() + l2.clone() - (lc!() + out_var);
        
        cs.enforce_constraint(first,second,last)?;

        Ok(())
    }

    pub fn add_or_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        
        
        let input_1 = input_ids[0];
        let input_2 = input_ids[1];
        let output = output_ids[0];

        
        let l1: LinearCombination<F> = self.find(input_1, cs.clone())?;
        let l2: LinearCombination<F> = self.find(input_2, cs.clone())?;

        let out_var: Variable;
        if let Some(&v) = self.variables.get(&output) {
            out_var = v; 
        } else {
            if self.flag{
                let value = self.wireValues.get(&output).ok_or_else(|| {eprintln!("Missing value for wire {}", output); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.numNizkInputs += 1;
                self.variables.insert(output, v);
                out_var = v;
            }
        }

        let first = l1.clone();
        let second = l2.clone();
        let last = l1.clone() + l2.clone() - (lc!() + out_var);
        
        cs.enforce_constraint(first,second,last)?;

        Ok(())
    }

    pub fn add_assert_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        
        
        let input_1 = input_ids[0];
        let input_2 = input_ids[1];
        let output = output_ids[0];

        
        let l1: LinearCombination<F> = self.find(input_1, cs.clone())?;
        let l2: LinearCombination<F> = self.find(input_2, cs.clone())?;
        let l3: LinearCombination<F> = self.find(output, cs.clone())?;

        
        cs.enforce_constraint(l1,l2,l3)?;

        Ok(())
    }


    pub fn add_zerop_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {

        let input      = input_ids[0];
        let output_1  = output_ids[0];
        let output_2   = output_ids[1];

        let lc_input: LinearCombination<F> = self.find(input, cs.clone())?;

        let vprt: Variable;
        let out_aux_var: Variable;


        //Using the same logic as explained before (while giving in advance the value to output_1)
        if let Some(&v) = self.variables.get(&output_1) {
            out_aux_var = v;

        } 
        else {
            if self.flag{
                let value = self.wireValues.get(&output_1).ok_or_else(|| {eprintln!("Missing value for wire {}", output_1); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.numNizkInputs += 1;
                self.variables.insert(output_1, v);
                out_aux_var = v;
              

            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.variables.insert(output_1, v);
                self.numNizkInputs += 1;
                out_aux_var = v;

            }
        }

        if let Some(&v) = self.variables.get(&output_2) {
            vprt = v; 

        } 
        else {
            if self.flag{
                let value = self.wireValues.get(&output_2).ok_or_else(|| {eprintln!("Missing value for wire {}", output_2); SynthesisError::Unsatisfiable})?;
                let v = cs.new_witness_variable(|| Ok(*value))?;
                self.numNizkInputs += 1;
                self.variables.insert(output_2, v);
                vprt = v;
              

            }
            else{
                let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.numNizkInputs += 1;
                self.variables.insert(output_2, v);
                vprt = v;

            }
        }

        
        
        let one_minus_out = lc!() + (F::one(), Variable::One) - vprt;
        
        cs.enforce_constraint(lc_input.clone(), one_minus_out, lc!())?;
        cs.enforce_constraint(lc_input.clone(), lc!() + out_aux_var, lc!() + vprt)?;

        Ok(())
    } 


    pub fn add_split_constraint(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
       
    
        let in_w: Wire = input_ids[0];
        let input_lc: LinearCombination<F> = self.find(in_w, cs.clone())?;

        
        let mut sum: LinearCombination<F> = lc!(); 
        let mut two_i: F = F::one();               // 2^0 = 1 -> si parte da 2^0 e si somma a sè stesso per raddoppiare ad ogni iterazione per ogni bit
        let one_lc: LinearCombination<F> = Variable::One.into();

        for bit_w in output_ids {
            
            let bit_var: Variable;
            
            if let Some(&v) = self.variables.get(&bit_w) {
                bit_var = v;
            } 
            else {
                if self.flag{
                    let value = self.wireValues.get(&bit_w).ok_or_else(|| {eprintln!("Missing value for wire {}", bit_w); SynthesisError::Unsatisfiable})?;
                    let v = cs.new_witness_variable(|| Ok(*value))?;
                    self.numNizkInputs += 1;
                    self.variables.insert(bit_w, v);
                    bit_var = v
                }
                else{
                    let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                    self.numNizkInputs += 1;
                    self.variables.insert(bit_w, v);
                    bit_var = v
                }

            };
            cs.enforce_constraint(lc!() + bit_var, lc!() + bit_var - one_lc.clone(), lc!())?;

            
            let term = LinearCombination::from(bit_var)*two_i;

            sum = sum + term;

            
            two_i = two_i + two_i;
        }
        cs.enforce_constraint(input_lc, one_lc, sum)?;
        Ok(())
    }


    pub fn handle_pack(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>) -> Result<(), SynthesisError> {
        
        let output = output_ids[0];
        let input_1 = input_ids[0];
        if self.variables.contains_key(&output) {
            eprintln!("Output already defined for pack operation");
            return Err(SynthesisError::Unsatisfiable);
        }
        

        let mut two_i: F = F::one();

        let mut sum: LinearCombination<F> = self.find(input_1, cs.clone())?;
      

        for &bit_w in &input_ids[1..] {

            let l = self.find(bit_w, cs.clone())?;
            
            two_i += two_i;
            sum = sum + l*two_i;   

        }
        
        self.wireLinearCombinations.insert(output, sum);
        
        Ok(())
    }

    pub fn handle_mul(&mut self,cs:ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>, constant: F) -> Result<(), SynthesisError> {

        let output = output_ids[0];
        let input = input_ids[0];
        if self.variables.contains_key(&output) {
            eprintln!("Output already defined for multiplication operation");
            return Err(SynthesisError::Unsatisfiable);
        }

        

        let lc: LinearCombination<F> = self.find(input, cs.clone())?;

        let lc_final = lc*constant;

        self.wireLinearCombinations.insert(output, lc_final);
        Ok(())
    }

    pub fn handle_mul_neg(&mut self, cs: ConstraintSystemRef<F>, input_ids: Vec<Wire>, output_ids: Vec<Wire>, constant: F) -> Result<(), SynthesisError> {
        
        let output = output_ids[0];
        let input = input_ids[0];
        if self.variables.contains_key(&output) {
            eprintln!("Output already defined for multiplication operation");
            return Err(SynthesisError::Unsatisfiable);
            
        }

        let lc: LinearCombination<F> = self.find(input,cs.clone())?;

        let lc_final = lc*constant;

        self.wireLinearCombinations.insert(output, lc_final);
        Ok(())
    }
    
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Parser<F> {

    fn generate_constraints(mut self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        
        self.parsing()?;

        for &w in &self.inputWireIds {
            if !self.variables.contains_key(&w) {
                if self.flag{
                let value = self.wireValues.get(&w).ok_or_else(|| {eprintln!("Missing value for wire {}", w); SynthesisError::Unsatisfiable})?;
                let v = cs.new_input_variable(|| Ok(*value))?;
                self.variables.insert(w, v);
                self.wireLinearCombinations
                    .insert(w, LinearCombination::from(v));
                }
                else{
                let v = cs.new_input_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.variables.insert(w, v);
                self.wireLinearCombinations
                    .insert(w, LinearCombination::from(v));
                }
            }
        }

    
        
        /*
        let n_fake_variables= (self.numInputs+self.numOutputs).next_power_of_two() - (self.numInputs+self.numOutputs);
        for _n in 1..n_fake_variables {
            cs.new_witness_variable(|| self.fake.ok_or(SynthesisError::AssignmentMissing))?;
        }

        self.numInputs += n_fake_variables;
 
        */
       
        

        

        for &w in &self.outputWireIds {
            if !self.variables.contains_key(&w) {
                if self.flag{
                let value = self.wireValues.get(&w).ok_or_else(|| {eprintln!("Missing value for wire {}", w); SynthesisError::Unsatisfiable})?;
                let v = cs.new_input_variable(|| Ok(*value))?;
                self.variables.insert(w, v);
                 self.wireLinearCombinations
                    .insert(w, LinearCombination::from(v));
                }
                else{
                let v = cs.new_input_variable(|| Err(SynthesisError::AssignmentMissing))?;
                self.variables.insert(w, v);
                self.wireLinearCombinations
                    .insert(w, LinearCombination::from(v));
                }
            }
        }


    

        for &w in &self.nizkWireIds {
           
            if !self.variables.contains_key(&w) {
                if self.flag{
                    let value = self.wireValues.get(&w).ok_or_else(|| {eprintln!("Missing value for wire {}", w); SynthesisError::Unsatisfiable})?;
                    let v = cs.new_witness_variable(|| Ok(*value))?;
                    self.variables.insert(w, v);
                    self.wireLinearCombinations
                        .insert(w, LinearCombination::from(v));
                }
                else{
                    let v = cs.new_witness_variable(|| Err(SynthesisError::AssignmentMissing))?;
                    self.variables.insert(w, v);
                    self.wireLinearCombinations
                        .insert(w, LinearCombination::from(v));
                }
            }
        }


        let reader = Self::open_reader(&self.path).map_err(|e| {
            eprintln!("FILE INESISTENTE");
            SynthesisError::Unsatisfiable
        })?;

        let lines = reader.lines().enumerate();
        
        for (i,line_t) in lines{

            let line = line_t.map_err(|e| { eprintln!("Error reading line {}", i); SynthesisError::Unsatisfiable })?;
            let line = line.trim();

            if!(line.starts_with("#") || line.starts_with("total ") || line.starts_with("input ") || line.starts_with("nizkinput ") || line.starts_with("output") || line.is_empty()){


                let (op, after_op) = line.split_once(" in ").ok_or_else(|| { eprintln!("Missing *IN* for operation, line {}", i); SynthesisError::Unsatisfiable })?; 
                let (in_blk, after_inputs) = after_op.split_once(" out ").ok_or_else(|| { eprintln!("Missing *OUT* for operation, line {}", i); SynthesisError::Unsatisfiable })?; 

                let input_str = in_blk
                    .split_once('<')
                    .and_then(|(_, r)| r.split_once('>'))
                    .map(|(ids, _)| ids)
                    .unwrap_or("");

                let output_str = after_inputs
                    .split_once('<')
                    .and_then(|(_, r)| r.split_once('>'))
                    .map(|(ids, _)| ids)
                    .unwrap_or("");

            

                let input_ids: Vec<Wire> = input_str
                .split_whitespace()
                .map(|t| t.parse().map_err(|_| SynthesisError::Unsatisfiable))
                .collect::<Result<_, _>>()?;

                let output_ids: Vec<Wire> = output_str
                .split_whitespace()
                .map(|t| t.parse().map_err(|_| SynthesisError::Unsatisfiable))
                .collect::<Result<_, _>>()?;

                    
                if op == "add"{
                    if output_ids.len() != 1{

                        eprintln!("Wrong ADD format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let _ = self.handle_addition(cs.clone(),input_ids, output_ids);
                }
                else if op == "mul"{
                    if output_ids.len() != 1 || input_ids.len() != 2 {
                        eprintln!("Wrong MUL format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let _ = self.add_mul_constraint(cs.clone(),input_ids,output_ids);
                }
                else if op == "xor"{
                    if output_ids.len() != 1 || input_ids.len() != 2 {
                        eprintln!("Wrong XOR format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let _ = self.add_xor_constraint(cs.clone(),input_ids,output_ids);

                }
                else if op == "or"{
                    if output_ids.len() != 1 || input_ids.len() != 2 {
                        eprintln!("Wrong OR format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let _ = self.add_or_constraint(cs.clone(),input_ids,output_ids);

                }
                else if op == "assert"{

                    if output_ids.len() != 1 || input_ids.len() != 2 {
                        eprintln!("Wrong ASSERT format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                   
                    let _ = self.add_assert_constraint(cs.clone(),input_ids,output_ids);

                }
                
                else if op == "zerop"{

                    if output_ids.len() != 2 || input_ids.len() != 1 {
                        eprintln!("Wrong ZEROP format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }

                    let _ = self.add_zerop_constraint(cs.clone(),input_ids,output_ids);
                    

                }
                else if op == "split"{

                    if input_ids.len() != 1 {
                        eprintln!("Wrong SPLIT format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                   
                    let _ = self.add_split_constraint(cs.clone(),input_ids,output_ids);


                }
                else if op == "pack"{

                    if output_ids.len() != 1 {
                        eprintln!("Wrong PACK format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let _ = self.handle_pack(cs.clone(),input_ids,output_ids);

                }
                
                else if let Some(hexstr) = op.strip_prefix("const-mul-neg-"){

                    if output_ids.len() != 1 || input_ids.len() != 1 {
                        eprintln!("Wrong CONST MUL format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                    
                    let big = BigUint::parse_bytes(hexstr.trim().as_bytes(),16)
                        .ok_or_else(|| {eprintln!("Wrong HEX format"); SynthesisError::Unsatisfiable})?;
                    let mut constant = F::from_be_bytes_mod_order(&big.to_bytes_be());
                    let constant = -constant;
                    let _ = self.handle_mul(cs.clone(),input_ids,output_ids, constant); 

                }
                else if let Some(hexstr) = op.strip_prefix("const-mul-"){

                    if output_ids.len() != 1 || input_ids.len() != 1 {
                        eprintln!("Wrong CONST MUL format, line: {}", i);
                        return Err(SynthesisError::Unsatisfiable);
                    }
                   
                    let big = BigUint::parse_bytes(hexstr.trim().as_bytes(),16)
                        .ok_or_else(|| {eprintln!("Wrong HEX format"); SynthesisError::Unsatisfiable})?;
                    let constant = F::from_be_bytes_mod_order(&big.to_bytes_be());
                    let _ = self.handle_mul(cs.clone(),input_ids,output_ids, constant); 
                    


                }
                else {
                    eprintln!("Parsing failed");
                    return Err(SynthesisError::Unsatisfiable);
                }
                


            }

            self.clean();

        }

        
        eprintln!("Number of NIZK inputs before padding: {}", self.numNizkInputs);
        eprintln!("Num of variables in cs: {}", cs.num_witness_variables());
        //eprintln!("MA RIESCI A STAMPARE QUALCOSA?");
        let mut n_fake_position = self.obtain_num_var_to_pad(cs.clone());
        let n_fake_variables= (self.numInputs + self.numOutputs + self.numNizkInputs).next_power_of_two() - (self.numInputs + self.numOutputs + self.numNizkInputs + 1);
        let needed = cs.num_constraints().next_power_of_two() - cs.num_constraints();
        n_fake_position = n_fake_position.next_power_of_two() - n_fake_position;

        eprintln!("n_fake position needed: {:?}", n_fake_position);
        eprintln!("n_fake variables needed: {:?}", n_fake_variables);
        eprintln!("n_fake constraints needed: {:?}", needed);
        
        //let total = needed * n_fake_variables;
        let added_constraints = if n_fake_variables == 0 {
            0
        } else {
            // ceiling division: (a + b - 1) / b
            (n_fake_position + n_fake_variables - 1) / n_fake_variables
        };

        let mut to_add = 0;
        let mut last_execution = 0;
        
        if n_fake_position > n_fake_variables{
            to_add = n_fake_variables;
            last_execution = n_fake_position - (added_constraints -1)* n_fake_variables;
        }
        else{
            to_add = n_fake_position;
        }

        eprintln!("to_add = {}", to_add);
        eprintln!("added_constraints = {}", added_constraints);

        let mut fake_lc_a: LinearCombination<F> = lc!();
        let mut fake_lc_b: LinearCombination<F> = lc!();
        let mut last_fake_lc_a: LinearCombination<F> = lc!();
        let mut last_fake_lc_b: LinearCombination<F> = lc!();
        
        let mut flag = true;
        //let mut value_c = F::one();
        for i in 0..to_add{
            
            let fake_variable_one = cs.new_witness_variable(|| Ok(F::one()))?;
            if i < last_execution{
                last_fake_lc_a = last_fake_lc_a + fake_variable_one;
            }
            self.numNizkInputs += 1;
            fake_lc_a = fake_lc_a + fake_variable_one;
            if flag{
                fake_lc_b = fake_lc_b + fake_variable_one;
                last_fake_lc_b = last_fake_lc_b + fake_variable_one;
                flag = false;
            }     

        }
        eprintln!("COMPUTATE LE FAKE lc_a e lc_b");
        
        let fake_lc_c = fake_lc_a.clone();
            
        
        
        for _ in 1..added_constraints{
            cs.enforce_constraint(fake_lc_a.clone(), fake_lc_b.clone(), fake_lc_c.clone())?;
        }

        let last_fake_lc_c = last_fake_lc_a.clone();
        cs.enforce_constraint(last_fake_lc_a.clone(), last_fake_lc_b.clone(), last_fake_lc_c.clone())?;

        eprintln!("AGGIUNTI I VINCOLI FAKE");

        //let fake_variable_one = cs.new_witness_variable(|| Ok(F::one()))?;
        /*
        self.numNizkInputs += 1;

        for _ in 0..n_fake_constraints{
            cs.enforce_constraint(lc!() + fake_variable_one, lc!() + fake_variable_one, lc!() + fake_variable_one)?;
        }
        */
        //eprintln!("Numero di variabili fake da aggiungere: {}", n_fake_variables);
        //let n_fake_variables = n_fake_variables.next_power_of_two() - (self.numInputs + self.numOutputs + self.numNizkInputs + 1);
        //let fake_variable: Variable = cs.new_witness_variable(|| self.fake.ok_or(SynthesisError::AssignmentMissing))?;
        let n_fake_variables= (self.numInputs + self.numOutputs + self.numNizkInputs).next_power_of_two() - (self.numInputs + self.numOutputs + self.numNizkInputs + 1);
        for n in 0..n_fake_variables{
            cs.new_witness_variable(|| self.fake.ok_or(SynthesisError::AssignmentMissing))?;
            
        }
        self.numNizkInputs += n_fake_variables;
        /*
        let threshold = self.obtain_num_var_to_pad(cs.clone());
        let mut added_var = 0;
        if self.numNizkInputs < threshold{
            added_var = threshold - (self.numNizkInputs + self.numOutputs + self.numInputs + 1);
            for _ in 0..added_var{
                cs.new_witness_variable(|| self.fake.ok_or(SynthesisError::AssignmentMissing))?;
            }
        }
        self.numNizkInputs += added_var;
        //eprintln!("numNizKInputs = {}", self.numNizkInputs);
        //eprintln!("num Real NizkInputs = {}", cs.num_witness_variables());
        
        //num_var_log = ark_std::log2(num_var_log) as usize;

        
        
        let num_var = (self.numInputs + self.numOutputs + self.numNizkInputs).next_power_of_two();

        let num_constraints = cs.num_constraints();
        let mut needed = 0;
        
        if num_constraints < num_var{
            needed = num_var - num_constraints;
           
        }
        else{
            needed = num_constraints.next_power_of_two() - num_constraints;
        }
        */
        
        let needed = cs.num_constraints().next_power_of_two() - cs.num_constraints();
        for _ in 0..needed {
            cs.enforce_constraint(lc!(), lc!(), lc!())?;
        }

        eprintln!("Circuit constructed with success");
        eprintln!("Public input variables: {}", cs.num_instance_variables());
        eprintln!("Private witness variables: {}", cs.num_witness_variables());
        eprintln!("Total constraints: {}", cs.num_constraints());

        Ok(())
    }
}
