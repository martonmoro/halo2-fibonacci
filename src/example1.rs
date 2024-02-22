use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation
};

// Example
// Row | a0 | a1 | a2 | s | i
//  0  |  1 |  1 |  2 | 1 |
//  1  |  1 |  2 |  3 | 1 |
//  2  |  2 |  3 |  5 | 1 |
//  3  |  3 |  5 |  8 | 1 |
//  4  |  5 |  8 | 13 | 1 |
// ...

struct ACell<F: FieldExt>(AssignedCell<F, F>);

// Defines the configuration of the columns
// Advice columns hold the private inputs and other witnesses - vary over each proof
// Instance columns hold public inputs - vary over each proof
// Fixed columns hold constants and lookup tables - circuit configuration
// Selector columns hold control gates (binary constants) - circuit configuration
#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
    pub instance: Column<Instance>
}

// The chip struct configures the constraints in the circuit and provides assignment functions
struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FiboChip<F> {
    // Default constructor
    fn construct(config: FiboConfig) -> Self {
        Self { config, _marker: PhantomData}
    }

    // This function will create columns and define the custom gates and enable the permutation check
    // and return a config with all the gates 
    // There are two different kinds of selectors:
    //  - Selector - halo2 BE will apply optimizations to the selectors and combine them while preserving which gate gets turned on where
    //  - Complex Selector - used in lookup arguments, selector has to always be binary thus cannot apply selector combining optimizations
    fn configure(
        meta: &mut ConstraintSystem<F>, 
        advice: [Column<Advice>; 3], 
        instance: Column<Instance>
    ) -> FiboConfig {
        // We pass them in because they can be shared accross different configs
        let col_a = advice[0];
        let col_b = advice[1];
        let col_c = advice[2];
        let selector = meta.selector();

        // Enable the ability to enforce equality over cells in this column
        // enabling equality has some cost so we only want to enable it when neccessary
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        // Defining a create_gate here applies it over every single column in the circuit.
        // We will use the selector column to decide when to turn this gate on and off, since we probably don't want it on every row
        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur()); // curr means we are using the field from the same row as the selector 
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            // return the constraint
            // there can be multiple constraints
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice: [col_a, col_b, col_c],
            selector,
            instance,
        }
    }

    // These assign functions are to be called by the synthesizer, and will be used to assign values to the columns (the witness)
    // The layouter will collect all the region definitions and compress it vertically (i.e. squeeze up/down)
    // but not horizontally (i.e. will not squeeze left/right, at least right now)
    fn assign_first_row(&self, mut layouter: impl Layouter<F>, a: Option<F>, b: Option<F>) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error>{
        layouter.assign_region(
            || "first_row", 
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice(
                    || "a", 
                    self.config.advice[0], 
                    0, 
                    || a.ok_or(Error::Synthesis),
                ).map(ACell)?;

                let b_cell = region.assign_advice(
                    || "b", 
                    self.config.advice[1], 
                    0, 
                    || b.ok_or(Error::Synthesis),
                ).map(ACell)?;

                let c_val = a.and_then(|a| b.map(|b| a + b));

                let c_cell = region.assign_advice(
                    || "c", 
                    self.config.advice[2], 
                    0, 
                    || c_val.ok_or(Error::Synthesis),
                ).map(ACell)?;

               Ok((a_cell, b_cell, c_cell))
            })
    }

    // This will be repeatedly called. Note that each time it makes a new region, comprised of a, b, c, s that happen to all be in the same row
    fn assign_row(&self, mut layouter: impl Layouter<F>, prev_b: &ACell<F>, prev_c: &ACell<F>) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                // first we enable the selector
                self.config.selector.enable(&mut region, 0)?;

                // copy from previous assigned cells
                // copy to the current region
                // permutation check
                prev_b.0.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                prev_c.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

                let c_val = prev_b.0.value().and_then(
                    |b|  {
                        prev_c.0.value().map(|c| *b + *c)
                    }
                );
                
                let c_cell = region.assign_advice(
                    || "c", 
                    self.config.advice[2], 
                    0, 
                    || c_val.ok_or(Error::Synthesis)
                ).map(ACell)?;

                Ok(c_cell)
            }
        )
    }

    pub fn expose_public(
        &self, 
        mut layouter: impl Layouter<F>,
        cell: &ACell<F>,
        row: usize,         // Absolute index inside the instance column
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F> {
    pub a: Option<F>,
    pub b: Option<F>,
}

// Our circuit will instantiate an instance based on the interface defined on the chip and floorplanner (layouter)
// There isn't a clear reason this and the chip aren't the same thing, except for better abstractions for complex circuits
impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config =  FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // Has the arrangement of columns. Called only during keygen, and will just call chip config most of the time
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let instance = meta.instance_column();
        FiboChip::configure(meta, [col_a, col_b, col_c], instance)
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // Will call all of the copy constraints
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let (prev_a, mut prev_b, mut prev_c) = chip.assign_first_row(
            layouter.namespace(|| "first row"),
            self.a, self.b,
        )?;

        chip.expose_public(layouter.namespace(|| "private a"), &prev_a, 0)?;
        chip.expose_public(layouter.namespace(|| "private b"), &prev_b, 1)?;

        for _i in 3..10 {
            let c_cell = chip.assign_row(
                layouter.namespace(|| "next row"),
                &prev_b,
                &prev_c,
            )?;
            prev_b = prev_c;
            prev_c = c_cell; 
        }

        chip.expose_public(layouter.namespace(|| "output"), &prev_c, 2)?;

        Ok(())
    }
}

fn main() {
    // Circuit size 
    let k =4;

    let a =Fp::from(1);     // F[0]
    let b = Fp::from(1);    // F[1]
    let out = Fp::from(55); // F[9]

    let circuit = MyCircuit{
        a: Some(a),
        b: Some(b),
    };

    let public_input = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    prover.assert_satisfied();
}
