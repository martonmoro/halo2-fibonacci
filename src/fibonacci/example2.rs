/*
Single column fibonacci circuit
This leads to faster proof generation
*/

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
    // In this example we are using only one column in order to try to avoid permutation checks
    pub advice: Column<Advice>,
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
        advice: Column<Advice>,
        instance: Column<Instance>
    ) -> FiboConfig {
        // We pass them in because they can be shared accross different configs
        // In this example we only have one advice column
        let selector = meta.selector();

        // Enable the ability to enforce equality over cells in this column
        // enabling equality has some cost so we only want to enable it when neccessary
        // We still need to enable equality on the advice column because 
        // we want to check that the first and last elements are the same as in the instance column
        meta.enable_equality(advice);
        meta.enable_equality(instance);

        // Defining a create_gate here applies it over every single column in the circuit.
        // We will use the selector column to decide when to turn this gate on and off, since we probably don't want it on every row
        meta.create_gate("add", |meta| {
            //
            // col_a | selector
            //   a   |    s
            //   b   |    
            //   c   |    
            let s = meta.query_selector(selector);
            // In this example all of the checks are from the same column but from three different rows frollowing each other
            let a = meta.query_advice(advice, Rotation::cur()); // curr means we are using the field from the same row as the selector 
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));
            // return the constraint
            // there can be multiple constraints
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

    // In this example we cannot assign row-by-row so we are assigning the entire table in one function
    fn assign(
        &self, 
        mut layouter: impl Layouter<F>, 
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error>{
        layouter.assign_region(
            || "entire fibonacci table", 
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice,
                    0
                )?;

                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice,
                    1
                )?;

                for row in 2..nrows {
                    if row < nrows - 2 {
                        self.config.selector.enable(&mut region, row)?;
                    }
                    let c_val = a_cell.value().and_then(
                        |a| {
                            b_cell.value().map(|b| *a + *b)
                        }
                    );

                    let c_cell = region.assign_advice(
                        || "advice", 
                        self.config.advice, 
                        row, 
                        || c_val.ok_or(Error::Synthesis)
                    )?;

                    a_cell = b_cell;
                    b_cell = c_cell;
                }

               Ok(b_cell)
            })
    }


    pub fn expose_public(
        &self, 
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,         // Absolute index inside the instance column
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
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
        let advice = meta.advice_column();
        let instance = meta.instance_column();
        FiboChip::configure(meta, advice, instance)
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // Will call all of the copy constraints
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let out_cell = chip.assign(
            layouter.namespace(|| "entire table"),
            10
        )?;

        chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

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