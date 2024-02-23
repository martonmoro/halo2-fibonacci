// This helper checks that the value witnessed in a given cell is  within a given range.
//
//
//         value   |   q_range_check
//  --------------------------------------
//           v     |          1

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt, 
    circuit::*, 
    plonk::*, poly::Rotation
};

#[derive(Debug, Clone)]

// First we create a config where we have one advice and one selector column and we need the PhantomData for F
struct RangeCheckConfig<F: FieldExt, const RANGE: usize> {
    value: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>
}

impl<F: FieldExt, const RANGE: usize> RangeCheckConfig<F, RANGE> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>, // It is best practice to pass in advice columns because advice columns are very often shared accross configs
    ) -> Self {
        // Toggles the range check constraint
        let q_range_check = meta.selector();

        let config = Self {
            q_range_check,
            value,
            _marker: PhantomData
        };

        // Range-check gate
        // For a value v and a range R, check that v < R
        //    v * (1 - v) * (2 - v) * ... * (R - 1 - v) = 0  
        // If v is any of these value then the product will be zero
        meta.create_gate("Range check", |meta|{
            // When queriyng a selector we don't specify the Rotation because it always queries at the current Rotation
            // Advice columns query relative to the selector's offset
            // query_selector gives us an expression for the selector
            let q_range_check = meta.query_selector(q_range_check); 
            let value = meta.query_advice(value, Rotation::cur());

            let range_check = |range: usize, value: Expression<F>| {
                assert!(range > 0);
                (1..range).fold(value.clone(), |expr, i| {
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone())
                })
            };

            Constraints::with_selector(q_range_check, [("range check", range_check(RANGE, value))])
        });

        config
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>, 
        value: Value<Assigned<F>>
    ) -> Result<(), Error> {
        layouter.assign_region(|| "Assign value", |mut region| {
            let offset = 0;
            // Enable q_range_check
            self.q_range_check.enable(&mut region, offset);

            // Assign given value
            region.assign_advice(|| "assign value", self.value, offset, || value)?;

            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: FieldExt, const RANGE: usize> {
        value: Value<Assigned<F>>,
    }

    impl<F: FieldExt, const RANGE: usize> Circuit<F> for MyCircuit<F, RANGE> {
        type Config = RangeCheckConfig<F, RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            RangeCheckConfig::configure(meta, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.assign(layouter.namespace(|| "Assign value"), self.value)?;

            Ok(())
        }
    }

    #[test]
    fn test_range_check_1() {
        let k = 4;
        const RANGE: usize = 8; // 3-bit value

        // Successful cases
        for i in 0..RANGE {
            let circuit = MyCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(i as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // Out-of-range value, v=8
        let circuit = MyCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from(RANGE as u64).into()),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        // Unit test expecting the faliure when the value is out of range
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "Range check").into(), 0, "range check").into(),
                location: FailureLocation::InRegion {
                    region: (0, "Assign value").into(),
                    offset: 0
                },
                cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x8".to_string())]
            }])
        );
    }
}