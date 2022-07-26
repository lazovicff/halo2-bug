use halo2wrong::{
    curves::pairing::{Engine, MultiMillerLoop},
    halo2::{
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Error, ProvingKey,
            VerifyingKey,
        },
        poly::{
            commitment::{CommitmentScheme, ParamsProver},
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::AccumulatorStrategy,
            },
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
};
use rand::Rng;
use std::{fmt::Debug, time::Instant};

fn main() {
    println!("Hello, world!");
}

/// Proving/verifying key generation.
pub fn keygen<E: MultiMillerLoop + Debug, C: Circuit<E::Scalar>>(
    params: &ParamsKZG<E>,
    circuit: &C,
) -> Result<ProvingKey<<E as Engine>::G1Affine>, Error> {
    let vk = keygen_vk::<KZGCommitmentScheme<E>, _>(params, circuit)?;
    let pk = keygen_pk::<KZGCommitmentScheme<E>, _>(params, vk, circuit)?;

    Ok(pk)
}

/// Generate parameters with polynomial degere = `k`.
pub fn generate_params<E: MultiMillerLoop + Debug>(k: u32) -> ParamsKZG<E> {
    ParamsKZG::<E>::new(k)
}

// Rust compiler can't infer the type, so we need to make a helper function
pub fn finalize_verify<
    'a,
    E: MultiMillerLoop + Debug,
    V: VerificationStrategy<'a, KZGCommitmentScheme<E>, VerifierSHPLONK<'a, E>>,
>(
    v: V,
) -> bool {
    v.finalize()
}

/// Make a proof for generic circuit.
pub fn prove<E: MultiMillerLoop + Debug, C: Circuit<E::Scalar>, R: Rng + Clone>(
    params: &ParamsKZG<E>,
    circuit: C,
    pub_inps: &[&[<KZGCommitmentScheme<E> as CommitmentScheme>::Scalar]],
    pk: &ProvingKey<E::G1Affine>,
    rng: &mut R,
) -> Result<Vec<u8>, Error> {
    let mut transcript = Blake2bWrite::<_, E::G1Affine, Challenge255<_>>::init(vec![]);
    create_proof::<KZGCommitmentScheme<E>, ProverSHPLONK<_>, _, _, _, _>(
        params,
        pk,
        &[circuit],
        &[pub_inps],
        rng.clone(),
        &mut transcript,
    )?;

    let proof = transcript.finalize();
    Ok(proof)
}

/// Verify a proof for generic circuit.
pub fn verify<E: MultiMillerLoop + Debug>(
    params: &ParamsKZG<E>,
    pub_inps: &[&[<KZGCommitmentScheme<E> as CommitmentScheme>::Scalar]],
    proof: &[u8],
    vk: &VerifyingKey<E::G1Affine>,
) -> Result<bool, Error> {
    let strategy = AccumulatorStrategy::<E>::new(params);
    let mut transcript = Blake2bRead::<_, E::G1Affine, Challenge255<_>>::init(proof);
    let output = verify_proof::<KZGCommitmentScheme<E>, _, _, VerifierSHPLONK<E>, _>(
        params,
        vk,
        strategy,
        &[pub_inps],
        &mut transcript,
    )?;

    Ok(finalize_verify(output))
}

/// Helper function for doing proof and verification at the same time.
pub fn prove_and_verify<E: MultiMillerLoop + Debug, C: Circuit<E::Scalar>, R: Rng + Clone>(
    params: ParamsKZG<E>,
    circuit: C,
    pub_inps: &[&[<KZGCommitmentScheme<E> as CommitmentScheme>::Scalar]],
    rng: &mut R,
) -> Result<bool, Error> {
    let pk = keygen(&params, &circuit)?;
    let start = Instant::now();
    let proof = prove(&params, circuit, pub_inps, &pk, rng)?;
    let end = start.elapsed();
    print!("Proving time: {:?}", end.as_secs());
    let res = verify(&params, pub_inps, &proof[..], pk.get_vk())?;

    Ok(res)
}

#[cfg(test)]
mod test {
    use halo2wrong::halo2::{
        arithmetic::FieldExt,
        circuit::{Layouter, Region},
        plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
    };

    use super::{generate_params, prove_and_verify};
    use halo2wrong::{
        curves::bn256::{Bn256, Fr},
        halo2::{
            circuit::{SimpleFloorPlanner, Value},
            dev::MockProver,
            plonk::{Circuit, Instance},
        },
    };

    #[derive(Clone)]
    struct TestConfig {
        a: Column<Advice>,
        fixed: Column<Fixed>,
        pub_ins: Column<Instance>,
    }

    #[derive(Clone)]
    struct TestCircuit<F: FieldExt> {
        a: Value<F>,
    }

    impl<F: FieldExt> TestCircuit<F> {
        fn new(a: F) -> Self {
            Self { a: Value::known(a) }
        }
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            self.clone()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> TestConfig {
            let a = meta.advice_column();
            let fixed = meta.fixed_column();
            let pub_ins = meta.instance_column();

            meta.enable_equality(a);
            // meta.enable_constant(fixed);
            meta.enable_equality(pub_ins);

            TestConfig { a, fixed, pub_ins }
        }

        fn synthesize(
            &self,
            config: TestConfig,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let res = layouter.assign_region(
                || "temp",
                |mut region: Region<'_, F>| {
                    let a = region.assign_advice(|| "temp", config.a, 0, || self.a)?;

                    let fix = region.assign_fixed(
                        || "temp",
                        config.fixed,
                        0,
                        || Value::known(F::from(1)),
                    )?;

                    let next = a.value().cloned() * fix.value().cloned();

                    let res = region.assign_advice(|| "temp", config.a, 1, || next)?;

                    Ok(res)
                },
            )?;

            layouter.constrain_instance(res.cell(), config.pub_ins, 0)?;
            Ok(())
        }
    }

    // THIS TEST WORKS FINE
    #[test]
    fn test_fixed() {
        let test_chip = TestCircuit::new(Fr::from(1));

        let k = 4;
        let pub_ins = vec![Fr::from(1)];
        let prover = MockProver::run(k, &test_chip, vec![pub_ins]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    // Error::Synthesis
    #[test]
    fn test_fixed_production() {
        let test_chip = TestCircuit::new(Fr::from(1));

        let k = 4;
        let rng = &mut rand::thread_rng();
        let params = generate_params(k);
        let res =
            prove_and_verify::<Bn256, _, _>(params, test_chip, &[&[Fr::from(1)]], rng).unwrap();
        assert!(res);
    }
}
