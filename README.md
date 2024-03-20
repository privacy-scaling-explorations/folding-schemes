# folding-schemes
(brief description) .. implemented on [arkworks](https://github.com/arkworks-rs).

> **Warning**: experimental code, do not use in production.
> The code has not been audited, and we have pending to implement several optimizations. The focus so far has been on implementing from scratch Nova + CycleFold and achieving onchain (EVM) verification.

## Schemes implemented
- [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370.pdf), Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla. 2021
- [CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192.pdf), Abhiram Kothapalli, Srinath Setty. 2023

Work in progress:

- [HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106.pdf), Liam Eagen, Ariel Gabizon. 2023

### Available frontends
Available frontends to define the folded circuit.

- [arkworks](https://github.com/arkworks-rs), arkworks contributors
- [Circom](https://github.com/iden3/circom), iden3, 0Kims Association

## Usage

### Folding Schemes introduction
[introductory text here]

- https://youtu.be/IzLTpKWt-yg?t=6367 , where [Carlos Pérez](https://twitter.com/CPerezz19) overviews the features of folding schemes and what can be build with them.

### Overview
Suppose that the user inputs a circuit that follows the IVC structure, chooses which Folding Scheme to use (eg. Nova), and which Decider (eg. Spartan over Pasta curve).

Later the user can for example change with few code changes the Folding Scheme being used (eg. switch to ProtoGalaxy) and also the Decider (eg. Groth16 over bn254), so the final proof can be verified in an Ethereum smart contract.

![](folding-schemes-lib-pipeline.png)

Complete examples can be found at [folding-schemes/examples](https://github.com/privacy-scaling-explorations/folding-schemes/tree/main/folding-schemes/examples)

### The folding circuit
For the next example, we're going to use Nova+CycleFold for the folding, with the On-chain (EVM) verifier.

The following image provides a description of the main Nova circuit and CycleFold circuit over a couple of steps.

![](cyclefold-nova-diagram.png)

### Define the circuit to be folded
First let's define our circuit to be folded:

```rust
/// This is the circuit that we want to fold, it implements the FCircuit trait
#[derive(Clone, Copy, Debug)]
pub struct Sha256FCircuit<F: PrimeField> {
    _f: PhantomData<F>,
}
impl<F: PrimeField> FCircuit<F> for Sha256FCircuit<F> {
    type Params = ();
    fn new(_params: Self::Params) -> Self {
        Self { _f: PhantomData }
    }
    fn state_len(&self) -> usize {
        1
    }
    /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
    /// z_{i+1}
    fn step_native(&self, _i: usize, z_i: Vec<F>) -> Result<Vec<F>, Error> {
        let out_bytes = Sha256::evaluate(&(), z_i[0].into_bigint().to_bytes_le()).unwrap();
        let out: Vec<F> = out_bytes.to_field_elements().unwrap();
        Ok(vec![out[0]])
    }
    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        &self,
        _cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let unit_var = UnitVar::default();
        let out_bytes = Sha256Gadget::evaluate(&unit_var, &z_i[0].to_bytes()?)?;
        let out = out_bytes.0.to_constraint_field()?;
        Ok(vec![out[0].clone()])
    }
}
```

We can also define the circuit in Circom:
```circom
//
```

### Folding the circuit
Now we plug it into the library:
```rust
// The idea here is that eventually we could replace the next line chunk that defines the
// `type NOVA = Nova<...>` by using another folding scheme that fulfills the `FoldingScheme`
// trait, and the rest of our code would be working without needing to be updated.
type NOVA = Nova<
    Projective,
    GVar,
    Projective2,
    GVar2,
    Sha256FCircuit<Fr>,
    KZG<'static, Bn254>,
    Pedersen<Projective2>,
>;

let num_steps = 10;
let initial_state = vec![Fr::from(1_u32)];

let F_circuit = Sha256FCircuit::<Fr>::new(());

println!("Prepare Nova ProverParams & VerifierParams");
let (prover_params, verifier_params) = nova_setup::<Sha256FCircuit<Fr>>(F_circuit);

println!("Initialize FoldingScheme");
let mut folding_scheme = NOVA::init(&prover_params, F_circuit, initial_state.clone()).unwrap();

// compute a step of the IVC
for i in 0..num_steps {
    let start = Instant::now();
    folding_scheme.prove_step().unwrap();
    println!("Nova::prove_step {}: {:?}", i, start.elapsed());
}

let (running_instance, incomming_instance, cyclefold_instance) = folding_scheme.instances();

println!("Run the Nova's IVC verifier");
NOVA::verify(
    verifier_params,
    initial_state,
    folding_scheme.state(), // latest state
    Fr::from(num_steps as u32),
    running_instance,
    incomming_instance,
    cyclefold_instance,
)
.unwrap();
```

### Final proof (decider proof)
Two options:

- offchain mode
- onchain (Ethereum's EVM) mode

Once we have been folding our circuit instances, we can generate the *"final proof"*, the Decider proof.


#### Offchain Decider

#### Onchain Decider

![](decider-onchain-flow-diagram.png)

Generating the final proof (decider), to be able to verify it in Ethereum's EVM:

```rust
type DECIDER = Decider<
    Projective,
    GVar,
    Projective2,
    GVar2,
    CubicFCircuit<Fr>,
    KZG<'static, Bn254>,
    Pedersen<Projective2>,
    Groth16<Bn254>, // here we define the Snark to use in the decider
    NOVA,           // here we define the FoldingScheme to use
>;

// generate Groth16 setup
let circuit = DeciderEthCircuit::<
    Projective,
    GVar,
    Projective2,
    GVar2,
    Pedersen<Projective>,
    Pedersen<Projective2>,
>::from_nova::<CubicFCircuit<Fr>>(nova.clone());
let mut rng = rand::rngs::OsRng;

let start = Instant::now();
let (pk, vk) =
    Groth16::<Bn254>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
println!("Groth16 setup, {:?}", start.elapsed());

// decider proof generation
let decider_pp = (poseidon_config.clone(), g16_pk, kzg_pk);
let proof = DECIDER::prove(decider_pp, rng, nova.clone()).unwrap();

// decider proof verification
let decider_vp = (poseidon_config, g16_vk, kzg_vk);
let verified = DECIDER::verify(decider_vp, nova.i, nova.z_0, nova.z_i, &nova.U_i, &nova.u_i, proof).unwrap();
assert!(verified);
```

As mentioned above, complete examples can be found at [folding-schemes/examples](https://github.com/privacy-scaling-explorations/folding-schemes/tree/main/folding-schemes/examples)

### Swapping curves and proving schemes
Thanks to the modularity of arkworks, we can swap between curves and proving systems.
Suppose that for the final proof (decider), instead of using Groth16 over the BN254 curve, we want to use Marlin+IPA over the Pasta curves, so we can enjoy of not needing a trusted setup.
It just requires few line changes on our previous code [...]

### On-chain verification
Having used the `DeciderEth` (see [Onchain Decider](#Onchain-Decider) section), we can now verify it in Ethereum's EVM.

First we need to generate the Solidity contracts that verify the Decider proofs. Use the [solidity-verifiers-cli](cli) tool
```
> solidity-verifier-cli -p nova-cyclefold -d ./folding-verifier-solidity/assets/G16_test_vk_data
```

## License
https://github.com/privacy-scaling-explorations/folding-schemes/blob/main/LICENSE

[TODO: add references to
- arkworks
- Espresso code regarding the multilinear 'virtual polynomial' and SumCheck used in HyperNova
- Solidity KZG & Groth16 original adapted code
    - Groth16: Jordi Baylina
    - KZG10: weijiekoh
    - Templating: Han
- People who helped us: Srinath Setty, Lev57, Matej (Lurk), Adrien (Lurk), TODO
]
