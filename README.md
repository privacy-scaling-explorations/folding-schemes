# folding-schemes
(brief description)

## Schemes implemented
- [Nova](https://eprint.iacr.org/2021/370.pdf): Recursive Zero-Knowledge Arguments from Folding Schemes + [CycleFold](https://eprint.iacr.org/2023/1192.pdf): Folding-scheme-based recursive arguments over a cycle of elliptic curves

WIP:
- [HyperNova](https://eprint.iacr.org/2023/573.pdf): Recursive arguments for customizable constraint systems
- [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf): Efficient ProtoStar-style folding of multiple instances

### Frontends available
- [arkworks](https://github.com/arkworks-rs)
- [Circom](https://github.com/iden3/circom)

## Usage

### Overview
Suppose that the user inputs a circuit that follows the IVC structure, chooses which Folding Scheme to use (eg. Nova), and which Decider (eg. Spartan over Pasta curve).

Later the user can for example change with few code changes the Folding Scheme being used (eg. switch to ProtoGalaxy) and also the Decider (eg. Groth16 over bn254), so the final proof can be verified in an Ethereum smart contract.

### Folding the circuit
First let's define our circuit to be folded:
```circom
//
```

Now we plug it into the library:
```rust
//
```

### Generating the final proof (decider), and verifying it in Ethereum

### Swapping curves and proving schemes
Additionally, let's suppose that for the final proof (decider), instead of using Groth16 over the BN254 curve, we want to use Marlin+IPA over the Pasta curves, so we can enjoy of not needing a trusted setup.
It just requires few line changes on our previous code [...]



## License
https://github.com/privacy-scaling-explorations/folding-schemes/blob/main/LICENSE
