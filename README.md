# folding-schemes
(brief description)

> **Warning**: experimental code, do not use in production.

## Schemes implemented
- [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370.pdf), Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla. 2021
- [CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192.pdf), Abhiram Kothapalli, Srinath Setty. 2023

WIP:
- [HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106.pdf), Liam Eagen, Ariel Gabizon. 2023

### Frontends available
- [arkworks](https://github.com/arkworks-rs), arkworks contributors
- [Circom](https://github.com/iden3/circom), iden3, 0Kims Association

## Usage

### Overview
Suppose that the user inputs a circuit that follows the IVC structure, chooses which Folding Scheme to use (eg. Nova), and which Decider (eg. Spartan over Pasta curve).

Later the user can for example change with few code changes the Folding Scheme being used (eg. switch to ProtoGalaxy) and also the Decider (eg. Groth16 over bn254), so the final proof can be verified in an Ethereum smart contract.

![](https://hackmd.io/_uploads/H1r7z9I32.png)
*note: this diagram will be improved and done with some non-handwritten tool.*

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


## Development
Structure of the code:

[...]

In each of the implementations of the folding dir, there are mainly 3 blocks plus 'other':
- circuits
- folding/nifs/nimfs
- ivc/lib
- other


## License
https://github.com/privacy-scaling-explorations/folding-schemes/blob/main/LICENSE
