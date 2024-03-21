{{ groth16_verifier }}

{{ kzg10_verifier }}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying Nova IVC SNARK proofs.
 * @dev     This is an askama template. It will feature a snarkjs groth16 and a kzg10 verifier, from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {
    function verifyProof(
        // IVC values
        uint256 i,
        uint256 z_0, // initial state
        uint256 z_i, // last state
        uint256[2] calldata U_i_cmW,
        uint256[2] calldata U_i_cmE,
        uint256 U_i_u,
        uint256[1] calldata U_i_x,
        uint256[2] calldata u_i_cmW,
        uint256[2] calldata u_i_cmE,
        uint256 u_i_u,
        uint256[1] calldata u_i_x,
        uint256[2] calldata cmT,
        uint256 r,

        // Groth16 proof
        uint[2] calldata pA,
        uint[2][2] calldata pB,
        uint[2] calldata pC,

        // KZG proof
        uint256 challenge_W,
        uint256 challenge_E,
        uint256[2][2] calldata kzg_proof, // 2 KZG proofs
        uint256[2] calldata kzg_evals // 2 KZG evals
    ) public view returns (bool) {

        // TODO compute r, or maybe compute it in-circuit and just get it here

        // NIFS.V
        uint256 u = (U_i_u + r * u_i_u) % BN254_SCALAR_FIELD;
        uint256 x = (U_i_x[0] + r * u_i_x[0]) % BN254_SCALAR_FIELD; // x is of length 1
        uint256[2] memory cmW = super.add(u_i_cmW, super.mulScalar(U_i_cmW, r));
        uint256[2] memory cmE = super.add(cmT, super.mulScalar(U_i_cmE, r));

        // TODO convert cmW.x,y & cmE.x,y & cmT.x,y into NonNative limbs (compatible with point_to_nonnative_limbs_custom_opt)
        // https://github.com/arkworks-rs/r1cs-std/tree/b477880a3b9c097b65b1e006d8116f3998cf013c/src/fields/nonnative/allocated_field_var.rs#L325
        // compute cmE_limbs, cmW_limbs, cmT_limbs

        // prepare public inputs
        uint256[110] memory public_inputs = [
            i,
            z_0,
            z_i,
            u,
            x,
            cmE_limbs[0],
            cmE_limbs[1],
            cmW_limbs[0],
            cmW_limbs[1],
            challenge_W,
            challenge_E,
            kzg_evals[0],
            kzg_evals[1],
            cmT_limbs[0],
            cmT_limbs[1],
            r
        ];
        
        // verify Groth16 proof
        bool success_g16 =  super.verifyProof(pA, pB, pC, public_inputs);
        require(success_g16 == true, "G16 Failed");

        // verify KZG proofs
        bool success_kzg_cmW = super.check(cmW, kzg_proof[0], challenge_W, kzg_evals[0]);
        require(success_kzg_cmW == true, "KZG of cmW Failed");

        bool success_kzg_cmE = super.check(cmE, kzg_proof[1], challenge_E, kzg_evals[1]);
        require(success_kzg_cmE == true, "KZG of cmE Failed");

        return(true);
    }   
}
