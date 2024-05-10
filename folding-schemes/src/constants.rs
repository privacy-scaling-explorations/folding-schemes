// used for the RO challenges.
// From [Srinath Setty](https://microsoft.com/en-us/research/people/srinath/): In Nova, soundness
// error ≤ 2/|S|, where S is the subset of the field F from which the challenges are drawn. In this
// case, we keep the size of S close to 2^128.
pub const NOVA_N_BITS_RO: usize = 128;
