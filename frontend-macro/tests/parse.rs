use ark_bn254::Fr;
use ark_ff::PrimeField;
use frontend_macro::Flatten;
#[derive(Flatten, Debug)]
struct State<F: PrimeField> {
    a: F,
    b: F,
}

fn main() {
    let s = State::<Fr> {
        a: Fr::from(1u32),
        b: Fr::from(1u32),
    };

    let v: Vec<Fr> = Vec::from(s);

    println!("{:?}", State::<Fr>::state_number());
    println!("{:?}", v);
    println!("{:?}", State::from(v));
}
