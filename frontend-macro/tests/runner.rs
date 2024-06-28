#[cfg(test)]
mod test {

    #[test]
    fn try_compile() {
        let t = trybuild::TestCases::new();
        t.pass("tests/parse.rs");
    }

    #[test]
    fn try_run_test() {
        use ark_bn254::Fr;
        use ark_ff::PrimeField;
        use frontend_macro::Flatten;
        #[derive(Flatten, Debug, PartialEq, Clone)]
        struct State<F: PrimeField> {
            a: F,
            b: F,
        }

        let s = State::<Fr> {
            a: Fr::from(1u32),
            b: Fr::from(1u32),
        };

        let v: Vec<Fr> = Vec::from(s.clone());

        assert_eq!(2, State::<Fr>::state_number());
        assert_eq!(vec![s.a, s.b], v);
        assert_eq!(s, State::from(v));
    }
}
