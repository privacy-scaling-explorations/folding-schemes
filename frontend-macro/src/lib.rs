use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(Flatten)]
pub fn derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let iden = &ast.ident;
    let cs_iden_name = format!("{}Constraint", iden);
    let cs_iden = syn::Ident::new(&cs_iden_name, iden.span());

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let fields = if let syn::Data::Struct(syn::DataStruct {
        fields: syn::Fields::Named(syn::FieldsNamed { ref named, .. }),
        ..
    }) = ast.data
    {
        named
    } else {
        unimplemented!();
    };

    let cs_fields_to_vec = fields.iter().map(|f| {
        let name = &f.ident;
        quote! { value.#name }
    });

    let cs_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {pub #name: ark_r1cs_std::fields::fp::FpVar<F> }
    });

    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! { value.#name }
    });

    let cs_vec_to_fields = fields.iter().enumerate().map(|(id, f)| {
        let name = &f.ident;
        quote! {#name: vec[#id].clone()}
    });

    let vec_to_fields = fields.iter().enumerate().map(|(id, f)| {
        let name = &f.ident;
        quote! {#name: vec[#id]}
    });

    let state_number = fields.len();

    let state_macro = quote! {
        impl #impl_generics #iden #ty_generics #where_clause {
            pub fn state_number() -> usize {
                #state_number
            }
        }

        impl #impl_generics From<#iden #ty_generics> for Vec #ty_generics #where_clause {
            fn from(value: #iden #ty_generics) -> Vec #ty_generics {
                vec![#(#builder_fields,)*]
            }
        }

        impl #impl_generics From<Vec #ty_generics> for #iden #ty_generics {
            fn from(vec: Vec #ty_generics) -> #iden #ty_generics {
                assert!(vec.len() == #iden::#ty_generics::state_number());
                #iden {
                    #(#vec_to_fields,)*
                }
            }
        }
    };

    let constraint_macro = quote! {
        pub struct #cs_iden<F: ark_ff::PrimeField> {
            #(#cs_fields,)*
        }


        impl<F: PrimeField> From<Vec<ark_r1cs_std::fields::fp::FpVar<F>>> for #cs_iden<F> {
            fn from(vec: Vec<ark_r1cs_std::fields::fp::FpVar<F>>) -> #cs_iden<F>{
                #cs_iden {
                    #(#cs_vec_to_fields,)*
                }
            }
        }

        impl<F: PrimeField> From<#cs_iden<F>> for Vec<ark_r1cs_std::fields::fp::FpVar<F>> {
            fn from(value: #cs_iden<F>) -> Vec<ark_r1cs_std::fields::fp::FpVar<F>> {
                vec![#(#cs_fields_to_vec,)*]
            }
        }


        impl<F: ark_ff::PrimeField> #iden<F>{
            pub fn cs_state(v: Vec< ark_r1cs_std::fields::fp::FpVar<F>>) -> #cs_iden<F> {
                #cs_iden::from(v)
            }
        }
    };

    let expanded = quote! {
        #state_macro

        #constraint_macro
    };

    expanded.into()
}
