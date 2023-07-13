mod parse;

use crate::parse::LexParser;

use quote::quote;

use syn::{parse_macro_input, parse_str};

#[proc_macro]
pub fn attach_lex_file(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let path = parse_macro_input!(input as syn::LitStr);

    let mut parser = LexParser::new(path.value()).unwrap();
    let token_enum = parser.parse_token_decs();
    parser.parse_regular_defs();
    parser.parse_match_rules();

    token_enum
}

pub(crate) fn gen_token_enum(
    token_names: Vec<String>,
    token_types: Vec<String>,
) -> proc_macro::TokenStream {
    let token_names: Vec<syn::Ident> = token_names
        .iter()
        .map(|name| parse_str(name).unwrap())
        .collect();

    let token_types: Vec<_> = token_types
        .iter()
        .map(|ty| convert_token_type(ty))
        .collect();

    quote! {
        pub enum LexToken {
            __SKIP, // Patterns that do not match any tokens
            #(#token_names #token_types),*
        }
    }
    .into()
}

fn convert_token_type(ty: &String) -> proc_macro2::TokenStream {
    if ty == "" {
        quote!()
    } else if ty == "int" {
        quote!((i32))
    } else if ty == "float" {
        quote!((f32))
    } else if ty == "bool" {
        quote!((bool))
    } else if ty == "string" {
        quote!((String))
    } else {
        // TODO: Handle Error
        panic!("Illegal type {}", ty);
    }
}
