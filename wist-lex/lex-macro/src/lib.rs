mod error;
mod lexer;
mod parse;

use crate::parse::LexParser;

use quote::quote;

use syn::parse_macro_input;

#[proc_macro]
pub fn attach_lex_file(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let path = parse_macro_input!(input as syn::LitStr);

    let parser = LexParser::new(path.value()).unwrap();
    self::lexer::include_lexer(parser)
}

pub(crate) fn gen_token_enums(
    token_names: &Vec<syn::Ident>,
    token_ty_variants: &Vec<Option<syn::Ident>>,
    token_types: &Vec<Option<syn::Type>>,
) -> proc_macro::TokenStream {
    let (mut ty_variants, mut tys) = (Vec::new(), Vec::new());
    for (ty, ty_variant) in token_types.iter().zip(token_ty_variants) {
        match (ty, ty_variant) {
            (Some(ty), Some(ty_variant)) => {
                if !tys.contains(ty) {
                    tys.push(ty.clone());
                    ty_variants.push(ty_variant.clone());
                }
            }
            _ => (),
        }
    }

    quote! {
        #[derive(Clone, Copy, Eq, PartialEq, Debug)]
        pub enum LexTokenKind {
            _SKIP,
            #(#token_names),*
        }

        // Need to generate automatically
        #[derive(Clone, PartialEq, Debug)]
        pub enum LexTokenValue {
            None,
            #(#ty_variants(#tys)),*
        }

        #[derive(Clone, PartialEq, Debug)]
        pub struct LexToken {
            kind: LexTokenKind,
            val: LexTokenValue,
        }
    }
    .into()
}
