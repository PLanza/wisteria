mod error;
mod lexer;
mod parse;

use crate::parse::LexParser;

use quote::quote;

use syn::parse_macro_input;

#[proc_macro]
pub fn attach_lex_file(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // TODO: Prevent multiple calls to the macro
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

    let tok_name_strs: Vec<_> = token_names.iter().map(|id| id.to_string()).collect();

    quote! {
        #[derive(Clone, Copy, Eq, PartialEq, Debug)]
        pub enum LexTokenTag {
            _SKIP,
            #(#token_names),*
        }

        #[derive(PartialEq, Clone, Debug)]
        pub enum LexTokenValue {
            None,
            #(#ty_variants(#tys)),*
        }

        #[derive(PartialEq, Clone, Debug)]
        pub struct LexToken {
            kind: LexTokenTag,
            val: LexTokenValue,
        }

        impl std::fmt::Display for LexToken {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let kind_str = match self.kind {
                    LexTokenTag::_SKIP => "",
                    #(LexTokenTag::#token_names => #tok_name_strs),*
                };
                match &self.val {
                    LexTokenValue::None => write!(f, "{}", kind_str),
                    #(LexTokenValue::#ty_variants(val) => write!(f, "{}({:?})", kind_str, val)),*
                }
            }
        }
    }
    .into()
}
