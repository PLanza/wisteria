mod backus;
mod error;
mod parse;

use quote::quote;
use syn::parse_macro_input;

#[proc_macro]
pub fn attach_parse_file(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let path = parse_macro_input!(input as syn::LitStr);
    quote!().into()
}
