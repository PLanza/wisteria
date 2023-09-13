use syn::parse::Parser;

#[proc_macro]
pub fn attach_wisteria_files(args: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro2::Span;
    let parse_error = syn::Error::new(
        Span::call_site(),
        "Pass the wisteria lex and parse file paths as string literals separated by a comma",
    );
    use syn::{punctuated::Punctuated, token::Comma, LitStr};
    let mut paths = match Punctuated::<LitStr, Comma>::parse_terminated.parse(args) {
        Ok(args) => args.into_iter(),
        Err(_) => return parse_error.to_compile_error().into(),
    };

    // TODO: Prevent multiple calls to the macro

    let missing_lex_file = syn::Error::new(Span::call_site(), "Missing lex file");
    let lex_parser = match paths.next() {
        Some(path) => lex_macro::LexParser::new(path.value()).unwrap(),
        None => return missing_lex_file.to_compile_error().into(),
    };
    let (token_type_map, mut lex_code) = lex_macro::lexer::include_lexer(lex_parser);

    let missing_parse_file = syn::Error::new(Span::call_site(), "Missing parse file");
    let grammar_parser = match paths.next() {
        Some(path) => parse_macro::GrammarParser::new(path.value(), token_type_map).unwrap(),
        None => return missing_parse_file.to_compile_error().into(),
    };

    let parse_code = parse_macro::generate_parser(grammar_parser);

    lex_code.extend(parse_code.into_iter());
    lex_code.into()
}
