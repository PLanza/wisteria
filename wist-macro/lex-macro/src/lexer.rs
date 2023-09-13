use quote::quote;

use std::collections::{HashMap, HashSet};

pub fn include_lexer(
    mut lex_parser: crate::LexParser,
) -> (HashMap<syn::Ident, syn::Type>, proc_macro2::TokenStream) {
    let (token_names, token_ty_variants, token_types) = lex_parser.parse_token_decs();
    let token_type_map: HashMap<syn::Ident, syn::Type> = token_names
        .clone()
        .into_iter()
        .zip(
            token_types
                .clone()
                .into_iter()
                .map(|o| o.map_or(syn::parse_str::<syn::Type>("()").unwrap(), |v| v)),
        )
        .collect();
    let (regex_names, regex_vals) = lex_parser.parse_regular_defs();
    let mut tok_kinds = HashSet::new();
    for name in &token_names {
        tok_kinds.insert(name.clone());
    }
    let (match_regex, ret_tok_kinds, ret_tok_contents) = lex_parser.parse_match_rules(tok_kinds);

    let n = match_regex.len();

    let mut tok_variant_map = HashMap::new();
    for (name, variant) in token_names.iter().zip(&token_ty_variants) {
        match variant {
            None => (),
            Some(variant) => {
                tok_variant_map.insert(name.clone(), variant.clone());
            }
        }
    }

    let mut token_enums = crate::gen_token_enums(&token_names, &token_ty_variants, &token_types);

    let token_fns = gen_token_fns(tok_variant_map, ret_tok_kinds, ret_tok_contents);

    let lexer_code: proc_macro2::TokenStream = quote! {
        fn __add_fn_to_map(
            map: &mut ::std::collections::HashMap<
                wist_lex::regex::Regex,
                Box<dyn Fn(String) -> LexToken>
            >,
            key: wist_lex::regex::Regex,
            func: Box<dyn Fn(String) -> LexToken>
        ) {
            map.insert(key, func);
        }

        pub struct Lexer {
            dfa: wist_lex::dfa::DFA<#n>,
            current_state: [wist_lex::regex::Regex; #n],
            input_buffer: String,
            token_fns: ::std::collections::HashMap<
                wist_lex::regex::Regex,
                Box<dyn Fn(String) -> LexToken>
            >,
            emitting_regex: Option<(usize, String)>,
        }

        impl Lexer {
            pub fn new() -> Result<Self, wist_lex::Error> {
                use ::std::collections::HashMap;
                use wist_lex::regex::Regex;

                // TODO: Save and load to/from a file
                let regular_defs = vec![#((#regex_names, #regex_vals)),*];

                let mut parser = wist_lex::RegexParser::new();
                let mut definitions: HashMap<String, Regex> = HashMap::new();
                for (name, regex) in regular_defs {
                    definitions.insert(
                        name.to_string(),
                        Regex::from_ast(parser.parse(&regex)?, &definitions),
                    );
                    parser.reset();
                }

                // TODO: Save and load to/from a file
                let match_rules = vec![#(#match_regex),*];
                let mut regexes: [Regex; #n] = (0..#n)
                    .map(|_| wist_lex::EMPTY_REGEX.clone())
                    .collect::<Vec<Regex>>()
                    .try_into()
                    .unwrap();
                for (i, regex) in match_rules.iter().enumerate() {
                    regexes[i] = Regex::from_ast(parser.parse(&regex)?, &definitions);
                    parser.reset();
                }

                let token_fns: Vec<Box<dyn Fn(String) -> LexToken>> = vec![
                    #(Box::new(|_lex: String| -> LexToken {#token_fns})),*
                ];
                let mut fns_map = HashMap::new();
                for (regex, func) in regexes.clone().into_iter().zip(token_fns) {
                    __add_fn_to_map(&mut fns_map, regex, func);
                }

                let dfa = wist_lex::dfa::DFA::<#n>::from_regexes(regexes);
                Ok(Lexer {
                    emitting_regex: None,
                    input_buffer: "".to_string(),
                    current_state: dfa.start_state.clone(),
                    token_fns: fns_map,
                    dfa,
                })
            }

            fn lex_file(&mut self, path: String) -> ::std::io::Result<Vec<LexToken>> {
                let file = ::std::fs::File::open(path)?;
                use ::std::io::prelude::*;
                let lines = ::std::io::BufReader::new(file).lines();

                let mut output_tokens = Vec::new();

                for line in lines {
                    let mut chars: Vec<char> = line?.chars().collect();
                    chars.push('\n');
                    while !chars.is_empty() {
                        let c = chars.remove(0);
                        self.input_buffer.push(c);
                        match self.step(c) {
                            None => (),
                            Some(token) => {
                                if token.tag != LexTokenTag::_SKIP {
                                    output_tokens.push(token);
                                }

                                self.current_state = self.dfa.start_state.clone();

                                let clone = self.emitting_regex.clone();
                                let truncated = self.input_buffer
                                    [clone.unwrap().1.len()..]
                                    .chars();
                                for (i, c) in truncated.enumerate() {
                                    chars.insert(i, c);
                                }

                                self.emitting_regex = None;
                                self.input_buffer = String::new();
                            }
                        }
                    }

                }

                let token = self.produce_token();
                if token.tag != LexTokenTag::_SKIP {
                    output_tokens.push(token);
                }

                Ok(output_tokens)
            }

            fn step(&mut self, c: char) -> Option<LexToken> {
                match self.dfa.transitions.get(&self.current_state) {
                    Some(transitions) => {
                        for (set, next_state) in transitions {
                            if set.contains(c) {
                                self.current_state = next_state.clone();
                                self.update_emitting_regex();
                                return None;
                            }
                        }
                        panic!("missing transition")
                    }
                    None => Some(self.produce_token())
                }
            }

            fn update_emitting_regex(&mut self) {
                for (i, regex) in self.current_state.iter().enumerate() {
                    if regex.nullable() {
                        self.emitting_regex = Some((i, self.input_buffer.clone()));
                        break;
                    }
                }
            }

            fn produce_token(&mut self) -> LexToken {
                let token = match &self.emitting_regex {
                    None => panic!("Need to emit token"),
                    Some((i, value)) => {
                        let matching_regex = &self.dfa.start_state[*i];
                        let token_fn = self.token_fns.get(matching_regex)
                            .unwrap_or_else(|| panic!("Regex has no matching token"));
                        token_fn(value.clone())
                    },
                };

                token
            }
        }
    };

    token_enums.extend(lexer_code.into_iter());
    (token_type_map, token_enums)
}

fn gen_token_fns(
    tok_variant_map: HashMap<syn::Ident, syn::Ident>,
    ret_tok_kinds: Vec<Option<syn::Ident>>,
    ret_tok_contents: Vec<Option<proc_macro2::TokenStream>>,
) -> Vec<proc_macro2::TokenStream> {
    let mut fns = Vec::new();

    for (kind, content) in ret_tok_kinds.iter().zip(ret_tok_contents) {
        match (kind, content) {
            (None, None) => fns.push(quote! {
                LexToken {
                    tag: LexTokenTag::_SKIP,
                    val: LexTokenValue::None,
                }
            }),
            (Some(kind), None) => fns.push(quote! {
                LexToken {
                    tag: LexTokenTag::#kind,
                    val: LexTokenValue::None,
                }
            }),
            (Some(kind), Some(content)) => {
                let variant = tok_variant_map.get(kind).unwrap();
                fns.push(quote! {
                    LexToken {
                        tag: LexTokenTag::#kind,
                        val: LexTokenValue::#variant(#content),
                    }
                })
            }
            (_, _) => unreachable!(),
        }
    }

    fns
}
