pub use wist_utils::{Position, Span};

lex_macro::attach_lex_file!("example/test.wilex");

pub fn testing() {
    let token = LexToken::ID("hello".to_string());
}

// Parse Lexer File:
//  Use macro to parse file and create enum with tokens
//
// Generate Lexer Tokens
//
// Parse Code using lexer
