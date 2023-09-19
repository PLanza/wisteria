# Wisteria

**DISCLAIMER: Wisteria is still in its early development so expect  breaking changes!!!**

Wisteria is a lexer and parser generator for Rust. Lexing and parsing grammars are defined using a proprietary specification language in the style of Lex and Yacc, details of which can be found here (TODO).

Wisteria approaches the problems of lexing and parsing using non-standard approaches that emphasize algebraic correctness. The library generates lexers using the regular-expression derivatives approach defined in [Owens, et al.'s paper ](https://www.khoury.northeastern.edu/home/turon/re-deriv.pdf).

Moreover, wisteria generates recursive-descent parsers modelled on the system described by Krishnaswami and Yallop in their paper [A Typed, Algebraic Approach to Parsing](https://www.cl.cam.ac.uk/~jdy22/papers/a-typed-algebraic-approach-to-parsing.pdf). This means that the grammars allowed by Wisteria is more restrictive than for the more common LALR parsers. Nevertheless, there are ways of getting around these limitations (TODO), and future revisions of Wisteria will automate this process.

Full documentation for Wisteria can be found here (TODO).



---

### Usage

Wisteria will become a Rust library that can be added as a dependency using Cargo like any other.

The current API is comprised of a macro and a function as follows:


---

### Examples

An example describing a subset of C language expressions can be found in the `examples/c_expr` folder. More examples can be found in the documentation.
