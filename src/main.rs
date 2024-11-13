// tiny.rs
//
// Tiny is a small calculator language.  It supports integers, three
// different math operations (+, -, *), grouping with parenthesis, and
// variables.   Here are some valid Tiny expressions:
//
//     2 + 3
//     2 + (3 * 4)
//     x = 2 + 3
//     10 + x
//
// Tiny does not allow more than two terms in a math operation. So
// "2 + 3 * 4" is illegal.  However, you can use parentheses to break
// it up into parts like "(2 + 3) * 4" or "2 + (3 * 4)".
//
// The code below implements Tiny.  The purpose is to illustrate the
// core features of a small programming language all in one place.
//
// In preparation for our Rust implementation of Crafting Interpreters,
// you might begin here.  See if you can translate the following
// code to Rust.  Doing this will require you to learn about Rust
// string handling, functions, and data structures.

use std::io::BufRead;
use std::fmt::Display;
use std::collections::BTreeMap;
use anyhow::{anyhow, Result};
use std::io::{self, Write};

// -----------------------------------------------------------------------------
// Part 1 : Tokens
//
// As input, a programming language usually receives source code in the
// form of a string. A tokenizer takes the source string and breaks it
// into tokens.  Think of a token as a "word" in the programming language.
// Tiny has the following token types:
//
//    NUM     : One or more numerical digits. (example, 1234)
//    NAME    : One or more alphabetic characters (example, abc)
//    PLUS    : '+'
//    MINUS   : '-'
//    TIMES   : '*'
//    LPAREN  : '('
//    RPAREN  : ')'
//    ASSIGN  : '='


#[derive(PartialEq, PartialOrd, Eq, Ord, Debug, Copy, Clone)]
enum TokenType {
    Number,
    Name,
    Plus,
    Minus,
    Times,
    LParen,
    RParen,
    Assign,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            TokenType::Number => {
                write!(f, "Number")
            },
            TokenType::Name => {
                write!(f, "Name")
            },
            TokenType::Plus => {
                write!(f, "+")
            },
            TokenType::Minus => {
                write!(f, "-")
            },
            TokenType::Times => {
                write!(f, "*")
            },
            TokenType::LParen => {
                write!(f, "(")
            },
            TokenType::RParen => {
                write!(f, ")")
            },
            TokenType::Assign => {
                write!(f, "=")
            },
        }
    }
}

#[derive(PartialEq, PartialOrd, Eq, Ord, Debug)]
enum TokenMode { Token, Number, Name }

#[derive(PartialEq, PartialOrd, Eq, Ord, Debug)]
struct Token { toktype: TokenType, tokvalue: String }

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.toktype {
            TokenType::Number => {
                write!(f, "{}", self.tokvalue)
            },
            TokenType::Name => {
                write!(f, "{}", self.tokvalue)
            },
            TokenType::Plus => {
                write!(f, "+")
            },
            TokenType::Minus => {
                write!(f, "-")
            },
            TokenType::Times => {
                write!(f, "*")
            },
            TokenType::LParen => {
                write!(f, "(")
            },
            TokenType::RParen => {
                write!(f, ")")
            },
            TokenType::Assign => {
                write!(f, "=")
            },
        }
    }
}

impl Token {
    fn tokenize(text: &str) -> Result<Vec<Self>> {
        let mut literals: BTreeMap<char, TokenType> = BTreeMap::new();
        literals.insert('+', TokenType::Plus);
        literals.insert('-', TokenType::Minus);
        literals.insert('*', TokenType::Times);
        literals.insert('(', TokenType::LParen);
        literals.insert(')', TokenType::RParen);
        literals.insert('=', TokenType::Assign);

        let mut tokens: Vec<Self> = vec![];
        let chars = text.chars();
        let mut mode = TokenMode::Token;
        let mut partial_token: Vec<char> = vec![];
        for c in chars {
            if c.is_whitespace() {
                match mode {
                    TokenMode::Token => {
                        continue;
                    },
                    TokenMode::Name => {
                        if partial_token.len() > 0 {
                            tokens.push(Token{
                                toktype: TokenType::Name,
                                tokvalue: partial_token.iter().collect::<String>(),
                            });
                        }
                        partial_token = vec![];
                    },
                    TokenMode::Number => {
                        if partial_token.len() > 0 {
                            tokens.push(Token{
                                toktype: TokenType::Number,
                                tokvalue: partial_token.iter().collect::<String>(),
                            });
                        }
                        partial_token = vec![];
                    }
                }
                mode = TokenMode::Token;
                continue;
            } else if c.is_numeric() {
                match mode {
                    TokenMode::Token => {
                        partial_token = vec![c];
                        mode = TokenMode::Number;
                    },
                    TokenMode::Name => {
                        tokens.push(Token{
                            toktype: TokenType::Name,
                            tokvalue: partial_token.iter().collect::<String>(),
                        });
                        partial_token = vec![c];
                        mode = TokenMode::Number;
                    },
                    TokenMode::Number => {
                        partial_token.push(c);
                    }
                }
            } else if c.is_alphabetic() {
                match mode {
                    TokenMode::Token => {
                        partial_token = vec![c];
                        mode = TokenMode::Name;
                    },
                    TokenMode::Name => {
                        partial_token.push(c);
                    },
                    TokenMode::Number => {
                        tokens.push(Token{
                            toktype: TokenType::Number,
                            tokvalue: partial_token.iter().collect::<String>(),
                        });
                        partial_token = vec![c];
                        mode = TokenMode::Name;
                    }
                }
            } else if let Some((tokvalue, toktype)) = literals.get_key_value(&c) {
                match mode {
                    TokenMode::Token => {},
                    TokenMode::Name => {
                        tokens.push(Token{
                            toktype: TokenType::Name,
                            tokvalue: partial_token.iter().collect::<String>(),
                        });
                        mode = TokenMode::Token;
                    },
                    TokenMode::Number => {
                        tokens.push(Token{
                            toktype: TokenType::Number,
                            tokvalue: partial_token.iter().collect::<String>(),
                        });
                        mode = TokenMode::Token;
                    }
                }

                tokens.push(Token{
                    toktype: toktype.clone(),
                    tokvalue: tokvalue.to_string(),
                });
                partial_token = vec![];
            } else {
                return Err(anyhow!("Bad character '{}'", c));
            }
        }
        if partial_token.len() > 0 {
            match mode {
                TokenMode::Token => {
                    return Err(anyhow!("Bad token '{}", partial_token.iter().collect::<String>()));
                },
                TokenMode::Name => {
                    tokens.push(Token{ toktype: TokenType::Name, tokvalue: partial_token.iter().collect::<String>() });
                },
                TokenMode::Number => {
                    tokens.push(Token{ toktype: TokenType::Number, tokvalue: partial_token.iter().collect::<String>() });
                },
            }
        }
        Ok(tokens)
    }
}

// -----------------------------------------------------------------------------
// Part 2 : Parsing and Abstract Syntax
//
// Programs are represented as a data structure known as an abstract
// syntax tree (AST).  Construction of the AST is performed by a parser.
// The following code implements the AST and a recursive descent parser.

#[derive(PartialEq, Eq, Debug)]
enum Expr {
    Number{n: i64},
    Variable{name: String},
    Assign{location: Box<Expr>, value: Box<Expr> },
    Add{left: Box<Expr>, right: Box<Expr> },
    Sub{left: Box<Expr>, right: Box<Expr> },
    Mul{left: Box<Expr>, right: Box<Expr> },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Number{n} => {
                write!(f, "{}", n)
            },
            Expr::Variable{name} => {
                write!(f, "{}", name)
            },
            Expr::Assign{location, value} => {
                write!(f, "{} = {}", *location, *value)
            },
            Expr::Add{left, right } => {
                write!(f, "{} + {}", *left, *right)
            },
            Expr::Sub{left, right } => {
                write!(f, "{} - {}", *left, *right)
            },
            Expr::Mul{left, right } => {
                write!(f, "({}) * ({})", *left, *right)
            },
        }
    }
}

// Parsing is implemented by making a left-to-right scan through a list
// of tokens.  At a superfiscal level, scanning a list is a lot like
// iterating with a for-loop.  However, unlike iteration, parsing also
// involves the extra step of "peeking ahead."  The following class
// implements methods needed for this scanning process.
#[derive(Debug)]
struct Parser {
    tokens: Vec<Token>,
    n: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, n: 0 } }

    fn accept(&mut self, toktype: TokenType) -> bool {
        if self.n < self.tokens.len() && self.tokens[self.n].toktype == toktype {
            self.n += 1;
            true
        } else {
            false
        }
    }

    fn last(&self) -> Option<&Token> {
        if self.n > 0 {
            self.tokens.get(self.n-1)
        } else {
            None
        }
    }

    fn at_end(&self) -> bool {
        self.n >= self.tokens.len()
    }

    // Top level parsing function.  This parses everything and makes sure there
    // are no unconsumed tokens left over.
    fn parse(&mut self) -> Result<Expr> {
        let expr = self.parse_expression()?;
        // On success, we should be at the end
        if !self.at_end() {
            return Err(anyhow!("syntax error"));
        }
        return Ok(expr);
    }

    fn parse_expression(&mut self) -> Result<Expr> {
        let left = self.parse_term()?;
        if self.accept(TokenType::Plus) {
            Ok(Expr::Add{ left: Box::new(left), right: Box::new(self.parse_term()?) })
        } else if self.accept(TokenType::Minus) {
            Ok(Expr::Sub{ left: Box::new(left), right: Box::new(self.parse_term()?) })
        } else if self.accept(TokenType::Times) {
            Ok(Expr::Mul{ left: Box::new(left), right: Box::new(self.parse_term()?)})
        } else if self.accept(TokenType::Assign) {
            Ok(Expr::Assign{ location: Box::new(left), value: Box::new(self.parse_expression()?) })
        } else {
            Ok(left)
        }
    }

    fn parse_term(&mut self) -> Result<Expr> {
        if self.accept(TokenType::Number) {
            if let Some(last) = self.last() {
                let n = last.tokvalue.parse().expect("Expected a number");
                return Ok(Expr::Number{ n });
            }
        } else if self.accept(TokenType::Name) {
            if let Some(last) = self.last() {
                return Ok(Expr::Variable{ name: last.tokvalue.clone() });
            }
        } else if self.accept(TokenType::LParen) {
            let e = self.parse_expression();
            if !self.accept(TokenType::RParen) {
                return Err(anyhow!("Expected a )"));
            }
            return e;
        }
        return Err(anyhow!("Expected a term"));
    }
}

// -----------------------------------------------------------------------------
// Part 3 - Interpreter
//
// An interpreter turns the AST into a value.  This involves walking over the
// AST structure, but also managing an environment for variables.

// The environment is a place to load/store variable values during evaluation.
struct Environment {
    vars: BTreeMap<String, i64>
}

impl Environment {
    fn new() -> Self {
        let vars = BTreeMap::new();
        Self{ vars }
    }

    fn assign(&mut self, name: &str, value: i64) {
        self.vars.insert(name.to_string(), value);
    }

    fn lookup(&self, name: &str) -> Option<i64> {
        self.vars.get(name).copied()
    }
}

// Evaluation works by recursively walking the AST and turning each
// AST node into a value.
fn evaluate(e: Expr, environ: &mut Environment) -> Result<i64> {
    match e {
        Expr::Number { n } => Ok(n),

        Expr::Variable { name } =>
            environ
                .lookup(&name)
                .map(Ok)
                .unwrap_or_else(|| Err(anyhow!("Can't evaluate {}", name))),

        Expr::Assign { location, value } => {
            if let Expr::Variable{ name } = *location {
                let value = evaluate(*value, environ)?;
                environ.assign(&name, value);
                environ
                    .lookup(&name)
                    .map(Ok)
                    .unwrap_or_else(|| panic!("Can't evaluate {}", name))
            } else {
                Err(anyhow!("Can't evaluate {} = {}", location, value))
            }
        },

        Expr::Add{ left, right } => {
            Ok(evaluate(*left, environ)? + evaluate(*right, environ)?)
        }

        Expr::Sub{ left, right } => {
            Ok(evaluate(*left, environ)? - evaluate(*right, environ)?)
        }

        Expr::Mul{ left, right } => {
            Ok(evaluate(*left, environ)? * evaluate(*right, environ)?)
        }
    }
}

// -----------------------------------------------------------------------------
// Part 4 - REPL (Read-Eval Print Loop)
//
// The following code reads expressions from the user, evaluates it, and
// prints the final result.

fn input(prompt: &str) -> Result<String> {
    print!("{}", prompt);
    io::stdout().flush()?;
    io::stdin()
        .lock()
        .lines()
        .next()
        .unwrap()
        .map(|x| x.trim_end().to_owned())
        .map_err(|e| anyhow!(e))
}

fn re(line: &str, environ: &mut Environment) -> Result<i64> {
    let tokens = Token::tokenize(&line)?;
    let ast = Parser::new(tokens).parse()?;
    evaluate(ast, environ)
}

fn repl() {
    let mut environ = Environment::new();
    loop {
        if let Ok(line) = input("calc > ") {
            let result = re(&line, &mut environ);
            match result {
                Ok(n) => {
                    println!("{}", n);
                },
                Err(err) => {
                    println!("{}", err);
                }
            }
        } else {
            break;
        }
    }
}

// Tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() {
        assert_eq!(Token::tokenize("+").unwrap().len(),  1);
        assert_eq!(Token::tokenize("+").unwrap()[0].toktype, TokenType::Plus);

        assert_eq!(Token::tokenize("-").unwrap().len(), 1);
        assert_eq!(Token::tokenize("-").unwrap()[0].toktype, TokenType::Minus);

        assert_eq!(Token::tokenize("*").unwrap().len(), 1);
        assert_eq!(Token::tokenize("*").unwrap()[0].toktype, TokenType::Times);

        assert_eq!(Token::tokenize("(").unwrap().len(), 1);
        assert_eq!(Token::tokenize("(").unwrap()[0].toktype, TokenType::LParen);

        assert_eq!(Token::tokenize(")").unwrap().len(), 1);
        assert_eq!(Token::tokenize(")").unwrap()[0].toktype, TokenType::RParen);

        assert_eq!(Token::tokenize("=").unwrap().len(), 1);
        assert_eq!(Token::tokenize("=").unwrap()[0].toktype, TokenType::Assign);

        assert_eq!(Token::tokenize("identifier").unwrap().len(), 1);
        assert_eq!(Token::tokenize("identifier").unwrap()[0].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("identifier").unwrap()[0].tokvalue, "identifier");

        assert_eq!(Token::tokenize("identifierandnumber12345").unwrap().len(), 2);
        assert_eq!(Token::tokenize("identifierandnumber12345").unwrap()[0].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("identifierandnumber12345").unwrap()[0].tokvalue, "identifierandnumber");
        assert_eq!(Token::tokenize("identifierandnumber12345").unwrap()[1].toktype, TokenType::Number);
        assert_eq!(Token::tokenize("identifierandnumber12345").unwrap()[1].tokvalue, "12345");

        assert_eq!(Token::tokenize("1 + 2").unwrap().len(), 3);
        assert_eq!(Token::tokenize("1 + 2").unwrap().len(), 3);

        assert_eq!(Token::tokenize("1 + 2").unwrap()[0].toktype, TokenType::Number);
        assert_eq!(Token::tokenize("1 + 2").unwrap()[0].tokvalue, "1");
        assert_eq!(Token::tokenize("1 + 2").unwrap()[1].toktype, TokenType::Plus);
        assert_eq!(Token::tokenize("1 + 2").unwrap()[1].tokvalue, "+");
        assert_eq!(Token::tokenize("1 + 2").unwrap()[2].toktype, TokenType::Number);
        assert_eq!(Token::tokenize("1 + 2").unwrap()[2].tokvalue, "2");

        assert_eq!(Token::tokenize("id + 1").unwrap()[0].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("id + 1").unwrap()[0].tokvalue, "id");
        assert_eq!(Token::tokenize("id + 1").unwrap()[1].toktype, TokenType::Plus);
        assert_eq!(Token::tokenize("id + 1").unwrap()[1].tokvalue, "+");
        assert_eq!(Token::tokenize("id + 1").unwrap()[2].toktype, TokenType::Number);
        assert_eq!(Token::tokenize("id + 1").unwrap()[2].tokvalue, "1");

        assert_eq!(Token::tokenize("a = 1 a + a").unwrap().len(), 6);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[0].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[0].tokvalue, "a");
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[1].toktype, TokenType::Assign);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[1].tokvalue, "=");
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[2].toktype, TokenType::Number);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[2].tokvalue, "1");
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[3].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[3].tokvalue, "a");
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[4].toktype, TokenType::Plus);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[4].tokvalue, "+");
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[5].toktype, TokenType::Name);
        assert_eq!(Token::tokenize("a = 1 a + a").unwrap()[5].tokvalue, "a");
    }

    #[test]
    fn test_parse_term() {
        assert_eq!(Parser::new(Token::tokenize("1").unwrap()).parse_term().unwrap(), Expr::Number { n: 1 });
        assert_eq!(Parser::new(Token::tokenize("1 + 2").unwrap()).parse_term().unwrap(), Expr::Number { n: 1 });
        assert_eq!(Parser::new(Token::tokenize("ident").unwrap()).parse_term().unwrap(), Expr::Variable { name: "ident".to_string() });
        assert_eq!(Parser::new(Token::tokenize("ident + 2").unwrap()).parse_term().unwrap(), Expr::Variable { name: "ident".to_string() });
        assert_eq!(Parser::new(Token::tokenize("1 * 2").unwrap()).parse_term().unwrap(), Expr::Number { n: 1 });
        assert_eq!(Parser::new(Token::tokenize("1 - ident").unwrap()).parse_term().unwrap(), Expr::Number { n: 1 });
    }

    #[test]
    fn test_parse_expression() {
        assert_eq!(
            Parser::new(Token::tokenize("1 + 2").unwrap()).parse_expression().unwrap(),
            Expr::Add {
                left: Box::new(Expr::Number { n: 1 }),
                right: Box::new(Expr::Number { n: 2 }),
            },
        );
        assert_eq!(
            Parser::new(Token::tokenize("a = 2").unwrap()).parse_expression().unwrap(),
            Expr::Assign {
                location: Box::new(Expr::Variable { name: "a".to_string() }),
                value: Box::new(Expr::Number { n: 2 }),
            }
        );
    }

    #[test]
    fn test_parse() {
        let tokens = Token::tokenize("1 + 2").unwrap();
        println!("{:?}", tokens);
        let mut parser = Parser::new(tokens);
        let parse_result = parser.parse();
        println!("{:?}", parse_result);
        println!("{:?}", parser);
        assert_eq!(
            parse_result.unwrap(),
            Expr::Add {
                left: Box::new(Expr::Number { n: 1 }),
                right: Box::new(Expr::Number { n: 2 }),
            },
        );
    }

    #[test]
    fn test_evaluate() {
        let mut environ = Environment::new();
        let a = re("a = 5", &mut environ);
        let b = re("b = 2", &mut environ);
        let result = re("20 - (a + (b + (a * 2)))", &mut environ);
        assert_eq!(a.unwrap(), 5);
        assert_eq!(b.unwrap(), 2);
        assert_eq!(result.unwrap(), 3);
    }
}

fn main() {
    repl();
}
