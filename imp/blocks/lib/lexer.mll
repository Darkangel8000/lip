{
open Parser
}

let white = [' ' '\t']+
let characters = ['a'-'z' 'A'-'Z']+
let numbers = ['0'-'9']+
let newline = '\n'
let var_types = "int"

rule read =
  parse
  | white { read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LCPAREN }
  | "}" { RCPAREN }
  | ":=" { ASSIGN }
  | ";" { SEQ }
  | "." { SEQ2 }
  | "+" { ADD }
  | "-" { SUB }
  | "*" { MUL }
  | "=" { EQ }
  | "<=" { LEQ }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "and" { AND }
  | "or" { OR }
  | "not" { NOT }
  | "while" { WHILE }
  | "do" { DO }
  | "skip" { SKIP }
  | "int" { INTVAR }
  | newline { read lexbuf }
  | characters { VAR (Lexing.lexeme lexbuf) }
  | numbers { CONST (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }