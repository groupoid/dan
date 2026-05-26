{
open Dan_parser
}

let whitespace = [' ' '\t' '\r']+
let string_lit = '\034' [^ '\034']* '\034'

let ident_start = ['a'-'z' 'A'-'Z' '_'] | "∂" | "ö"
let ident_char = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\''] | "∂" | "ö" | ("\xe2\x82" ['\x80'-'\x89'])
let ident = ident_start ident_char*

rule token = parse
  | whitespace { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | string_lit as s {
      let s' = String.sub s 1 (String.length s - 2) in
      STRING s'
    }
  | "--" [^ '\n']* { token lexbuf }
  | "import" { IMPORT }
  | "def" { DEF }
  | "in" { IN }
  | "∈" { IN }
  | "order" { ORDER }
  | "rel" { REL }
  | "PcGroup" { PCGROUP }
  | "FpGroup" { FPGROUP }
  | "PermGroup" { PERMGROUP }
  | "MatGroup" { MATGROUP }
  | "Hom" { HOM }
  | "Face" { FACE }
  | "Deg" { DEG }
  | "Boundary" { BOUNDARY }
  | "∂" { BOUNDARY }
  | "Orbit" { ORBIT }
  | "Stabilizer" { STABILIZER }
  | "Perm" { PERM }
  | "Cycle" { CYCLE }
  | "П" | "Π" { PI }
  | "∘" { COMP }
  | "+" { ADD }
  | "-" { SUB }
  | "/" { DIV }
  | "⋅" | "*" | "×" { MUL }
  | "·" | "•" { ACT }
  | "^-1" { INVLIT }
  | "^" { POW }
  | "¹" { POW_LIT S1 }
  | "²" { POW_LIT S2 }
  | "³" { POW_LIT S3 }
  | "⁴" { POW_LIT S4 }
  | "⁵" { POW_LIT S5 }
  | "⁶" { POW_LIT S6 }
  | "⁷" { POW_LIT S7 }
  | "⁸" { POW_LIT S8 }
  | "⁹" { POW_LIT S9 }
  | "∞" { INFINITE }
  | "|-" | "⊢" { TURNSTILE }
  | ":" { COLON }
  | ":=" { COLONEQ }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "=" { EQ }
  | "≠" | "!=" { NEQ }
  | "|" { BAR }
  | "<" { LEQ }
  | "≤" { LEQ }
  | "0" { ZERO }
  | "1" { ONE }
  | ['0'-'9']+ as n { INTLIT (int_of_string n) }
  | ident as id { IDENT id }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "unexpected character: %c" c) }
