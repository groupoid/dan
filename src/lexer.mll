{
open Parser
}

let whitespace = [' ' '\t' '\r']+
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
let string_lit = '\034' [^ '\034']* '\034'

rule token = parse
  | whitespace { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | string_lit as s {
      let s' = String.sub s 1 (String.length s - 2) in
      STRING s'
    }
  | "--" [^ '\n']* { token lexbuf }
  | "{-" { comment 0 lexbuf }
  | "module" { MODULE }
  | "where" { WHERE }
  | "import" { IMPORT }
  | "functor" { FUNCTOR }
  | "def_type" { DEF_TYPE }
  | "def_term" { DEF_TERM }
  | "check" { CHECK }
  | "hom" { HOMLIT }
  | "coend" { COENDLIT }
  | "end" { ENDLIT }
  | "id" { IDLIT }
  | "J" { JLIT }
  | "J_cov" { JCOVLIT }
  | "J_contra" { JCONTRALIT }
  | "let" { LET }
  | "in" { IN }
  | "mix" { MIX }
  | "lambda" { LAMBDALIT }
  | "λ" { LAMBDALIT }
  | "\\" { LAMBDALIT }
  | "∫^" { COENDLIT }
  | "∫_" { ENDLIT }
  | "⊗" { TENSORLIT }
  | "⊸" { FUNCLIT }
  | "†" { OP }
  | "^op" { OP }
  | "op" { OP }
  | "*" { TENSORLIT }
  | "×" { TENSORLIT }
  | "->" { FUNCLIT }
  | "|-" { TURNSTILE }
  | "⊢" { TURNSTILE }
  | ":" { COLON }
  | ":=" { COLONEQ }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "<" { LANGLE }
  | ">" { RANGLE }
  | "⟨" { LANGLE }
  | "⟩" { RANGLE }
  | "|" { BAR }
  | "." { DOT }
  | "@" { AT }
  | ident as id { IDENT id }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "unexpected character: %c" c) }

and comment depth = parse
  | "-}" { if depth = 0 then token lexbuf else comment (depth - 1) lexbuf }
  | "{-" { comment (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment depth lexbuf }
  | _ { comment depth lexbuf }
  | eof { failwith "unterminated comment" }
