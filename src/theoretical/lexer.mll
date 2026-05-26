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
  | "def" { DEF }
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
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "mu" { MULIT }
  | "μ" { MULIT }
  | "<" { LANGLE }
  | ">" { RANGLE }
  | "⟨" { LANGLE }
  | "⟩" { RANGLE }
  | "|" { BAR }
  | "." { DOT }
  | "@" { AT }
  | "U" { UNIV }
  | "refl" { REFL }
  | "I" { IDIR }
  | "𝕀" { IDIR }
  | "0" { ZERO }
  | "1" { ONE }
  | "<=" { LEQ }
  | "≤" { LEQ }
  | "⊆" { SUBSETEQ }
  | "subseteq" { SUBSETEQ }
  | "\\/" { JOIN }
  | "∨" { JOIN }
  | "/\\" { MEET }
  | "∧" { MEET }
  | "~" { NEG }
  | "¬" { NEG }
  | "not" { NEG }
  | ".1" { FST }
  | "fst" { FST }
  | ".2" { SND }
  | "snd" { SND }
  | "^tw" { TW }
  | "tw" { TW }
  | "π₀" { PI0 }
  | "pi0" { PI0 }
  | "π₁" { PI1 }
  | "pi1" { PI1 }
  | "=" { EQ }
  | ident as id { IDENT id }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "unexpected character: %c" c) }

and comment depth = parse
  | "-}" { if depth = 0 then token lexbuf else comment (depth - 1) lexbuf }
  | "{-" { comment (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment depth lexbuf }
  | _ { comment depth lexbuf }
  | eof { failwith "unterminated comment" }
