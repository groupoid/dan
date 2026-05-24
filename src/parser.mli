type token =
  | IDENT of (
# 5 "src/parser.mly"
        string
# 6 "src/parser.mli"
)
  | STRING of (
# 6 "src/parser.mly"
        string
# 11 "src/parser.mli"
)
  | MODULE
  | WHERE
  | IMPORT
  | FUNCTOR
  | DEF_TYPE
  | DEF_TERM
  | CHECK
  | COLON
  | COLONEQ
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LANGLE
  | RANGLE
  | BAR
  | TURNSTILE
  | DOT
  | AT
  | OP
  | HOMLIT
  | COENDLIT
  | ENDLIT
  | TENSORLIT
  | FUNCLIT
  | IDLIT
  | JLIT
  | JCOVLIT
  | JCONTRALIT
  | LET
  | IN
  | MIX
  | LAMBDALIT
  | EOF
  | UNIV
  | REFL
  | IDIR
  | ZERO
  | ONE
  | LEQ
  | SUBSETEQ
  | JOIN
  | MEET
  | NEG
  | FST
  | SND
  | TW
  | PI0
  | PI1
  | EQ
  | LBRACE
  | RBRACE
  | MULIT

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.cmd list
