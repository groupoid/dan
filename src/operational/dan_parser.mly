%{
open Dan_syntax

let eq_count = ref 0
let next_eq_id () =
  incr eq_count;
  "eq_" ^ string_of_int !eq_count
%}

%token <string> IDENT
%token <string> STRING
%token DEF PI COMP ADD SUB DIV INFINITE MUL IMPORT LEQ LANGLE POW
%token COLON COLONEQ COMMA LPAREN RPAREN LBRACKET RBRACKET BAR TURNSTILE EQ EOF INVLIT ZERO ONE
%token <Dan_syntax.superscript> POW_LIT
%token <int> INTLIT

%left ADD SUB
%left MUL DIV
%left COMP
%left POW

%start file
%type <Dan_syntax.cmd list> file

%%

file:
  | decls EOF { $1 }

decls:
  | /* empty */ { [] }
  | decl decls  { $1 :: $2 }

decl:
  | IMPORT IDENT { CImport $2 }
  | IMPORT STRING { CImport $2 }
  | DEF IDENT COLON IDENT COLONEQ PI dan_context TURNSTILE dan_specs
    { CDef { name = $2; typ = parse_type_name $4; context = $7; specs = $9 } }

dan_specs:
  | dan_spec { [$1] }
  | dan_specs COMMA dan_spec { $1 @ [$3] }

dan_spec:
  | dan_rank LPAREN idents_list BAR idents_list RPAREN
    { { spec_rank = $1; spec_elements = $3; spec_faces = $5; spec_constraints = [] } }
  | dan_rank LPAREN idents_list BAR dan_constraints_list RPAREN
    { { spec_rank = $1; spec_elements = $3; spec_faces = []; spec_constraints = $5 } }
  | dan_rank LPAREN idents_list BAR idents_list BAR dan_constraints_list RPAREN
    { { spec_rank = $1; spec_elements = $3; spec_faces = $5; spec_constraints = $7 } }

idents_list:
  | IDENT { [$1] }
  | idents_list IDENT { $1 @ [$2] }
  | idents_list COMMA IDENT { $1 @ [$3] }

dan_constraints:
  | /* empty */ { [] }
  | dan_constraints_list { $1 }

dan_constraints_list:
  | dan_constraint { [$1] }
  | dan_constraints_list COMMA dan_constraint { $1 @ [$3] }

dan_constraint:
  | dan_term EQ dan_term { Eq ($1, $3) }
  | dan_term LEQ dan_term { Eq ($1, $3) }

dan_context:
  | dan_hypotheses { $1 }

dan_hypotheses:
  | dan_hypothesis { $1 }
  | dan_hypotheses COMMA dan_hypothesis { $1 @ $3 }

dan_hypothesis:
  | idents_list COLON IDENT { [Decl ($1, parse_type_name $3)] }
  | LPAREN idents_list COLON IDENT RPAREN { [Decl ($2, parse_type_name $4)] }
  | dan_term EQ dan_term { [Equality (next_eq_id (), $1, $3)] }
  | dan_term LEQ dan_term { [Mapping (next_eq_id (), $1, $3)] }
  | LPAREN idents_list COLON IDENT COMMA dan_term EQ dan_term RPAREN
    { [Decl ($2, parse_type_name $4); Equality (next_eq_id (), $6, $8)] }
  | LPAREN IDENT COLON IDENT LPAREN PI dan_context TURNSTILE dan_rank LPAREN idents_list BAR dan_constraints RPAREN RPAREN RPAREN
    { $7 }

dan_term:
  | IDENT { if $1 = "e" then E else Id $1 }
  | ZERO { Id "0" }
  | ONE { Id "1" }
  | INTLIT { Id (string_of_int $1) }
  | dan_term COMP dan_term { Comp ($1, $3) }
  | dan_term IDENT %prec COMP { Comp ($1, Id $2) }
  | dan_term INVLIT { Inv $1 }
  | dan_term POW_LIT { Pow ($1, $2) }
  | dan_term POW dan_term { Pow ($1, SN (string_of_term $3)) }
  | IDENT LPAREN dan_term RPAREN { Id ($1 ^ "(" ^ string_of_term $3 ^ ")") }
  | dan_term ADD dan_term { Add ($1, $3) }
  | dan_term MUL dan_term { Mul ($1, $3) }
  | dan_term DIV dan_term { Div ($1, $3) }
  | matrix { Matrix $1 }
  | LPAREN dan_term RPAREN { $2 }

matrix:
  | LBRACKET rows RBRACKET { $2 }

rows:
  | row { [$1] }
  | row COMMA rows { $1 :: $3 }

row:
  | LBRACKET numbers RBRACKET { $2 }

numbers:
  | INTLIT { [$1] }
  | ZERO { [0] }
  | ONE { [1] }
  | INTLIT COMMA numbers { $1 :: $3 }
  | ZERO COMMA numbers { 0 :: $3 }
  | ONE COMMA numbers { 1 :: $3 }

dan_rank:
  | INTLIT { Finite $1 }
  | ZERO { Finite 0 }
  | ONE { Finite 1 }
  | INFINITE { Infinite }
%%
