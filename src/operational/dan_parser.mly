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

/* GAP Tokens */
%token ACT NEQ IN ORDER REL PCGROUP FPGROUP PERMGROUP MATGROUP HOM FACE DEG BOUNDARY ORBIT STABILIZER PERM CYCLE

%left ADD SUB
%left MUL DIV ACT
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
  | DEF IDENT COLON type_ident COLONEQ PI dan_context TURNSTILE dan_specs
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
  | dan_term NEQ dan_term { Neq ($1, $3) }
  | dan_term IN dan_term { In ($1, $3) }
  | ORDER LPAREN dan_term RPAREN EQ INTLIT { Order ($3, $6) }
  | REL LBRACKET dan_terms RBRACKET { Rel $3 }

dan_context:
  | dan_hypotheses { $1 }

dan_hypotheses:
  | dan_hypothesis { $1 }
  | dan_hypotheses COMMA dan_hypothesis { $1 @ $3 }

type_ident:
  | IDENT { $1 }
  | PERMGROUP { "PermGroup" }
  | MATGROUP { "MatGroup" }
  | FPGROUP { "FpGroup" }
  | PCGROUP { "PcGroup" }

dan_hypothesis:
  | idents_list COLON type_ident { [Decl ($1, parse_type_name $3)] }
  | LPAREN idents_list COLON type_ident RPAREN { [Decl ($2, parse_type_name $4)] }
  | dan_term EQ dan_term { [Equality (next_eq_id (), $1, $3)] }
  | dan_term LEQ dan_term { [Mapping (next_eq_id (), $1, $3)] }
  | REL LPAREN dan_term RPAREN { [Relation $3] }
  | ORBIT LPAREN dan_term COMMA dan_term RPAREN EQ LBRACKET idents_list RBRACKET
    { [Orbit ($3, $5, List.map (fun x -> Id x) $9)] }
  | STABILIZER LPAREN dan_term COMMA dan_term RPAREN EQ dan_term
    { [Stabilizer ($3, $5, $8)] }
  | LPAREN idents_list COLON type_ident COMMA dan_term EQ dan_term RPAREN
    { [Decl ($2, parse_type_name $4); Equality (next_eq_id (), $6, $8)] }
  | LPAREN idents_list COLON type_ident LPAREN PI dan_context TURNSTILE dan_rank LPAREN idents_list BAR dan_constraints RPAREN RPAREN RPAREN
    { $7 }

dan_terms:
  | dan_term { [$1] }
  | dan_terms COMMA dan_term { $1 @ [$3] }
  | dan_terms dan_term { $1 @ [$2] }

dan_term:
  | IDENT { if $1 = "e" then E else Id $1 }
  | ZERO { Scalar 0 }
  | ONE { Scalar 1 }
  | INTLIT { Scalar $1 }
  | dan_term COMP dan_term { Comp ($1, $3) }
  | dan_term IDENT %prec COMP { Comp ($1, Id $2) }
  | dan_term INVLIT { Inv $1 }
  | dan_term POW_LIT { Pow ($1, $2) }
  | dan_term POW dan_term {
      match $3 with
      | Scalar n -> PowInt ($1, n)
      | _ -> Conj ($1, $3)
    }
  | LBRACKET dan_term COMMA dan_term RBRACKET { Comm ($2, $4) }
  | IDENT LPAREN dan_term RPAREN { Id ($1 ^ "(" ^ string_of_term $3 ^ ")") }
  | dan_term ADD dan_term { Add ($1, $3) }
  | dan_term MUL dan_term { Mul ($1, $3) }
  | dan_term DIV dan_term { Div ($1, $3) }
  | matrix { Matrix $1 }
  | LPAREN dan_term RPAREN { $2 }
  | PERM LPAREN numbers RPAREN { Perm $3 }
  | CYCLE cycles { Cycle $2 }
  | PERMGROUP LPAREN dan_terms RPAREN { PermGroup $3 }
  | MATGROUP LPAREN dan_terms COMMA INTLIT COMMA INTLIT RPAREN { MatGroup ($3, $5, $7) }
  | FPGROUP LPAREN idents_list BAR fp_relators RPAREN { FpGroup ($3, $5) }
  | PCGROUP LPAREN idents_list BAR fp_relators RPAREN { PcGroup ($3, $5) }
  | FACE POW_LIT LPAREN dan_term RPAREN { Face ($2, $4) }
  | FACE POW dan_term LPAREN dan_term RPAREN { Face (SN (string_of_term $3), $5) }
  | FACE LPAREN INTLIT COMMA dan_term RPAREN { Face (Sn $3, $5) }
  | FACE LPAREN IDENT COMMA dan_term RPAREN { Face (SN $3, $5) }
  | DEG POW_LIT LPAREN dan_term RPAREN { Deg ($2, $4) }
  | DEG POW dan_term LPAREN dan_term RPAREN { Deg (SN (string_of_term $3), $5) }
  | DEG LPAREN INTLIT COMMA dan_term RPAREN { Deg (Sn $3, $5) }
  | DEG LPAREN IDENT COMMA dan_term RPAREN { Deg (SN $3, $5) }
  | BOUNDARY LPAREN dan_term RPAREN { Boundary $3 }
  | dan_term ACT dan_term { Act ($1, $3) }
  | HOM LPAREN dan_term COMMA dan_term RPAREN { Hom ($3, $5) }

cycles:
  | cycle { [$1] }
  | cycle cycles { $1 :: $2 }

cycle:
  | LPAREN numbers RPAREN { $2 }

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

fp_relator:
  | dan_term { $1 }
  | dan_term EQ dan_term { RelEq ($1, $3) }

fp_relators:
  | fp_relator { [$1] }
  | fp_relators COMMA fp_relator { $1 @ [$3] }
  | fp_relators fp_relator { $1 @ [$2] }
%%
