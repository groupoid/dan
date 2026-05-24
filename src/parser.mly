%{
open Dirtt
%}

%token <string> IDENT
%token <string> STRING
%token MODULE WHERE IMPORT FUNCTOR DEF_TYPE DEF_TERM CHECK
%token COLON COLONEQ COMMA LPAREN RPAREN LBRACKET RBRACKET LANGLE RANGLE BAR TURNSTILE DOT AT OP
%token HOMLIT COENDLIT ENDLIT TENSORLIT FUNCLIT IDLIT JLIT JCOVLIT JCONTRALIT LET IN MIX LAMBDALIT EOF

%right FUNCLIT
%left TENSORLIT
%nonassoc OP

%start file
%type <Dirtt.cmd list> file

%%

file:
  | decls EOF { $1 }

decls:
  | /* empty */ { [] }
  | decl decls  { $1 :: $2 }

decl:
  | MODULE IDENT WHERE { CModule $2 }
  | IMPORT STRING { CImport $2 }
  | FUNCTOR IDENT LPAREN functor_args RPAREN COLON cat { CFunctor ($2, $4, $7) }
  | DEF_TYPE IDENT opt_params COLONEQ m_type { CDefType ($2, $3, $5) }
  | DEF_TERM IDENT opt_params COLON m_type COLONEQ m_term { CDefTerm ($2, $3, $5, $7) }
  | CHECK delta BAR gamma TURNSTILE m_term COLON m_type { CCheck ($2, $4, $6, $8) }

functor_args:
  | functor_arg { [$1] }
  | functor_arg COMMA functor_args { $1 :: $3 }

functor_arg:
  | IDENT COLON cat { ($3, `Cov) }
  | IDENT COLON cat OP { ($3, `Contra) }

opt_params:
  | /* empty */ { [] }
  | LPAREN idents RPAREN { $2 }

idents:
  | IDENT { [$1] }
  | IDENT idents { $1 :: $2 }

cat:
  | IDENT { CVar $1 }
  | cat OP { COp $1 }
  | cat TENSORLIT cat { CProd ($1, $3) }
  | LPAREN cat RPAREN { $2 }

cat_term:
  | IDENT { CTVar $1 }
  | IDENT LPAREN cat_terms RPAREN { CTFun ($1, $3) }
  | cat_term OP { CTOp $1 }
  | LPAREN cat_term RPAREN { $2 }

cat_terms:
  | cat_term { [$1] }
  | cat_term COMMA cat_terms { $1 :: $3 }

m_type:
  | HOMLIT LPAREN cat COMMA cat_term COMMA cat_term RPAREN { MHom ($3, $5, $7) }
  | IDENT { MApp ($1, []) }
  | IDENT LPAREN cat_terms RPAREN { MApp ($1, $3) }
  | m_type TENSORLIT m_type { MTensor ($1, $3) }
  | COENDLIT LPAREN IDENT COLON cat RPAREN DOT m_type { MCoend ($5, $3, $8) }
  | ENDLIT LPAREN IDENT COLON cat RPAREN DOT m_type { MEnd ($5, $3, $8) }
  | m_type FUNCLIT m_type { MFunc ($1, $3) }
  | LPAREN m_type RPAREN { $2 }

m_term:
  | IDENT { MTVar $1 }
  | IDLIT LPAREN cat_term RPAREN { MTId $3 }
  | JLIT LPAREN IDENT DOT IDENT DOT m_type COMMA IDENT COMMA m_term COMMA cat_term COMMA cat_term COMMA m_term RPAREN { MTJ ($7, $3, $5, $9, $11, $13, $15, $17) }
  | JCOVLIT LPAREN IDENT DOT m_type COMMA m_term COMMA cat_term COMMA m_term RPAREN { MTJCov ($5, $3, $7, $9, $11) }
  | JCONTRALIT LPAREN IDENT DOT m_type COMMA m_term COMMA cat_term COMMA m_term RPAREN { MTJContra ($5, $3, $7, $9, $11) }
  | m_term TENSORLIT m_term { MTTensorIntro ($1, $3) }
  | LET IDENT TENSORLIT IDENT COLONEQ m_term IN m_term { MTTensorElim ($2, $4, $6, $8) }
  | MIX IDENT IDENT COLONEQ IDENT IN m_term { MTCoendIntro ($2, $3, $5, $7) }
  | LET LANGLE IDENT COMMA IDENT RANGLE COLONEQ m_term IN m_term { MTCoendElim ($3, $5, $8, $10) }
  | LET LBRACKET IDENT COMMA IDENT RBRACKET COLONEQ m_term IN m_term { MTCoendElim ($3, $5, $8, $10) }
  | ENDLIT LPAREN IDENT COMMA m_term RPAREN { MTEndIntro ($3, $5) }
  | LET IDENT IDENT AT IDENT COLONEQ m_term IN m_term { MTEndElim ($2, $3, $5, $7, $9) }
  | LAMBDALIT LPAREN IDENT COLON m_type RPAREN DOT m_term { MTFuncIntro ($3, $5, $8) }
  | m_term AT m_term { MTFuncElim ($1, $3) }
  | LPAREN m_term RPAREN { $2 }

delta:
  | /* empty */ { [] }
  | delta_list { $1 }

delta_list:
  | delta_binding { [$1] }
  | delta_binding COMMA delta_list { $1 :: $3 }

delta_binding:
  | IDENT COLON cat { ($1, $3) }

gamma:
  | /* empty */ { [] }
  | gamma_list { $1 }

gamma_list:
  | gamma_binding { [$1] }
  | gamma_binding COMMA gamma_list { $1 :: $3 }

gamma_binding:
  | IDENT COLON m_type { ($1, $3) }
