%{
open Syntax
%}

%token <string> IDENT
%token <string> STRING
%token MODULE WHERE IMPORT FUNCTOR DEF_TYPE DEF_TERM CHECK
%token COLON COLONEQ COMMA LPAREN RPAREN LBRACKET RBRACKET LANGLE RANGLE BAR TURNSTILE DOT AT OP
%token HOMLIT COENDLIT ENDLIT TENSORLIT FUNCLIT IDLIT JLIT JCOVLIT JCONTRALIT LET IN MIX LAMBDALIT EOF
%token UNIV REFL IDIR ZERO ONE LEQ SUBSETEQ JOIN MEET NEG FST SND TW PI0 PI1 EQ LBRACE RBRACE MULIT

%right FUNCLIT
%left TENSORLIT
%left JOIN
%left MEET
%nonassoc EQ LEQ SUBSETEQ
%nonassoc OP TW
%left AT
%left FST SND


%start file
%type <Syntax.cmd list> file

%%

file:
  | decls EOF { $1 }

decls:
  | /* empty */ { [] }
  | decl decls  { $1 :: $2 }

decl:
  | MODULE IDENT WHERE { CModule $2 }
  | IMPORT STRING { CImport $2 }
  | FUNCTOR IDENT LPAREN functor_args RPAREN COLON expr { CFunctor ($2, $4, $7) }
  | DEF_TYPE IDENT opt_params COLONEQ expr { CDefType ($2, $3, $5) }
  | DEF_TERM IDENT opt_params COLON expr COLONEQ expr { CDefTerm ($2, $3, $5, $7) }
  | CHECK delta BAR gamma TURNSTILE expr COLON expr { CCheck ($2, $4, $6, $8) }
  | CHECK delta TURNSTILE expr COLON expr { CCheckSimplicial ($2, $4, $6) }

functor_args:
  | functor_arg { [$1] }
  | functor_arg COMMA functor_args { $1 :: $3 }

functor_arg:
  | IDENT COLON expr { ($3, `Cov) }
  | IDENT COLON expr OP { ($3, `Contra) }

opt_params:
  | /* empty */ { [] }
  | LPAREN idents RPAREN { $2 }

idents:
  | IDENT { [$1] }
  | IDENT idents { $1 :: $2 }

expr:
  | simple_expr { $1 }
  | expr simple_expr %prec AT { EApp ($1, $2) }
  | expr AT expr { EModalApp ($1, $3) }
  | expr FUNCLIT expr { EFunc ($1, $3) }
  | expr TENSORLIT expr { ETensor ($1, $3) }
  | expr EQ expr { EId (EUniv, $1, $3) }
  | expr LEQ expr { ELeq ($1, $3) }
  | expr SUBSETEQ expr { EShapeInc ($1, $3) }
  | expr JOIN expr { EJoin ($1, $3) }
  | expr MEET expr { EMeet ($1, $3) }
  | NEG expr { ENeg ($2) }
  | expr OP { EOp $1 }
  | expr TW { ETw $1 }
  | expr FST { EFst $1 }
  | expr SND { ESnd $1 }

  | LPAREN IDENT COLON expr RPAREN FUNCLIT expr { EPi ($4, ($2, $7)) }
  | LPAREN IDENT COLON expr RPAREN TENSORLIT expr { ESig ($4, ($2, $7)) }
  | LAMBDALIT LPAREN IDENT COLON expr RPAREN DOT expr { ELam (($3, $5), $8) }
  | LAMBDALIT LPAREN IDENT RPAREN DOT expr { ELam (($3, EUniv), $6) }
  | MULIT LPAREN IDENT COLON expr RPAREN DOT expr { EModalPi ($5, ($3, $8)) }
  | LAMBDALIT OP LPAREN IDENT COLON expr RPAREN DOT expr { EModalLam (($4, $6), $9) }
  | COENDLIT LPAREN IDENT COLON expr RPAREN DOT expr { ECoend ($5, $3, $8) }
  | ENDLIT LPAREN IDENT COLON expr RPAREN DOT expr { EEnd ($5, $3, $8) }

  (* Primitive DTT / Compatibility term formers *)
  | HOMLIT LPAREN expr COMMA expr COMMA expr RPAREN { EHom ($3, $5, $7) }
  | IDLIT LPAREN expr RPAREN { EIdTerm $3 }
  | JLIT LPAREN IDENT DOT IDENT DOT expr COMMA IDENT COMMA expr COMMA expr COMMA expr COMMA expr RPAREN { EJ ($7, $3, $5, $9, $11, $13, $15, $17) }
  | JCOVLIT LPAREN IDENT DOT expr COMMA expr COMMA expr COMMA expr RPAREN { EJCov ($5, $3, $7, $9, $11) }
  | JCONTRALIT LPAREN IDENT DOT expr COMMA expr COMMA expr COMMA expr RPAREN { EJContra ($5, $3, $7, $9, $11) }
  | LET IDENT TENSORLIT IDENT COLONEQ expr IN expr { ETensorElim ($2, $4, $6, $8) }
  | MIX IDENT IDENT COLONEQ IDENT IN expr { ECoendIntro ($2, $3, $5, $7) }
  | LET LANGLE IDENT COMMA IDENT RANGLE COLONEQ expr IN expr { ECoendElim ($3, $5, $8, $10) }
  | LET LBRACKET IDENT COMMA IDENT RBRACKET COLONEQ expr IN expr { ECoendElim ($3, $5, $8, $10) }
  | ENDLIT LPAREN IDENT COMMA expr RPAREN { EEndIntro ($3, $5) }
  | LET IDENT IDENT AT IDENT COLONEQ expr IN expr { EEndElim ($2, $3, $5, $7, $9) }

simple_expr:
  | IDENT { EVar $1 }
  | UNIV { EUniv }
  | REFL { ERef (EVar "_") }
  | REFL LPAREN expr RPAREN { ERef $3 }
  | IDIR { EIDir }
  | ZERO { EZeroDir }
  | ONE { EOneDir }
  | LPAREN expr RPAREN { $2 }
  | LPAREN expr COMMA expr RPAREN { EPair ($2, $4) }
  | LBRACKET system_cases RBRACKET { ESystem $2 }
  | LBRACKET RBRACKET { ESystem [] }
  | LANGLE expr COMMA expr RANGLE { EPair ($2, $4) }
  | LBRACE IDENT COLON expr BAR expr BAR expr RBRACE { EExt ($4, $6, $8) }
  | FST LPAREN expr RPAREN { EFst $3 }
  | SND LPAREN expr RPAREN { ESnd $3 }
  | PI0 LPAREN expr RPAREN { ETwPi0 $3 }
  | PI1 LPAREN expr RPAREN { ETwPi1 $3 }

system_cases:
  | system_case { [$1] }
  | system_case system_cases { $1 :: $2 }

system_case:
  | LBRACKET expr BAR expr RBRACKET { ($2, $4) }

delta:
  | /* empty */ { [] }
  | delta_list { $1 }

delta_list:
  | delta_binding { [$1] }
  | delta_binding COMMA delta_list { $1 :: $3 }

delta_binding:
  | IDENT COLON expr { ($1, $3) }

gamma:
  | /* empty */ { [] }
  | gamma_list { $1 }

gamma_list:
  | gamma_binding { [$1] }
  | gamma_binding COMMA gamma_list { $1 :: $3 }

gamma_binding:
  | IDENT COLON expr { ($1, $3) }
