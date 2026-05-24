type token =
  | IDENT of (
# 5 "src/parser.mly"
        string
# 6 "src/parser.ml"
)
  | STRING of (
# 6 "src/parser.mly"
        string
# 11 "src/parser.ml"
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

open Parsing
let _ = parse_error;;
# 2 "src/parser.mly"
open Dirtt
# 53 "src/parser.ml"
let yytransl_const = [|
  259 (* MODULE *);
  260 (* WHERE *);
  261 (* IMPORT *);
  262 (* FUNCTOR *);
  263 (* DEF_TYPE *);
  264 (* DEF_TERM *);
  265 (* CHECK *);
  266 (* COLON *);
  267 (* COLONEQ *);
  268 (* COMMA *);
  269 (* LPAREN *);
  270 (* RPAREN *);
  271 (* LBRACKET *);
  272 (* RBRACKET *);
  273 (* LANGLE *);
  274 (* RANGLE *);
  275 (* BAR *);
  276 (* TURNSTILE *);
  277 (* DOT *);
  278 (* AT *);
  279 (* OP *);
  280 (* HOMLIT *);
  281 (* COENDLIT *);
  282 (* ENDLIT *);
  283 (* TENSORLIT *);
  284 (* FUNCLIT *);
  285 (* IDLIT *);
  286 (* JLIT *);
  287 (* JCOVLIT *);
  288 (* JCONTRALIT *);
  289 (* LET *);
  290 (* IN *);
  291 (* MIX *);
  292 (* LAMBDALIT *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
  258 (* STRING *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\003\000\003\000\
\003\000\004\000\004\000\011\000\011\000\006\000\006\000\012\000\
\012\000\005\000\005\000\005\000\005\000\013\000\013\000\013\000\
\013\000\014\000\014\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\009\000\009\000\015\000\015\000\016\000\010\000\
\010\000\017\000\017\000\018\000\000\000"

let yylen = "\002\000\
\002\000\000\000\002\000\003\000\002\000\007\000\005\000\007\000\
\008\000\001\000\003\000\003\000\004\000\000\000\003\000\001\000\
\002\000\001\000\002\000\003\000\003\000\001\000\004\000\002\000\
\003\000\001\000\003\000\008\000\001\000\004\000\003\000\008\000\
\008\000\003\000\003\000\001\000\004\000\018\000\012\000\012\000\
\003\000\008\000\007\000\010\000\010\000\006\000\009\000\008\000\
\003\000\003\000\000\000\001\000\001\000\003\000\003\000\000\000\
\001\000\001\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\061\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\
\000\000\000\000\052\000\000\000\001\000\003\000\004\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\018\000\000\000\000\000\
\000\000\000\000\057\000\000\000\054\000\000\000\000\000\000\000\
\017\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\019\000\000\000\000\000\000\000\000\000\000\000\
\000\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\021\000\000\000\000\000\036\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\059\000\000\000\000\000\000\000\000\000\000\000\000\000\035\000\
\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\000\
\030\000\000\000\000\000\000\000\050\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\025\000\027\000\000\000\000\000\
\000\000\000\000\037\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\028\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\039\000\040\000\000\000\000\000\000\000\000\000\
\000\000\038\000"

let yydgoto = "\002\000\
\009\000\010\000\011\000\032\000\040\000\026\000\056\000\088\000\
\018\000\042\000\033\000\035\000\094\000\095\000\019\000\020\000\
\043\000\044\000"

let yysindex = "\007\000\
\201\255\000\000\072\255\133\255\149\255\171\255\204\255\211\255\
\000\000\066\000\201\255\153\255\000\000\202\255\203\255\203\255\
\207\255\195\255\000\000\206\255\000\000\000\000\000\000\218\255\
\219\255\210\255\212\255\003\255\223\255\211\255\213\255\214\255\
\215\255\219\255\216\255\012\255\012\255\000\000\003\255\148\255\
\221\255\205\255\000\000\220\255\000\000\003\255\224\255\218\255\
\000\000\000\000\225\255\012\255\226\255\227\255\228\255\095\255\
\251\254\055\255\000\000\003\255\012\255\032\255\223\255\172\255\
\003\255\000\000\028\255\075\255\003\255\232\255\234\255\012\255\
\012\255\032\255\000\000\229\255\095\255\000\000\032\255\230\255\
\231\255\233\255\235\255\236\255\002\255\241\255\237\255\005\255\
\000\000\000\000\148\255\238\255\028\255\084\255\240\255\000\000\
\019\255\243\255\245\255\000\000\095\255\170\255\026\255\244\255\
\028\255\246\255\255\255\002\000\001\255\004\000\021\000\023\000\
\025\000\012\255\032\255\032\255\028\255\029\255\028\255\000\000\
\000\000\028\255\003\255\003\255\000\000\035\000\085\255\208\255\
\247\255\028\000\029\000\069\000\060\000\062\000\089\000\248\255\
\095\255\170\255\079\000\088\000\000\000\000\000\097\255\115\255\
\126\255\032\255\000\000\102\000\012\255\012\255\105\000\097\000\
\124\000\126\000\128\000\012\255\000\000\028\255\084\000\109\000\
\138\255\152\000\048\255\065\255\175\000\032\255\119\000\162\000\
\192\255\091\255\180\255\012\255\012\255\000\000\012\255\032\255\
\032\255\032\255\064\255\177\000\178\000\032\255\166\000\000\000\
\095\255\095\255\067\255\027\255\088\255\146\255\032\255\032\255\
\032\255\170\255\032\255\189\000\028\255\028\255\032\255\170\255\
\155\255\159\255\170\255\179\000\113\255\125\255\170\255\032\255\
\032\255\032\255\032\255\032\255\170\255\170\255\094\255\140\255\
\152\255\028\255\000\000\000\000\178\255\028\255\179\255\032\255\
\156\255\000\000"

let yyrindex = "\000\000\
\236\000\000\000\000\000\000\000\000\000\000\000\000\000\173\000\
\000\000\000\000\236\000\000\000\000\000\000\000\182\000\184\000\
\000\000\000\000\000\000\180\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\181\000\000\000\000\000\000\000\
\183\000\186\000\000\000\000\000\000\000\000\000\000\000\249\254\
\000\000\000\000\000\000\185\000\000\000\000\000\000\000\000\000\
\000\000\000\000\104\000\000\000\000\000\000\000\000\000\090\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\186\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\114\000\254\254\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\060\255\161\000\173\255\000\000\188\000\000\000\000\000\
\000\000\000\000\000\000\000\000\131\000\169\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\176\000\011\000\001\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\141\000\151\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\024\000\000\000\000\000\000\000\000\000\000\000\034\000\
\000\000\000\000\047\000\000\000\000\000\000\000\057\000\000\000\
\000\000\000\000\000\000\000\000\070\000\080\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\226\000\000\000\209\000\217\255\179\001\239\255\191\255\
\000\000\000\000\000\000\162\001\222\255\094\000\168\001\000\000\
\140\001\000\000"

let yytablesize = 461
let yytable = "\058\000\
\041\000\131\000\109\000\038\000\055\000\074\000\064\000\001\000\
\102\000\060\000\049\000\055\000\051\000\103\000\114\000\039\000\
\110\000\060\000\111\000\057\000\076\000\072\000\073\000\043\000\
\052\000\091\000\115\000\132\000\092\000\097\000\122\000\116\000\
\078\000\042\000\068\000\053\000\054\000\055\000\197\000\125\000\
\093\000\059\000\141\000\077\000\079\000\060\000\048\000\115\000\
\115\000\138\000\139\000\120\000\116\000\116\000\100\000\101\000\
\047\000\080\000\118\000\176\000\081\000\082\000\083\000\084\000\
\085\000\021\000\086\000\087\000\075\000\045\000\127\000\013\000\
\012\000\013\000\072\000\073\000\177\000\059\000\196\000\044\000\
\161\000\060\000\019\000\144\000\145\000\115\000\019\000\143\000\
\096\000\007\000\116\000\072\000\073\000\072\000\073\000\119\000\
\137\000\191\000\147\000\198\000\179\000\072\000\073\000\029\000\
\183\000\218\000\120\000\120\000\158\000\115\000\188\000\189\000\
\190\000\020\000\116\000\115\000\194\000\072\000\073\000\120\000\
\116\000\072\000\073\000\171\000\211\000\200\000\201\000\202\000\
\159\000\203\000\034\000\163\000\164\000\207\000\013\000\120\000\
\212\000\059\000\170\000\160\000\032\000\060\000\213\000\214\000\
\215\000\216\000\217\000\120\000\059\000\014\000\033\000\174\000\
\060\000\219\000\185\000\186\000\023\000\187\000\225\000\115\000\
\006\000\115\000\205\000\206\000\116\000\220\000\116\000\115\000\
\008\000\226\000\059\000\015\000\116\000\115\000\060\000\009\000\
\115\000\115\000\116\000\199\000\115\000\116\000\116\000\221\000\
\022\000\116\000\022\000\223\000\208\000\222\000\224\000\115\000\
\209\000\184\000\090\000\022\000\116\000\012\000\060\000\012\000\
\120\000\120\000\120\000\003\000\016\000\004\000\005\000\006\000\
\007\000\008\000\140\000\017\000\142\000\029\000\024\000\025\000\
\028\000\030\000\031\000\034\000\036\000\037\000\046\000\041\000\
\062\000\182\000\048\000\047\000\148\000\050\000\061\000\063\000\
\098\000\065\000\099\000\002\000\022\000\067\000\069\000\070\000\
\071\000\112\000\104\000\105\000\126\000\106\000\128\000\107\000\
\108\000\113\000\117\000\059\000\123\000\121\000\124\000\129\000\
\066\000\156\000\130\000\041\000\133\000\041\000\041\000\041\000\
\041\000\041\000\041\000\149\000\041\000\049\000\041\000\049\000\
\049\000\049\000\049\000\049\000\049\000\134\000\049\000\135\000\
\049\000\136\000\043\000\041\000\043\000\043\000\043\000\043\000\
\043\000\043\000\041\000\043\000\042\000\043\000\042\000\042\000\
\042\000\042\000\042\000\042\000\049\000\042\000\146\000\042\000\
\150\000\048\000\151\000\048\000\048\000\048\000\048\000\048\000\
\048\000\043\000\048\000\047\000\048\000\047\000\047\000\047\000\
\047\000\047\000\047\000\042\000\047\000\152\000\047\000\153\000\
\045\000\154\000\045\000\045\000\045\000\045\000\045\000\045\000\
\048\000\045\000\044\000\045\000\044\000\044\000\044\000\044\000\
\044\000\044\000\047\000\044\000\007\000\044\000\007\000\007\000\
\007\000\007\000\007\000\155\000\115\000\157\000\162\000\045\000\
\172\000\165\000\029\000\166\000\029\000\029\000\029\000\029\000\
\029\000\044\000\029\000\029\000\020\000\029\000\020\000\020\000\
\020\000\020\000\020\000\029\000\167\000\020\000\168\000\020\000\
\169\000\173\000\029\000\029\000\020\000\034\000\180\000\034\000\
\034\000\034\000\034\000\034\000\020\000\034\000\034\000\032\000\
\034\000\032\000\032\000\032\000\032\000\032\000\034\000\032\000\
\032\000\033\000\032\000\033\000\033\000\033\000\033\000\033\000\
\032\000\033\000\033\000\006\000\033\000\006\000\006\000\006\000\
\006\000\006\000\033\000\008\000\175\000\008\000\008\000\008\000\
\008\000\008\000\009\000\181\000\009\000\009\000\009\000\009\000\
\009\000\178\000\195\000\192\000\193\000\204\000\210\000\051\000\
\014\000\014\000\027\000\049\000\010\000\045\000\053\000\016\000\
\056\000\026\000\089\000\000\000\058\000"

let yycheck = "\039\000\
\000\000\001\001\001\001\001\001\012\001\011\001\046\000\001\000\
\074\000\012\001\000\000\019\001\001\001\079\000\010\001\013\001\
\015\001\020\001\017\001\037\000\060\000\027\001\028\001\000\000\
\013\001\065\000\022\001\027\001\001\001\069\000\012\001\027\001\
\001\001\000\000\052\000\024\001\025\001\026\001\012\001\014\001\
\013\001\023\001\014\001\061\000\013\001\027\001\000\000\022\001\
\022\001\115\000\116\000\023\001\027\001\027\001\072\000\073\000\
\000\000\026\001\093\000\012\001\029\001\030\001\031\001\032\001\
\033\001\000\000\035\001\036\001\014\001\000\000\105\000\012\001\
\001\001\014\001\027\001\028\001\012\001\023\001\012\001\000\000\
\146\000\027\001\023\001\123\000\124\000\022\001\027\001\122\000\
\014\001\000\000\027\001\027\001\028\001\027\001\028\001\012\001\
\114\000\034\001\014\001\012\001\166\000\027\001\028\001\000\000\
\014\001\012\001\023\001\023\001\012\001\022\001\176\000\177\000\
\178\000\000\000\027\001\022\001\182\000\027\001\028\001\023\001\
\027\001\027\001\028\001\158\000\012\001\191\000\192\000\193\000\
\014\001\195\000\000\000\149\000\150\000\199\000\002\001\023\001\
\012\001\023\001\156\000\014\001\000\000\027\001\208\000\209\000\
\210\000\211\000\212\000\023\001\023\001\001\001\000\000\014\001\
\027\001\014\001\172\000\173\000\004\001\175\000\224\000\022\001\
\000\000\022\001\197\000\198\000\027\001\014\001\027\001\022\001\
\000\000\014\001\023\001\001\001\027\001\022\001\027\001\000\000\
\022\001\022\001\027\001\034\001\022\001\027\001\027\001\218\000\
\012\001\027\001\014\001\222\000\034\001\012\001\012\001\022\001\
\034\001\014\001\023\001\023\001\027\001\012\001\027\001\014\001\
\023\001\023\001\023\001\003\001\001\001\005\001\006\001\007\001\
\008\001\009\001\117\000\001\001\119\000\019\001\013\001\013\001\
\010\001\012\001\001\001\001\001\011\001\010\001\010\001\001\001\
\020\001\034\001\012\001\014\001\021\001\014\001\010\001\012\001\
\001\001\010\001\001\001\000\000\011\000\013\001\013\001\013\001\
\013\001\001\001\013\001\013\001\001\001\013\001\001\001\013\001\
\013\001\013\001\013\001\023\001\010\001\014\001\010\001\001\001\
\048\000\010\001\001\001\003\001\001\001\005\001\006\001\007\001\
\008\001\009\001\010\001\021\001\012\001\003\001\014\001\005\001\
\006\001\007\001\008\001\009\001\010\001\001\001\012\001\001\001\
\014\001\001\001\003\001\027\001\005\001\006\001\007\001\008\001\
\009\001\010\001\034\001\012\001\003\001\014\001\005\001\006\001\
\007\001\008\001\009\001\010\001\034\001\012\001\012\001\014\001\
\021\001\003\001\022\001\005\001\006\001\007\001\008\001\009\001\
\010\001\034\001\012\001\003\001\014\001\005\001\006\001\007\001\
\008\001\009\001\010\001\034\001\012\001\001\001\014\001\012\001\
\003\001\012\001\005\001\006\001\007\001\008\001\009\001\010\001\
\034\001\012\001\003\001\014\001\005\001\006\001\007\001\008\001\
\009\001\010\001\034\001\012\001\003\001\014\001\005\001\006\001\
\007\001\008\001\009\001\011\001\022\001\014\001\001\001\034\001\
\021\001\001\001\003\001\011\001\005\001\006\001\007\001\008\001\
\009\001\034\001\011\001\012\001\003\001\014\001\005\001\006\001\
\007\001\008\001\009\001\020\001\001\001\012\001\001\001\014\001\
\001\001\021\001\027\001\028\001\019\001\003\001\016\001\005\001\
\006\001\007\001\008\001\009\001\027\001\011\001\012\001\003\001\
\014\001\005\001\006\001\007\001\008\001\009\001\020\001\011\001\
\012\001\003\001\014\001\005\001\006\001\007\001\008\001\009\001\
\020\001\011\001\012\001\003\001\014\001\005\001\006\001\007\001\
\008\001\009\001\020\001\003\001\021\001\005\001\006\001\007\001\
\008\001\009\001\003\001\018\001\005\001\006\001\007\001\008\001\
\009\001\011\001\021\001\011\001\011\001\001\001\012\001\019\001\
\011\001\010\001\016\000\034\000\014\001\030\000\019\001\014\001\
\020\001\014\001\063\000\255\255\020\001"

let yynames_const = "\
  MODULE\000\
  WHERE\000\
  IMPORT\000\
  FUNCTOR\000\
  DEF_TYPE\000\
  DEF_TERM\000\
  CHECK\000\
  COLON\000\
  COLONEQ\000\
  COMMA\000\
  LPAREN\000\
  RPAREN\000\
  LBRACKET\000\
  RBRACKET\000\
  LANGLE\000\
  RANGLE\000\
  BAR\000\
  TURNSTILE\000\
  DOT\000\
  AT\000\
  OP\000\
  HOMLIT\000\
  COENDLIT\000\
  ENDLIT\000\
  TENSORLIT\000\
  FUNCLIT\000\
  IDLIT\000\
  JLIT\000\
  JCOVLIT\000\
  JCONTRALIT\000\
  LET\000\
  IN\000\
  MIX\000\
  LAMBDALIT\000\
  EOF\000\
  "

let yynames_block = "\
  IDENT\000\
  STRING\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decls) in
    Obj.repr(
# 21 "src/parser.mly"
              ( _1 )
# 391 "src/parser.ml"
               : Dirtt.cmd list))
; (fun __caml_parser_env ->
    Obj.repr(
# 24 "src/parser.mly"
                ( [] )
# 397 "src/parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 25 "src/parser.mly"
                ( _1 :: _2 )
# 405 "src/parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 28 "src/parser.mly"
                       ( CModule _2 )
# 412 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 29 "src/parser.mly"
                  ( CImport _2 )
# 419 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'functor_args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'cat) in
    Obj.repr(
# 30 "src/parser.mly"
                                                       ( CFunctor (_2, _4, _7) )
# 428 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'opt_params) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 31 "src/parser.mly"
                                             ( CDefType (_2, _3, _5) )
# 437 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'opt_params) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'm_type) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 32 "src/parser.mly"
                                                          ( CDefTerm (_2, _3, _5, _7) )
# 447 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'delta) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'gamma) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 33 "src/parser.mly"
                                                        ( CCheck (_2, _4, _6, _8) )
# 457 "src/parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'functor_arg) in
    Obj.repr(
# 36 "src/parser.mly"
                ( [_1] )
# 464 "src/parser.ml"
               : 'functor_args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'functor_arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'functor_args) in
    Obj.repr(
# 37 "src/parser.mly"
                                   ( _1 :: _3 )
# 472 "src/parser.ml"
               : 'functor_args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cat) in
    Obj.repr(
# 40 "src/parser.mly"
                    ( (_3, `Cov) )
# 480 "src/parser.ml"
               : 'functor_arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'cat) in
    Obj.repr(
# 41 "src/parser.mly"
                       ( (_3, `Contra) )
# 488 "src/parser.ml"
               : 'functor_arg))
; (fun __caml_parser_env ->
    Obj.repr(
# 44 "src/parser.mly"
                ( [] )
# 494 "src/parser.ml"
               : 'opt_params))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'idents) in
    Obj.repr(
# 45 "src/parser.mly"
                         ( _2 )
# 501 "src/parser.ml"
               : 'opt_params))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 48 "src/parser.mly"
          ( [_1] )
# 508 "src/parser.ml"
               : 'idents))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'idents) in
    Obj.repr(
# 49 "src/parser.mly"
                 ( _1 :: _2 )
# 516 "src/parser.ml"
               : 'idents))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 52 "src/parser.mly"
          ( CVar _1 )
# 523 "src/parser.ml"
               : 'cat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'cat) in
    Obj.repr(
# 53 "src/parser.mly"
           ( COp _1 )
# 530 "src/parser.ml"
               : 'cat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'cat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cat) in
    Obj.repr(
# 54 "src/parser.mly"
                      ( CProd (_1, _3) )
# 538 "src/parser.ml"
               : 'cat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cat) in
    Obj.repr(
# 55 "src/parser.mly"
                      ( _2 )
# 545 "src/parser.ml"
               : 'cat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 58 "src/parser.mly"
          ( CTVar _1 )
# 552 "src/parser.ml"
               : 'cat_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'cat_terms) in
    Obj.repr(
# 59 "src/parser.mly"
                                  ( CTFun (_1, _3) )
# 560 "src/parser.ml"
               : 'cat_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'cat_term) in
    Obj.repr(
# 60 "src/parser.mly"
                ( CTOp _1 )
# 567 "src/parser.ml"
               : 'cat_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cat_term) in
    Obj.repr(
# 61 "src/parser.mly"
                           ( _2 )
# 574 "src/parser.ml"
               : 'cat_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cat_term) in
    Obj.repr(
# 64 "src/parser.mly"
             ( [_1] )
# 581 "src/parser.ml"
               : 'cat_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'cat_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cat_terms) in
    Obj.repr(
# 65 "src/parser.mly"
                             ( _1 :: _3 )
# 589 "src/parser.ml"
               : 'cat_terms))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'cat) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'cat_term) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'cat_term) in
    Obj.repr(
# 68 "src/parser.mly"
                                                           ( MHom (_3, _5, _7) )
# 598 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 69 "src/parser.mly"
          ( MApp (_1, []) )
# 605 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'cat_terms) in
    Obj.repr(
# 70 "src/parser.mly"
                                  ( MApp (_1, _3) )
# 613 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'm_type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 71 "src/parser.mly"
                            ( MTensor (_1, _3) )
# 621 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'cat) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 72 "src/parser.mly"
                                                      ( MCoend (_5, _3, _8) )
# 630 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'cat) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 73 "src/parser.mly"
                                                    ( MEnd (_5, _3, _8) )
# 639 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'm_type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 74 "src/parser.mly"
                          ( MFunc (_1, _3) )
# 647 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'm_type) in
    Obj.repr(
# 75 "src/parser.mly"
                         ( _2 )
# 654 "src/parser.ml"
               : 'm_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 78 "src/parser.mly"
          ( MTVar _1 )
# 661 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'cat_term) in
    Obj.repr(
# 79 "src/parser.mly"
                                 ( MTId _3 )
# 668 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 15 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 13 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 11 : 'm_type) in
    let _9 = (Parsing.peek_val __caml_parser_env 9 : string) in
    let _11 = (Parsing.peek_val __caml_parser_env 7 : 'm_term) in
    let _13 = (Parsing.peek_val __caml_parser_env 5 : 'cat_term) in
    let _15 = (Parsing.peek_val __caml_parser_env 3 : 'cat_term) in
    let _17 = (Parsing.peek_val __caml_parser_env 1 : 'm_term) in
    Obj.repr(
# 80 "src/parser.mly"
                                                                                                                      ( MTJ (_7, _3, _5, _9, _11, _13, _15, _17) )
# 682 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 9 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 7 : 'm_type) in
    let _7 = (Parsing.peek_val __caml_parser_env 5 : 'm_term) in
    let _9 = (Parsing.peek_val __caml_parser_env 3 : 'cat_term) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'm_term) in
    Obj.repr(
# 81 "src/parser.mly"
                                                                                    ( MTJCov (_5, _3, _7, _9, _11) )
# 693 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 9 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 7 : 'm_type) in
    let _7 = (Parsing.peek_val __caml_parser_env 5 : 'm_term) in
    let _9 = (Parsing.peek_val __caml_parser_env 3 : 'cat_term) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'm_term) in
    Obj.repr(
# 82 "src/parser.mly"
                                                                                       ( MTJContra (_5, _3, _7, _9, _11) )
# 704 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 83 "src/parser.mly"
                            ( MTTensorIntro (_1, _3) )
# 712 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 84 "src/parser.mly"
                                                       ( MTTensorElim (_2, _4, _6, _8) )
# 722 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 85 "src/parser.mly"
                                            ( MTCoendIntro (_2, _3, _5, _7) )
# 732 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _10 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 86 "src/parser.mly"
                                                                 ( MTCoendElim (_3, _5, _8, _10) )
# 742 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _10 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 87 "src/parser.mly"
                                                                     ( MTCoendElim (_3, _5, _8, _10) )
# 752 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'm_term) in
    Obj.repr(
# 88 "src/parser.mly"
                                            ( MTEndIntro (_3, _5) )
# 760 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 89 "src/parser.mly"
                                                      ( MTEndElim (_2, _3, _5, _7, _9) )
# 771 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'm_type) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 90 "src/parser.mly"
                                                          ( MTFuncIntro (_3, _5, _8) )
# 780 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'm_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'm_term) in
    Obj.repr(
# 91 "src/parser.mly"
                     ( MTFuncElim (_1, _3) )
# 788 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'm_term) in
    Obj.repr(
# 92 "src/parser.mly"
                         ( _2 )
# 795 "src/parser.ml"
               : 'm_term))
; (fun __caml_parser_env ->
    Obj.repr(
# 95 "src/parser.mly"
                ( [] )
# 801 "src/parser.ml"
               : 'delta))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'delta_list) in
    Obj.repr(
# 96 "src/parser.mly"
               ( _1 )
# 808 "src/parser.ml"
               : 'delta))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'delta_binding) in
    Obj.repr(
# 99 "src/parser.mly"
                  ( [_1] )
# 815 "src/parser.ml"
               : 'delta_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'delta_binding) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'delta_list) in
    Obj.repr(
# 100 "src/parser.mly"
                                   ( _1 :: _3 )
# 823 "src/parser.ml"
               : 'delta_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cat) in
    Obj.repr(
# 103 "src/parser.mly"
                    ( (_1, _3) )
# 831 "src/parser.ml"
               : 'delta_binding))
; (fun __caml_parser_env ->
    Obj.repr(
# 106 "src/parser.mly"
                ( [] )
# 837 "src/parser.ml"
               : 'gamma))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'gamma_list) in
    Obj.repr(
# 107 "src/parser.mly"
               ( _1 )
# 844 "src/parser.ml"
               : 'gamma))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'gamma_binding) in
    Obj.repr(
# 110 "src/parser.mly"
                  ( [_1] )
# 851 "src/parser.ml"
               : 'gamma_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'gamma_binding) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'gamma_list) in
    Obj.repr(
# 111 "src/parser.mly"
                                   ( _1 :: _3 )
# 859 "src/parser.ml"
               : 'gamma_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'm_type) in
    Obj.repr(
# 114 "src/parser.mly"
                       ( (_1, _3) )
# 867 "src/parser.ml"
               : 'gamma_binding))
(* Entry file *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let file (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Dirtt.cmd list)
