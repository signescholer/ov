local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = (int*int)
type t__4__ = char*(int*int)
type t__5__ = (int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = (int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = (int*int)
type t__12__ = (int*int)
type t__13__ = (int*int)
type t__14__ = (int*int)
type t__15__ = (int*int)
type t__16__ = string*(int*int)
type t__17__ = (int*int)
type t__18__ = (int*int)
type t__19__ = (int*int)
type t__20__ = (int*int)
type t__21__ = (int*int)
type t__22__ = (int*int)
type t__23__ = (int*int)
type t__24__ = (int*int)
type t__25__ = (int*int)
type t__26__ = (int*int)
type t__27__ = (int*int)
type t__28__ = (int*int)
type t__29__ = (int*int)
type t__30__ = int*(int*int)
type t__31__ = (int*int)
type t__32__ = (int*int)
type t__33__ = (int*int)
type t__34__ = (int*int)
type t__35__ = (int*int)
type t__36__ = (int*int)
type t__37__ = (int*int)
type t__38__ = (int*int)
type t__39__ = (int*int)
type t__40__ = (int*int)
type t__41__ = string*(int*int)
type t__42__ = (int*int)
type t__43__ = (int*int)
type t__44__ = (int*int)
type t__45__ = (int*int)
in
datatype token =
    AND of t__1__
  | BOOL of t__2__
  | CHAR of t__3__
  | CHARLIT of t__4__
  | COMMA of t__5__
  | DEQ of t__6__
  | DIV of t__7__
  | ELSE of t__8__
  | EOF of t__9__
  | EQ of t__10__
  | FALSE of t__11__
  | FILTER of t__12__
  | FN of t__13__
  | FNEQ of t__14__
  | FUN of t__15__
  | ID of t__16__
  | IF of t__17__
  | IN of t__18__
  | INT of t__19__
  | IOTA of t__20__
  | LBRACKET of t__21__
  | LCURLY of t__22__
  | LET of t__23__
  | LPAR of t__24__
  | LTH of t__25__
  | MAP of t__26__
  | MINUS of t__27__
  | NEGATE of t__28__
  | NOT of t__29__
  | NUM of t__30__
  | OP of t__31__
  | OR of t__32__
  | PLUS of t__33__
  | RBRACKET of t__34__
  | RCURLY of t__35__
  | READ of t__36__
  | REDUCE of t__37__
  | REPLICATE of t__38__
  | RPAR of t__39__
  | SCAN of t__40__
  | STRINGLIT of t__41__
  | THEN of t__42__
  | TIMES of t__43__
  | TRUE of t__44__
  | WRITE of t__45__
end;

val Prog :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Fasto.UnknownTypes.Prog;
