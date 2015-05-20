signature SOURCE =
sig

type p = Id.id
type var = Id.id
type m = Id.id

datatype typ = UnitTyp 
	     | StringTyp 
	     | BoolTyp
	     | ArrTyp of typ*p*typ 
	     | RefTyp of typ*p
	     | ObjTyp of (m*p*typ) list
	     | StackTyp
	     | IntTyp
	     | TupleTyp of typ list
	     | SockTyp 
	     | FileTyp
	      

datatype exp = 
    UnitExp 
  | StringExp of string
  | TrueExp
  | FalseExp
  | IfExp of exp * exp * exp
  | VarExp of var 
  | SeqExp of exp * exp 
  | PrintExp of exp 
  | DerefExp of exp 
  | AssignExp of exp * exp
  | MethExp of exp * m * exp
  | LetExp of dec list * exp
  | CaseExp of exp * pat * exp * exp
  | ConcatExp of exp * exp
  | PlusExp of exp * exp
  | EqExp of exp * exp
  | GTExp of exp * exp
  | AbortExp of exp
  | IntExp of int
  | ItoSExp of exp
  | PosExp of Util.pos * exp
  | TupleExp of exp list
  | SplitExp of var list * exp * exp
  | SocketExp of socket_type * exp
  | BindExp of exp
  | ListenExp of exp 
  | AcceptExp of exp
  | ConnectExp of exp
  | SendExp of exp
  | RecvExp of exp
  | NowExp of exp
  | OpenExp of open_type * exp
  | WriteExp of exp
  | ReadExp of exp 
  | DeleteExp of exp
  | RenameExp of exp
  | SizeExp of exp
  | SleepExp of exp
  | IndexOfExp of index_type * exp
  | SubstringExp of exp
  | ExistsExp of exp
  | MultExp of exp * exp
  | DivExp of exp * exp
  | NegExp of exp

and index_type = 
    First
  | Last

and socket_type =
    Active
  | Passive

and open_type =
    Read
  | Write
  | Append

and pat =
    NilPat
    | PtPat of (var * m) list * var * var * var * pat
    | AllPat of pat
    | VarPat of var

and dec = 
    BoolDec of var * exp
    | StringDec of var * exp
    | IntDec of var * exp
    | RefDec of var * typ * exp
    | ObjDec of var * (m*typ*var*var*typ*exp) list
    | AspDec of time * (var * m) list * var * var * var * var * exp
    | FileDec of var * exp
    | SockDec of var * exp
    | PosDec of Util.pos * dec
    
and time = 
    Before
  | After

and asp =
    Asp of p * dec list
    

and prog = 
    Prog of dec list * asp list * exp

and G = VarG of var*typ 

val eq_typ : typ -> typ -> bool

end
