structure Source :> SOURCE =
struct

open Util ProtDom

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
  | PosExp of pos * exp
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

and socket_type = Active | Passive
 
and open_type = Read | Write | Append

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
    | PosDec of pos * dec
    
and time = 
    Before
  | After

and asp =
    Asp of p * dec list
    

and prog = 
    Prog of dec list * asp list * exp

and G = VarG of var*typ 


fun eq_typ UnitTyp UnitTyp = 
    true
  | eq_typ StringTyp StringTyp = 
    true
  | eq_typ BoolTyp BoolTyp = 
    true
  | eq_typ (ArrTyp(t1,p,t2)) (ArrTyp(t1',p',t2')) =
    eq_typ t1 t1' 
    andalso eq_prot p p' 
    andalso eq_typ t2 t2'
  | eq_typ (RefTyp(t,p)) (RefTyp(t',p')) =
    eq_typ t t'
    andalso eq_prot p p'
  | eq_typ (TupleTyp ts) (TupleTyp ts') =
    eq_typ_list ts ts'
  | eq_typ (ObjTyp mpts) (ObjTyp mpts') =
    eq_mpt_list mpts mpts'
  | eq_typ StackTyp StackTyp =
    true
  | eq_typ IntTyp IntTyp =
    true
  | eq_typ SockTyp SockTyp =
    true
  | eq_typ FileTyp FileTyp =
    true
  | eq_typ _ _ =
    false

and eq_typ_list (t1::t1') (t2::t2') =
    eq_typ t1 t2
    andalso eq_typ_list t1' t2'
  | eq_typ_list nil nil =
    true
  | eq_typ_list _ _ = 
    false

and eq_mpt_list ((m1,p1,t1)::t1') ((m2,p2,t2)::t2') =
    Id.eqid m1 m2
    andalso eq_prot p1 p2
    andalso eq_typ t1 t2
    andalso eq_mpt_list t1' t2'
  | eq_mpt_list nil nil =
    true
  | eq_mpt_list _ _ =
    false



end
