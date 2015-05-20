structure Core : CORE = 
struct

open ProtDom

type var = Id.id
type m = Id.id

datatype typ = UnitTyp 
	     | StringTyp 
	     | BoolTyp
	     | ArrTyp of typ*p*typ 
	     | AdvTyp of p 
	     | LabTyp of typ*p 
	     | PCTyp of typ*p 
	     | RefTyp of typ*p
	     | TupleTyp of typ list
	     | ObjTyp of (m*p*typ) list
	     | StackTyp
	     | IntTyp
	     | SockTyp
	     | FileTyp

type l = int
type r = int

datatype exp = 
	 UnitExp 
       | StringExp of string 
       | TrueExp
       | FalseExp
       | IfExp of exp * exp * exp
       | FunExp of p*var*typ*exp 
       | LabExp of l
       | RefExp of r
       | ObjExp of (m*typ*p*var*exp) list
       | VarExp of var
       | SeqExp of exp*exp 
       | PrintExp of exp 
       | AppExp of exp*exp
       | AdvExp of exp*var*p*exp 
       | AdvInstExp of exp 
       | NewExp of p*typ 
       | PCExp of exp*exp
       | NewRefExp of p * exp 
       | DerefExp of exp 
       | AssignExp of exp*exp 
       | LowerExp of p*exp
       | TupleExp of exp list
       | SplitExp of var list * exp * exp
       | LabSetExp of exp list * p
       | UnionExp of exp * p * exp
       | MembExp of exp * m
       | StackExp
       | NilStExp
       | PtStExp of exp * exp * exp
       | StoreExp of exp * exp * exp
       | CaseExp of exp * pat * exp * exp
       | ConcatExp of exp * exp
       | PlusExp of exp * exp
       | EqExp of exp * exp
       | GTExp of exp * exp
       | AbortExp of exp
       | IntExp of int
       | ItoSExp of exp
       | PosExp of Util.pos * exp
       | SocketExp of socket_type * exp
       | BindExp of exp
       | ListenExp of exp 
       | AcceptExp of exp
       | ConnectExp of exp
       | SendExp of exp
       | RecvExp of exp
       | SockExp of somesocket
       | NowExp of exp
       | OpenExp of open_type * exp
       | WriteExp of exp
       | ReadExp of exp 
       | DeleteExp of exp
       | RenameExp of exp
       | FileExp of somestream
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
       
and somesocket =
    SocketActive of (INetSock.inet, Socket.active Socket.stream) Socket.sock
  | SocketPassive of (INetSock.inet, Socket.passive Socket.stream) Socket.sock

and open_type = 
    Read
  | Write
  | Append
    
and somestream =
     FileRead of TextIO.instream 
   | FileWrite of TextIO.outstream

and pat =
    NilPat
  | PtPat of exp * var * pat
  | AllPat of pat
  | VarPat of var

and G = VarG of var*typ 
  | LabG of l*typ*p 
  | RefG of r*typ*p
	    
and A = AdvA of exp*var*p*exp
	   
and S = RefS of r*exp*p
  | LabS of l*typ*p


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
  | eq_typ (AdvTyp p) (AdvTyp p') =
    eq_prot p p'
  | eq_typ (LabTyp(t,p)) (LabTyp(t',p')) =
    eq_typ t t'
    andalso eq_prot p p'
  | eq_typ (PCTyp(t,p)) (PCTyp(t',p')) =
    eq_typ t t'
    andalso eq_prot p p'
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

