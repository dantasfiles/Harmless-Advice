signature CORE = 
sig

type p = Id.id
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

and G = VarG of var * typ 
  | LabG of l * typ * p 
  | RefG of r * typ * p
	    
and A = AdvA of exp*var*p*exp
	   
and S = RefS of r*exp*p
  | LabS of l * typ * p

val eq_typ : typ -> typ -> bool

end
