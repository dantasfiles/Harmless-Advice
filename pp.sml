structure PrettyPrint :> PRETTYPRINT =
struct

structure C = Core
structure S = Source

fun ppList (h::t) =
    h ^ ppList t
  | ppList nil =
    ""

fun ppMeth m = 
    Id.id2string m

fun ppProt p = 
    Id.id2string p

fun ppVar v =
    Id.id2string v

fun ppCTyp C.UnitTyp =
    "unit"
  | ppCTyp C.StringTyp = 
    "string"
  | ppCTyp C.BoolTyp =
    "bool"
  | ppCTyp (C.ArrTyp(t1,p,t2)) =
    ppCTyp t1 ^ " ->" ^ ppProt p ^ " " ^ ppCTyp t2
  | ppCTyp (C.AdvTyp p) =
    "advice" ^ ppProt p
  | ppCTyp (C.LabTyp(t,p)) =
    ppCTyp t ^ " label_" ^ ppProt p
  | ppCTyp (C.PCTyp(t,p)) =
    ppCTyp t ^ " pc_" ^ ppProt p
  | ppCTyp (C.RefTyp(t,p)) =
    ppCTyp t ^ " ref_" ^ ppProt p
  | ppCTyp (C.TupleTyp(ts)) =
    "( " ^ ppList (map (fn(t) => ppCTyp t ^ " * ") ts) ^ " )"
  | ppCTyp (C.ObjTyp(mpts)) =
    "[ " ^ (*ppList (map (fn(m,p,t) => ppMeth m ^ " :" ^ ppProt p ^ " " ^ ppCTyp t ^ "," ) mpts) ^*) " ]"
  | ppCTyp C.StackTyp =
    "stack"
  | ppCTyp C.IntTyp = 
    "int"
  | ppCTyp C.SockTyp = 
    "sock"
  | ppCTyp C.FileTyp = 
    "file"

fun ppSS (C.SocketActive _) =
    "active"
  | ppSS (C.SocketPassive _) =
    "passive"

fun ppCExp C.UnitExp =
    "()"
  | ppCExp (C.StringExp s) =
    "\""^s^"\""
  | ppCExp C.TrueExp =
    "true"
  | ppCExp C.FalseExp =
    "false"
  | ppCExp (C.IfExp(e1,e2,e3)) =
    "if " ^ ppCExp e1 ^ " then " ^ ppCExp e2 ^ " else " ^ ppCExp e3
  | ppCExp (C.FunExp(p,x,t,e)) =
    "(\\" ^ ppProt p ^ " " ^ ppVar x ^ ":" ^ ppCTyp t ^ "." ^ ppCExp e ^ ")"
  | ppCExp (C.LabExp l) =
    "l" ^ Int.toString l
  | ppCExp (C.RefExp r) =
    "r" ^ Int.toString r
  | ppCExp (C.ObjExp(mtps)) =
    "[" ^ ppList (map (fn(m,t,p,x,e) => ppMeth m ^ ":" ^ ppCTyp t ^ " = \\" ^ ppProt p ^ " " ^ ppVar x ^ "." ^ ppCExp e ^ "," ) mtps)  ^ "]"
  | ppCExp (C.VarExp v) =
    ppVar v
  | ppCExp (C.SeqExp(e1,e2)) =
    ppCExp e1 ^ "; " ^ ppCExp e2
  | ppCExp (C.PrintExp e) =
    "print " ^ ppCExp e
  | ppCExp (C.AppExp(e1,e2)) =
    ppCExp e1 ^ " (" ^ ppCExp e2 ^ ")"
  | ppCExp (C.AdvExp(e1,x,p,e2)) =
    "{" ^ ppCExp e1 ^ "." ^ ppVar x ^ " ->" ^ ppProt p ^ " " ^ ppCExp e2
  | ppCExp (C.AdvInstExp e) =
    "=> " ^ ppCExp e
  | ppCExp (C.NewExp(p,t)) =
    "new_" ^ ppProt p ^ ":" ^ ppCTyp t
  | ppCExp (C.PCExp(e1,e2)) =
    ppCExp e1 ^ "[" ^ ppCExp e2 ^ "]"
  | ppCExp (C.NewRefExp(p,e)) =
    "new_" ^ ppProt p ^ " " ^ ppCExp e
  | ppCExp (C.DerefExp(e)) =
    "!" ^ ppCExp e
  | ppCExp (C.AssignExp(e1,e2)) =
    ppCExp e1 ^ " := " ^ ppCExp e2
  | ppCExp (C.LowerExp(p,e)) =
    ppProt p ^ "<" ^ ppCExp e ^ ">"
  | ppCExp (C.TupleExp(es)) =
    "(" ^ ppList (map (fn(e) => ppCExp e ^ ", ") es) ^ ")"
  | ppCExp (C.SplitExp(xs,e1,e2)) =
    "split " ^ ppList (map (fn(x) => ppVar x^",") xs) ^ " = " ^ ppCExp e1 ^ " in " ^ ppCExp e2 ^ " end"
  | ppCExp (C.LabSetExp(es,p)) =
    "{" ^ ppList (map (fn(e) => ppCExp e ^ ",") es) ^ "}" ^ ppProt p
  | ppCExp (C.UnionExp(e1,p,e2)) =
    ppCExp e1 ^ " U " ^ ppProt p ^ " " ^ ppCExp e2
  | ppCExp (C.MembExp(e,m)) =
    ppCExp e ^ "." ^ ppMeth m
  | ppCExp C.StackExp =
    "stack()"
  | ppCExp C.NilStExp =
    "nil"
  | ppCExp (C.PtStExp(e1,e2,e3)) =
    ppCExp e1 ^ "[" ^ ppCExp e2 ^ "]::" ^ ppCExp e3
  | ppCExp (C.StoreExp(e1,e2,e3)) =
    ppCExp e1 ^ "[" ^ ppCExp e2 ^ "] in " ^ ppCExp e3
  | ppCExp (C.CaseExp (e1, p, e2, e3)) =
    "case " ^ ppCExp e1 ^ " of ( "^ppCPat p ^ " => "^ppCExp e2 ^ " | _ => "^ ppCExp e3^" )"
  | ppCExp (C.ConcatExp (e1, e2)) =
    ppCExp e1 ^ " ^ " ^ ppCExp e2
  | ppCExp (C.PlusExp (e1, e2)) =
    ppCExp e1 ^ " + " ^ ppCExp e2
  | ppCExp (C.EqExp (e1, e2)) =
    ppCExp e1 ^ " == " ^ ppCExp e2
  | ppCExp (C.GTExp (e1, e2)) =
    ppCExp e1 ^ " > " ^ ppCExp e2
  | ppCExp (C.AbortExp e) =
    "abort " ^ ppCExp e
  | ppCExp (C.IntExp i) =
    "#" ^ Int.toString i
  | ppCExp (C.ItoSExp e) =
    "itos " ^ ppCExp e
  | ppCExp (C.PosExp (pos, e)) =
    ppCExp e (*"[" ^ Util.string_of_pos pos ^ "|" ^ ppCExp e^ "]"*)
  | ppCExp (C.SocketExp (st, e)) =
    "socket " ^ ppCExp e
  | ppCExp (C.BindExp e) =
    "bind " ^ ppCExp e
  | ppCExp (C.ListenExp e) =
    "listen " ^ ppCExp e
  | ppCExp (C.AcceptExp e) =
    "accept " ^ ppCExp e
  | ppCExp (C.ConnectExp e) =
    "connect " ^ ppCExp e
  | ppCExp (C.SendExp e) =
    "send " ^ ppCExp e
  | ppCExp (C.RecvExp e) =
    "recv " ^ ppCExp e
  | ppCExp (C.SockExp ss) =
    "sock" ^ ppSS ss
  | ppCExp (C.NowExp e) =
    "now " ^ ppCExp e
  | ppCExp (C.OpenExp (ot, e)) =
    "open " ^ ppCExp e
  | ppCExp (C.WriteExp e) =
    "write " ^ ppCExp e
  | ppCExp (C.ReadExp e) =
    "read " ^ ppCExp e
  | ppCExp (C.DeleteExp e) =
    "delete " ^ ppCExp e
  | ppCExp (C.RenameExp e) =
    "rename " ^ ppCExp e
  | ppCExp (C.FileExp _) = 
    "file"
  | ppCExp (C.SizeExp e) =
    "size " ^ ppCExp e
 | ppCExp (C.SleepExp e) =
    "sleep " ^ ppCExp e
 | ppCExp (C.IndexOfExp (_, e)) =
    "indexof " ^ ppCExp e
 | ppCExp (C.SubstringExp e) =
    "substring " ^ ppCExp e
 | ppCExp (C.ExistsExp e) =
    "exists " ^ ppCExp e
 | ppCExp (C.MultExp (e1, e2)) =
    ppCExp e1 ^ " * " ^ ppCExp e2
  | ppCExp (C.DivExp (e1, e2)) =
    ppCExp e1 ^ " / " ^ ppCExp e2
  | ppCExp (C.NegExp e) =
    "~" ^ ppCExp e

and ppCPat p =
    "unimplemented"

 
fun ppSTyp S.UnitTyp = 
    "unit"
  | ppSTyp S.StringTyp = 
    "string"
  | ppSTyp S.BoolTyp = 
    "bool"
  | ppSTyp (S.ArrTyp (t1, p, t2)) = 
    ppSTyp t1 ^ " -" ^ ppProt p ^ "> " ^ ppSTyp t2
  | ppSTyp (S.RefTyp (t, p)) = 
    "ref_" ^ ppProt p ^ " " ^ ppSTyp t
  | ppSTyp (S.ObjTyp(mpts)) =
    "[ " ^ ppList (map (fn(m,p,t) => ppMeth m ^ " :" ^ ppProt p ^ " " ^ ppSTyp t ^ "," ) mpts) ^ " ]"
  | ppSTyp S.StackTyp =
    "stack"
  | ppSTyp S.IntTyp =
    "int"
  | ppSTyp (S.TupleTyp ts) =
    "(" ^ ppList (map (fn(t) => ppSTyp t ^ "*") ts) ^ ")"
  | ppSTyp S.SockTyp =
    "sock"
  | ppSTyp S.FileTyp =
    "file"


end
    