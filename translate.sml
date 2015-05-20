structure Translate :> TRANSLATE =
struct

open Core ProtDom PrettyPrint Util
structure S = Source

datatype P = PointP of var * m * S.typ * S.typ * S.typ * p * var * var

exception TransError of string

fun not_eq t1 t2 = 
    ppSTyp t1 ^ " != " ^ ppSTyp t2

fun not_prot_eq p1 p2 = 
    ppProt p1 ^ " != " ^ ppProt p2

fun trans_err pos s = 
  raise (TransError ("Position " ^ string_of_pos pos ^ ": " ^ s)) 

fun LetExp(p,x,t:typ,e1:exp,e2:exp) = AppExp(FunExp(p,x,t,e2), e1)

val main_prot = Id.makeid "main"

fun create_lattice (S.Asp(p,decs)::t) =
    add_prot (create_lattice t) p main_prot
  | create_lattice nil =
    empty_prot

fun lookupVarG(v, S.VarG(var,typ)::G) = if Id.eqid v var
				      then typ 
				      else lookupVarG(v,G)
  | lookupVarG(v,_) = raise TransError ("lookupVarG: Cannot find variable " ^ PrettyPrint.ppVar v)


fun transOT S.Read = Read
  | transOT S.Write = Write
  | transOT S.Append = Append

fun transIOT S.First = First
  | transIOT S.Last = Last

fun transST S.Active = Active
  | transST S.Passive = Passive

fun transTyp S.UnitTyp = 
    UnitTyp
  | transTyp S.StringTyp = 
    StringTyp
  | transTyp S.BoolTyp = 
    BoolTyp
  | transTyp (S.ArrTyp(t1, p, t2)) = 
    ArrTyp(transTyp t1, p, transTyp t2)
  | transTyp (S.RefTyp(t, p)) = 
    RefTyp (transTyp t, p)
  | transTyp (S.ObjTyp mpts) = 
    ObjTyp (map (fn(m,p,t) => (m,p,transTyp t)) mpts)
  | transTyp S.StackTyp =
    StackTyp
  | transTyp S.IntTyp =
    IntTyp
  | transTyp (S.TupleTyp ts) =
    TupleTyp (map transTyp ts)
  | transTyp S.SockTyp =
    SockTyp
  | transTyp S.FileTyp =
    FileTyp

and transExp pos latt P G p =
    let 
	fun transExp' S.UnitExp = 
	    (S.UnitTyp, UnitExp)
	  | transExp' (S.StringExp s) = 
	    (S.StringTyp, StringExp s)
	  | transExp' S.TrueExp = 
	    (S.BoolTyp, TrueExp)
	  | transExp' S.FalseExp = 
	    (S.BoolTyp, FalseExp)
	  | transExp' (S.IfExp(e1,e2,e3)) =
	    let 
		val (t1,e1') = transExp' e1
		val (t2,e2') = transExp' e2
		val (t3,e3') = transExp' e3
	    in 
		if (S.eq_typ t1 S.BoolTyp)
		then (if (S.eq_typ t2 t3)
		      then (t2, IfExp(e1', e2', e3'))
		      else trans_err pos ("IfExp: " ^ not_eq t2 t3))
		else trans_err pos ("IfExp: " ^ not_eq t1 S.BoolTyp)
	    end
	  | transExp' (S.VarExp x) = 
	    (lookupVarG(x,G), VarExp x)
	  | transExp' (S.SeqExp(e1,e2)) = 
	    let 
		val (t1,e1') = transExp' e1
		val (t2,e2') = transExp' e2
	    in
		(*if S.eq_typ t1 S.UnitTyp
		then*) (t2, SeqExp(e1',e2'))
		(*else trans_err pos ("SeqExp: " ^ not_eq t1 S.UnitTyp)*)
	    end
	  | transExp' (S.PrintExp e) =
	    let
		val (t,e') = transExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.UnitTyp, PrintExp(e'))
		else trans_err pos ("PrintExp: " ^ not_eq t S.StringTyp)
	    end
	  | transExp' (S.DerefExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		case t of
		    S.RefTyp(t',p') => if (leq_prot latt p p')
				       then (t', DerefExp(e'))
				       else trans_err pos "DerefExp: bad protection domains"
		  | _ => trans_err pos ("DerefExp: " ^ (ppSTyp t) ^ " is not a ref")
	    end
	  | transExp' (S.AssignExp(e1,e2)) =
	    let 
		val (t1,e1') = transExp' e1
		val (t2,e2') = transExp' e2
	    in
		case t1 of
		    S.RefTyp(t1', p') => if (S.eq_typ t1' t2)
					 then (if (leq_prot latt p' p)
					       then (t2, AssignExp(e1',e2'))
					       else trans_err pos "AssignExp: bad rotection domains")
					 else trans_err pos ("AssignExp: " ^ not_eq t1' t2)
		  | _ => raise trans_err pos ("AssignExp: " ^ (ppSTyp t1) ^ " is not a ref")
	    end
	  | transExp' (S.MethExp(e1,m,e2)) =
	    let 
		val (t1,e1') = transExp' e1
		val (t2,e2') = transExp' e2
	    in
		case t1 of 
		    S.ObjTyp(mlist) => 
		    (case List.find (fn(m',p',t) => (Id.eqid m' m)) mlist of
			 SOME (m', p', t) => 
			 (case t of 
			      S.ArrTyp(t1',p'', t2') =>
			      if ProtDom.eq_prot p' p''
			      then (if ProtDom.eq_prot p p'
				    then (if S.eq_typ t1' t2
					  then (t2', AppExp(MembExp(e1',m), e2'))
					  else trans_err pos ("MethExp: " ^ not_eq t1' t2))
				    else trans_err pos ("MethExp1: " ^ not_prot_eq p p'))
			      else trans_err pos ("MethExp2: " ^ not_prot_eq p' p'')
			    | _ => trans_err pos ("MethExp:" ^ ppSTyp t ^ " not array type"))
		       | NONE => trans_err pos "MethExp: no such method")
		  | _ => trans_err pos ("MethExp: " ^ ppSTyp t1 ^ " not object type")
	    end
	  | transExp' (S.LetExp(decs, e)) =
	    transDec pos latt P G p decs nil e
	  | transExp' (S.CaseExp(e1, pat, e2, e3)) =
	    let
		val (t1,e1') = transExp' e1
		val (pat', G', T) = transPat pos latt P p pat
		val (t2,e2') = transExp pos latt P (List.concat [G',G]) p e2
		val (t3,e3') = transExp pos latt P G p e3
	    in 
		if S.eq_typ t1 S.StackTyp 
		then (if S.eq_typ t2 t3
		      then (t2, CaseExp(e1', pat', splitExp T e2', e3'))
		      else trans_err pos ("CaseExp: " ^ not_eq t1 S.StackTyp))
		else trans_err pos ("CaseExp: " ^ not_eq t2 t3)
	    end
	  | transExp' (S.ConcatExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		if S.eq_typ t1 S.StringTyp
		then (if S.eq_typ t2 S.StringTyp
		      then (t1, ConcatExp(e1', e2'))
		      else trans_err pos ("ConcatExp1: " ^ not_eq t2 S.StringTyp))
		else trans_err pos ("ConcatExp2: " ^ not_eq t1 S.StringTyp)
	    end
	  | transExp' (S.PlusExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		if S.eq_typ t1 S.IntTyp
		then (if S.eq_typ t2 S.IntTyp
		      then (t1, PlusExp(e1', e2'))
		      else trans_err pos ("PlusExp1: " ^ not_eq t2 S.IntTyp))
		else trans_err pos ("PlusExp2: " ^ not_eq t1 S.IntTyp)
	    end
	  | transExp' (S.EqExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		case (t1, t2) of 
		    (S.StringTyp, S.StringTyp) => (S.BoolTyp, EqExp(e1', e2'))
		  | (S.BoolTyp, S.BoolTyp) => (S.BoolTyp, EqExp(e1', e2'))
		  | (S.IntTyp, S.IntTyp) => (S.BoolTyp, EqExp(e1', e2'))
		  | _ => trans_err pos ("EqExp: " ^ not_eq t1 t2)
	    end
	  | transExp' (S.GTExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		if S.eq_typ t1 S.IntTyp
		then (if S.eq_typ t2 S.IntTyp
		      then (S.BoolTyp, GTExp(e1', e2'))
		      else trans_err pos ("GTExp1: " ^ not_eq t2 S.IntTyp))
		else trans_err pos ("GTExp2: " ^ not_eq t1 S.IntTyp)
	    end
	  | transExp' (S.AbortExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.UnitTyp
		then (t, AbortExp e')
		else trans_err pos ("AbortExp: " ^ not_eq t S.UnitTyp)
	    end
	  | transExp' (S.IntExp i) =
	    (S.IntTyp, IntExp i)
	  | transExp' (S.ItoSExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.IntTyp
		then (S.StringTyp, ItoSExp e')
		else trans_err pos ("ItoSExp: " ^ not_eq t S.IntTyp)
	    end
	  | transExp' (S.PosExp (pos', e)) =
	    let 
		val (t, e') = transExp pos' latt P G p e
	    in 
		(t, PosExp (pos', e'))
	    end
	  | transExp' (S.TupleExp es) =
	    let 
		val tes = map transExp' es
		val ts = map #1 tes
		val es' = map #2 tes
	    in 
		(S.TupleTyp ts, TupleExp es')
	    end
	  | transExp' (S.SplitExp (xs, e1, e2)) =
	    let 
		val (t1, e1') = transExp' e1
		val ts = case t1 of 
			  S.TupleTyp ts => ts
			| _ => trans_err pos ("SplitExp: " ^ ppSTyp t1 ^ " not TupleTyp")
		val xts = map (fn (x,t) => S.VarG(x,t)) (zip xs ts)
		val (t2, e2') = transExp pos latt P (xts@G) p e2
	    in
		(t2, SplitExp (xs, e1', e2'))
	    end
	  | transExp' (S.SocketExp (st,e)) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.UnitTyp 
		then (S.SockTyp, SocketExp (transST st, e'))
		else trans_err pos ("SocketExp: " ^ not_eq t S.UnitTyp)
	    end
	  | transExp' (S.BindExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.SockTyp, S.StringTyp, S.IntTyp])
		then (S.UnitTyp, BindExp e')
		else trans_err pos ("SocketExp: " ^ not_eq  t (S.TupleTyp [S.SockTyp, S.StringTyp, S.IntTyp]))
	    end
	  | transExp' (S.ListenExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.SockTyp, S.IntTyp])
		then (S.UnitTyp, ListenExp e')
		else trans_err pos ("ListenExp: " ^ not_eq t (S.TupleTyp [S.SockTyp, S.IntTyp]))
	    end
	  | transExp' (S.AcceptExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.SockTyp
		then (S.TupleTyp [S.SockTyp, S.StringTyp, S.IntTyp], AcceptExp e')
		else trans_err pos ("AcceptExp: " ^ not_eq t S.SockTyp)
	    end
	  | transExp' (S.ConnectExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.SockTyp, S.StringTyp, S.IntTyp])
		then (S.UnitTyp, ConnectExp e')
		else trans_err pos ("ConnectExp: " ^ not_eq  t (S.TupleTyp [S.SockTyp, S.StringTyp, S.IntTyp]))
	    end
	  | transExp' (S.SendExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.SockTyp, S.StringTyp])
		then (S.IntTyp, SendExp e')
		else trans_err pos ("SendExp: " ^ not_eq t (S.TupleTyp [S.SockTyp, S.StringTyp]))
	    end
	  | transExp' (S.RecvExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.SockTyp, S.IntTyp])
		then (S.StringTyp, RecvExp e')
		else trans_err pos ("RecvExp: " ^ not_eq t (S.TupleTyp [S.SockTyp, S.IntTyp]))
	    end
	  | transExp' (S.NowExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.UnitTyp
		then (S.IntTyp, NowExp e')
		else trans_err pos ("NowExp: " ^ not_eq t S.UnitTyp)
	    end
	  | transExp' (S.OpenExp (ot, e)) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.FileTyp, OpenExp (transOT ot,e'))
		else trans_err pos ("OpenExp: " ^ not_eq t S.StringTyp)
	    end
	  | transExp' (S.WriteExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.FileTyp, S.StringTyp])
		then (S.IntTyp, WriteExp e')
		else trans_err pos ("WriteExp: " ^ not_eq t (S.TupleTyp [S.FileTyp, S.StringTyp]) )
	    end
	  | transExp' (S.ReadExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.FileTyp, S.IntTyp])
		then (S.StringTyp, ReadExp e')
		else trans_err pos ("ReadExp: " ^ not_eq t (S.TupleTyp [S.FileTyp, S.IntTyp]) )
	    end
	  | transExp' (S.DeleteExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.UnitTyp, DeleteExp e')
		else trans_err pos ("DeleteExp: " ^ not_eq t S.StringTyp)
	    end
	  | transExp' (S.RenameExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.StringTyp, S.StringTyp])
		then (S.UnitTyp, RenameExp e')
		else trans_err pos ("RenameExp: " ^ not_eq t (S.TupleTyp [S.StringTyp, S.StringTyp]))
	    end
	  | transExp' (S.SizeExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.IntTyp, SizeExp e')
		else trans_err pos ("SizeExp: " ^ not_eq t S.StringTyp)
	    end
	  | transExp' (S.SleepExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.IntTyp
		then (S.UnitTyp, SleepExp e')
		else trans_err pos ("SleepExp: " ^ not_eq t S.IntTyp)
	    end
	  | transExp' (S.IndexOfExp (iot, e)) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.StringTyp, S.StringTyp])
		then (S.IntTyp, IndexOfExp (transIOT iot, e'))
		else trans_err pos ("IndexOfExp: " ^ not_eq t (S.TupleTyp [S.StringTyp, S.StringTyp]))
	    end
	  | transExp' (S.SubstringExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t (S.TupleTyp [S.StringTyp, S.IntTyp, S.IntTyp])
		then (S.StringTyp, SubstringExp e')
		else trans_err pos ("SubstringExp: " ^ not_eq t (S.TupleTyp [S.StringTyp, S.IntTyp, S.IntTyp]))
	    end
	  | transExp' (S.ExistsExp e) =
	    let 
		val (t, e') = transExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.BoolTyp, ExistsExp e')
		else trans_err pos ("ExistsExp: " ^ not_eq t S.StringTyp)
	    end
	  | transExp' (S.MultExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		if S.eq_typ t1 S.IntTyp
		then (if S.eq_typ t2 S.IntTyp
		      then (t1, MultExp(e1', e2'))
		      else trans_err pos ("MultExp1: " ^ not_eq t2 S.IntTyp))
		else trans_err pos ("MultExp2: " ^ not_eq t1 S.IntTyp)
	    end
	  | transExp' (S.DivExp (e1, e2)) =
	    let
		val (t1, e1') = transExp' e1
		val (t2, e2') = transExp' e2
	    in
		if S.eq_typ t1 S.IntTyp
		then (if S.eq_typ t2 S.IntTyp
		      then (t1, DivExp(e1', e2'))
		      else trans_err pos ("DivExp1: " ^ not_eq t2 S.IntTyp))
		else trans_err pos ("DivExp2: " ^ not_eq t1 S.IntTyp)
	    end
	  | transExp' (S.NegExp e) =
	    let
		val (t, e') = transExp' e
	    in
		if S.eq_typ t S.IntTyp
		then (t, NegExp e')
		else (if S.eq_typ t S.BoolTyp
		      then (t, NegExp e')
		      else trans_err pos ("DivExp1: " ^ not_eq t S.BoolTyp))
	    end




		
    in 
	transExp'
    end

and splitExp nil e = 
    e
  | splitExp ((a,x,y,z)::T) e = 
    splitExp T (SplitExp([x,y,z], VarExp a, e))
    

and transPat pos latt P p =
    let
	fun transPat' (S.PtPat(pts,x,y,n,pat)) =
	    let
		val (tself, targ, tres, pres, posts) = pt_help pos S.Before pts P
		val (pat', G, T) = transPat' pat
		val z = Id.freshid "z"
	    in 
		(PtPat(LabSetExp(pres, p), z, pat'),
		 S.VarG(x,tself)::S.VarG(y,targ)::S.VarG(n,S.StringTyp)::G,
		 (z,x,y,n)::T)
	    end
	  | transPat' S.NilPat =
	    (NilPat, nil, nil)
	  | transPat' (S.AllPat pat) =
	    let
		val (pat', G, T) = transPat' pat
	    in 
		(AllPat pat', G, T)
	    end
	  | transPat' (S.VarPat x) =
	    (VarPat x, [S.VarG(x,S.StackTyp)], nil)
    in 
	transPat'
    end


and lookupP pos (obj1,meth1) ((PointP(obj2,meth2,tself,targ,tres,p,pre,post))::t) =
    if Id.eqid obj1 obj2 andalso Id.eqid meth1 meth2
    then (tself,targ,tres,p,pre,post)
    else lookupP pos (obj1,meth1) t
  | lookupP pos (obj1,meth1) nil =
    trans_err pos ("lookupP: Cannot find pointcut " ^ ppVar obj1 ^ "." ^ ppVar meth1)

and pt_help pos time (h::t) P =
    let 
	val (tself,targ,tres,p,pre,post) = lookupP pos h P
	val (pres, posts) = pt_help' pos time tself targ tres t P
    in 
	(tself,targ,tres,(VarExp pre)::pres,(VarExp post)::posts)
    end
  | pt_help pos time nil P =
    (S.UnitTyp, S.UnitTyp, S.UnitTyp, nil, nil)

and pt_help' pos time tself targ tres (h::t) P =
    let
	val (tself',targ',tres',p,pre,post) = lookupP pos h P
	val (pres,posts) = pt_help' pos time tself targ tres t P
    in 
	if S.eq_typ tself tself' 
	   andalso (case time of S.Before => S.eq_typ targ targ'
			       | S.After => S.eq_typ tres tres')
	then ((VarExp pre)::pres, (VarExp post)::posts)
	else raise TransError "pt_help"
    end
  | pt_help' pos time tself targ tres nil P =
    (nil,nil)
	
and transDec pos latt P G p nil nil e =
    transExp pos latt P G p e
  | transDec pos latt P G p nil (S.Asp(p',decs)::asps) e = 
    if leq_prot latt p' p
    then let
	    val (t1,e') = transDec pos latt P G p' decs nil S.UnitExp
	    val (t2,e'') = transDec pos latt P G p nil asps e
	in 
	    if (S.eq_typ t1 S.UnitTyp)
	    then (t2, SeqExp(LowerExp(p', e'), e''))
	    else trans_err pos ("Asp: " ^ not_eq t1 S.UnitTyp)
	end
    else trans_err pos "Asp: bad protection domains"
  | transDec pos latt P G p (S.BoolDec(x, e1)::ds) asps e2 =
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.BoolTyp)::G) p ds asps e2
    in 
	if (S.eq_typ t1 S.BoolTyp)
	then (t2, LetExp(p, x, transTyp t1, e1', e2'))
	else trans_err pos ("BoolDec: " ^ not_eq t1 S.BoolTyp)
    end
  | transDec pos latt P G p (S.StringDec(x, e1)::ds) asps e2 =
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.StringTyp)::G) p ds asps e2
    in 
	if (S.eq_typ t1 S.StringTyp)
	then (t2, LetExp(p, x, transTyp t1, e1', e2'))
	else trans_err pos ("StringDec: " ^ not_eq t1 S.StringTyp)
    end
  | transDec pos latt P G p (S.IntDec(x, e1)::ds) asps e2 =
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.IntTyp)::G) p ds asps e2
    in 
	if (S.eq_typ t1 S.IntTyp)
	then (t2, LetExp(p, x, transTyp t1, e1', e2'))
	else trans_err pos ("IntDec: " ^ not_eq t1 S.IntTyp)
    end
  | transDec pos latt P G p (S.FileDec(x, e1)::ds) asps e2 =
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.FileTyp)::G) p ds asps e2
    in 
	if (S.eq_typ t1 S.FileTyp)
	then (t2, LetExp(p, x, transTyp t1, e1', e2'))
	else trans_err pos ("FileDec: " ^ not_eq t1 S.FileTyp)
    end
  | transDec pos latt P G p (S.SockDec(x, e1)::ds) asps e2 =
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.SockTyp)::G) p ds asps e2
    in 
	if (S.eq_typ t1 S.SockTyp)
	then (t2, LetExp(p, x, transTyp t1, e1', e2'))
	else trans_err pos ("SockDec: " ^ not_eq t1 S.SockTyp)
    end
  | transDec pos latt P G p (S.RefDec(x,t,e1)::ds) asps e2 = 
    let 
	val (t1,e1') = transExp pos latt P G p e1
	val (t2,e2') = transDec pos latt P (S.VarG(x,S.RefTyp(t,p))::G) p ds asps e2
    in 
	if (S.eq_typ t1 t)
	then (t2, LetExp(p, x, RefTyp(transTyp t1,p), NewRefExp(p,e1'), e2'))
	else trans_err pos ("RefDec: " ^ not_eq t1 t)
    end
  | transDec pos latt P G p (S.ObjDec(objvar,mlist)::ds) asps e2 =
    let
	val sobjtyp = S.ObjTyp(map (fn(m,rettyp,x,y,argtyp,ei) =>
				   (m,p,S.ArrTyp(argtyp,p,rettyp)))
				mlist)
	val objtyp = transTyp sobjtyp
	val prepts = map (fn(m,rettyp,x,y,argtyp,ei) => 
			    Id.freshid (Id.id2string objvar ^ Id.id2string m ^ "pre")) 
			 mlist
	val postpts = map (fn(m,rettyp,x,y,argtyp,ei) => 
			     Id.freshid (Id.id2string objvar ^ Id.id2string m ^ "post")) 
			  mlist
	val obj = 
	    ObjExp(map (fn((m,rettyp,x,y,argtyp,e),pre,post) => 
			  let 
			      val (t,e') = transExp pos latt P (S.VarG(x,sobjtyp)::
							    S.VarG(y,argtyp)::
							    G) p e
			      val res = Id.freshid "res"
			  in
			      if (S.eq_typ t rettyp)
			      then
				  (m,
				   ArrTyp(transTyp argtyp, p, transTyp rettyp),
				   p,
				   x,
				   FunExp(p,
					  y,
					  transTyp argtyp,
					  StoreExp (VarExp pre,
						    TupleExp([VarExp x,
							      VarExp y, 
							      StringExp(Id.id2string objvar ^ "." ^ Id.id2string m)]),
						    SeqExp(PCExp(VarExp pre,
								 TupleExp([VarExp x,
									   VarExp y, 
									   StringExp(Id.id2string objvar ^ "." ^ Id.id2string m)])),
							   LetExp(p,
								  res,
								  transTyp rettyp,
								  e',
								  SeqExp(PCExp(VarExp post,
									       TupleExp([VarExp x,
											 VarExp res, 
											 StringExp(Id.id2string objvar ^ "." ^ Id.id2string m)])),
									 VarExp res))))))
				  else trans_err pos ("ObjDec: " ^ not_eq t rettyp)
			  end)
		   (zip3 mlist prepts postpts))
	val P' = (map (fn((m,rettyp,x,y,argtyp,e),pre,post) =>
			  PointP(objvar,m,sobjtyp,argtyp, rettyp,p,pre,post))
		      (zip3 mlist prepts postpts))
		 @ P
	val G' = S.VarG(objvar,sobjtyp)::G
	val (t, e2') = transDec pos latt P' G' p ds asps e2	  
	val objexp = LetExp(p,objvar,objtyp,obj,e2')
  	val postexp = foldr (fn(((m,rettyp,x,y,argtyp,e),pre,post),e') => 
			       LetExp(p,
				      post,
				      LabTyp(TupleTyp([objtyp,
						      transTyp rettyp,
						      StringTyp]),
					     p),
				      NewExp(p,
					     TupleTyp([objtyp,
						       transTyp rettyp,
						       StringTyp])),
				      e'))
			    objexp 
			    (zip3 mlist prepts postpts)
	val preexp = foldr (fn(((m,rettyp,x,y,argtyp,e),pre,post),e') => 
			       LetExp(p,
				      pre,
				      LabTyp(TupleTyp([objtyp,
						      transTyp argtyp,
						      StringTyp]),
					     p),
				      NewExp(p,
					     TupleTyp([objtyp,
						       transTyp argtyp,
						       StringTyp])),
				      e'))
			    postexp 
			    (zip3 mlist prepts postpts)
    in 
	(t,preexp)
    end
  | transDec pos latt P G p (S.AspDec(time, pts, x,y,s,n,e1)::ds) asps e2 =
			  let 
	val (tself, targ, tres, pres, posts) = pt_help pos time pts P
	val (t,pts') = case time of
			   S.Before => (targ,pres)
			 | S.After => (tres, posts)
	val (t1, e1') = transExp pos latt P (S.VarG(x,tself)::S.VarG(y,t)::S.VarG(s,S.StackTyp)::S.VarG(n,S.StringTyp)::G) p e1
	val (t2, e2') = transDec pos latt P G p ds asps e2
	val z = Id.freshid "z"
    in 
	if S.eq_typ t1 S.UnitTyp
	then (t2,SeqExp(AdvInstExp(AdvExp(LabSetExp(pts',
						    p),
					  z,
					  p,
					  SplitExp([x,y,n],
						   VarExp z,
						   LetExp(p,s,
							  StackTyp,
							  StackExp,
							  e1')))),
			e2'))
	else trans_err pos ("AspDec: " ^ not_eq t1 S.UnitTyp)
    end
  | transDec pos latt P G p (S.PosDec (pos', d)::ds) asps e =
    transDec pos' latt P G p (d::ds) asps e

fun translate (S.Prog(decs, asps, e)) =
    let 
	val latt = create_lattice asps
	val (t,e') = transDec start_pos latt nil nil main_prot decs asps e 
	    handle (TransError s) => (print ("Trans Error: " ^ s ^ "\n");
				      (S.UnitTyp,UnitExp))
    in 
	(latt, t, e') 
    end

end
