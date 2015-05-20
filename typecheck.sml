structure TypeCheck :> TYPECHECK =
struct

open Core ProtDom PrettyPrint Util

exception TypeError of string

fun not_eq t1 t2 = 
    ppCTyp t1 ^ " != " ^ ppCTyp t2

fun type_err pos s = 
  raise (TypeError ("Position " ^ string_of_pos pos ^ ": " ^ s)) 
    
fun typeExp pos latt G p =
    let
	fun typeExp' UnitExp = 
	    UnitTyp
	  | typeExp' (StringExp s) = 
	    StringTyp
	  | typeExp' TrueExp =
	    BoolTyp
	  | typeExp' FalseExp =
	    BoolTyp
	  | typeExp' (IfExp(e1, e2, e3)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
		val t3 = typeExp' e3
	    in 
		if (eq_typ t1 BoolTyp) 
		then if eq_typ t2 t3
		     then t2
		     else type_err pos ("IfExp " ^ not_eq t2 t3)
		else type_err pos ("IfExp " ^ not_eq t2 t3)
	    end
	  | typeExp' (FunExp(p',var,typ,exp)) = 
	    ArrTyp (typ, p', typeExp pos latt (VarG(var,typ)::G) p' exp)
	  | typeExp' (LabExp l) = 
	    let 
		val (t,p') = lookupLabG l G
	    in 
		LabTyp(t,p') 
	    end
	  | typeExp' (RefExp r) = 
	    let 
		val (t,p') = lookupRefG r G
	    in 
		RefTyp(t,p') 
	    end
	  | typeExp' (ObjExp mlist) = 
	    let 
		val objtyp = ObjTyp (map 
					 (fn(m,t,p',x,e) => 
					    (m,p',t)) 
					 mlist)
	    in
		(app (fn(m,t,p',x,e) => 
			let 
			    val t' = typeExp pos latt (VarG(x,objtyp)::G) p' e
			in 
			    if (eq_typ t' t)
			    then ()
			    else type_err pos ("ObjExp " ^ not_eq t' t)
			end)
		     mlist);
		objtyp
	    end
	  | typeExp' (VarExp x) = 
	    lookupVarG x G
	  | typeExp' (SeqExp(e1,e2)) = 
	    let
		val t1 = typeExp' e1
	    in 
		(*if eq_typ t1 UnitTyp 
		then *)typeExp' e2
		(*else type_err pos ("SeqExp " ^ not_eq t1 UnitTyp)*)
	    end
	  | typeExp' (PrintExp e) = 
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp
		then UnitTyp
		else type_err pos ("PrintExp " ^ not_eq t StringTyp)
	    end
	  | typeExp' (AppExp(e1, e2)) = 
	    (case typeExp' e1 of 
		 ArrTyp (t1,p',t2) => 
		 let 
		     val t2' = typeExp' e2
		 in 
		     if eq_typ t1 t2'
		     then if eq_prot p p'
			  then t2 
			  else type_err pos "AppExp: bad protection domain"
		     else type_err pos ("AppExp " ^ not_eq t1 t2')
		 end
	       | _ => raise TypeError "AppExp3")
	  | typeExp' (AdvExp(e1, x, p'', e2)) =
	    (case typeExp' e1 of
		 PCTyp(t,p') => 
		 let 
		     val t2 = typeExp pos latt (VarG(x,t)::G) p'' e2
		 in
			 if eq_typ t2 UnitTyp
			 then if leq_prot latt p'' p'
			      then AdvTyp p'' 
			      else type_err pos "AdvExp: bad protectoin domain"
			 else type_err pos ("AdvExp: " ^ not_eq t2 UnitTyp)
		 end
	       | t => type_err pos ("AdvExp: Not pc - " ^ ppCTyp t)) 
	  | typeExp' (AdvInstExp e) =
	    (case typeExp' e of 
		AdvTyp p' => if (leq_prot latt p' p)
			      then UnitTyp
			      else type_err pos "AdvInstExp: bad protection domains"
	       | t => type_err pos ("AdvInstExp2: " ^ ppCTyp t ^ " not AdvTyp"))
	  | typeExp' (NewExp(p', t)) = 
	    LabTyp(t,p')
	  | typeExp' (PCExp(e1,e2)) = 
	    (case typeExp' e1 of
		 LabTyp(t,p') => 
		 let 
		     val t2 = typeExp' e2
		 in 
		     if eq_typ t2 t
		     then if leq_prot latt p' p
			  then UnitTyp
			  else type_err pos "PCExp: bad protection domains"
		     else type_err pos ("PCExp: " ^ not_eq t2 t)
		 end
	       | _ => raise TypeError "PCExp3")
	  | typeExp' (NewRefExp(p',e)) =
	    (if (leq_prot latt p' p)
	     then RefTyp(typeExp' e, p')
	     else type_err pos "NewRefExp")
	  | typeExp' (DerefExp e) = 
	    (case typeExp' e of
		 RefTyp(t,p') => if (leq_prot latt p p') 
				 then t 
				 else type_err pos "DerefExp1"
	       | _ => type_err pos "DerefExp e")
	  | typeExp' (AssignExp(e1,e2)) =
	    (case typeExp' e1 of
		 RefTyp(t,p') => if (eq_typ (typeExp' e2) t) 
				    andalso (leq_prot latt p' p)
				 then t
				 else type_err pos "AssignExp1"
	       | _ => type_err pos "AssignExp2")
	  | typeExp' (LowerExp(p',e)) =
	    let
		val typ = typeExp pos latt G p' e
	    in 
		(if (eq_typ typ UnitTyp) 
		    andalso (leq_prot latt p' p)
		 then UnitTyp
		 else type_err pos "LowerExp")
	    end
	  | typeExp' (TupleExp elist) =
	    TupleTyp(map (fn(e) => typeExp' e) elist)
	  | typeExp' (SplitExp(xlist, e1, e2)) = 
	    let 
		val tuptyp = typeExp' e1
	    in
		case tuptyp of
		    TupleTyp tlist => typeExp pos latt (splitHelp G xlist tlist) p e2
		  | _ => raise TypeError "SplitExp"
	    end
	  | typeExp' (LabSetExp(elist,p')) = 
	    (let
		 val tlist = map typeExp' elist
		 val (plist,t) = extractLab(tlist)
	     in		      
		 (checkP latt plist p'); PCTyp(t,p')
	     end)
	  | typeExp' (UnionExp(e1,p',e2)) = 
	    (case (typeExp' e1, typeExp' e2) of
		 (PCTyp(t1,p1),PCTyp(t2,p2)) => 
		 if (eq_typ t1 t2) 
		    andalso (leq_prot latt p' p1) 
		    andalso (leq_prot latt p' p2)
		 then PCTyp(t1,p')
		 else type_err pos "UnionExp1"
	       | _ => type_err pos "UnionExp2")	
	  | typeExp' (MembExp(e,m)) = 
	    let 
		val objtyp = typeExp' e
	    in 
		case objtyp of 
		    ObjTyp(mlist) => membHelp p mlist m
		  |_ => type_err pos "MembExp"
			      
	    end
	  | typeExp' StackExp =
	    StackTyp
	  | typeExp' NilStExp =
	    StackTyp
	  | typeExp' (PtStExp(e1, e2, e3)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
		val t3 = typeExp' e3
	    in 
		case (t1,t3) of
		    (LabTyp(t,p'),StackTyp) => 
		    if (eq_typ t t2)
		    then StackTyp
		    else type_err pos "PtStExp1"
		  | _ => type_err pos "PtStExp2"
	    end
	  | typeExp' (StoreExp(e1, e2, e3)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
		val t3 = typeExp' e3
	    in 
		case t1 of
		    LabTyp(t,p') => 
		    if (eq_typ t t2)
		    then t3
		    else type_err pos "StoreExp1"
		  | _ => type_err pos "StoreExp2"
	    end
	  | typeExp' (CaseExp(e1, pat, e2, e3)) =
	    let
		val t1 = typeExp' e1
		val G' = typePat pos latt G p pat
		val G'' = List.concat [G', G]
		val t2 = typeExp pos latt G'' p e2
		val t3 = typeExp' e3
	    in 
		if eq_typ t1 StackTyp 
		   andalso eq_typ t2 t3
		then t2
		else type_err pos "CaseExp"
	    end 
	  | typeExp' (ConcatExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 StringTyp
		then (if eq_typ t2 StringTyp
		      then t1
		      else type_err pos ("ConcatExp: " ^ not_eq t2 StringTyp))
		else type_err pos ("ConcatExp: " ^ not_eq t1 StringTyp)
	    end
	  | typeExp' (PlusExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 IntTyp
		then (if eq_typ t2 IntTyp
		      then IntTyp
		      else type_err pos ("PlusExp: " ^ not_eq t2 IntTyp))
		else type_err pos ("PlusExp: " ^ not_eq t1 IntTyp)
	    end
	  | typeExp' (EqExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		case (t1, t2) of
		    (StringTyp, StringTyp) => BoolTyp
		  | (IntTyp, IntTyp) => BoolTyp
		  | (BoolTyp, BoolTyp) => BoolTyp
		  | _ =>  type_err pos ("EqExp: " ^ not_eq t1 t2)
	    end
	  | typeExp' (GTExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 IntTyp
		then (if eq_typ t2 IntTyp
		      then BoolTyp
		      else type_err pos ("GTExp: " ^ not_eq t2 IntTyp))
		else type_err pos ("GTExp: " ^ not_eq t1 IntTyp)
	    end 
	  | typeExp' (AbortExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t UnitTyp 
		then UnitTyp
		else type_err pos ("AbortExp: " ^ not_eq t UnitTyp)
	    end
	  | typeExp' (IntExp i) =
	    IntTyp
	  | typeExp' (ItoSExp e) =
	    let
		val t = typeExp' e
	    in 
		if eq_typ t IntTyp 
		then StringTyp
		else type_err pos ("PrintExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (PosExp (pos', e)) =
	    typeExp pos' latt G p e
	  | typeExp' (SocketExp (st, e)) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t UnitTyp 
		then SockTyp
		else type_err pos ("SocketExp: " ^ not_eq t UnitTyp)
	    end
	  | typeExp' (BindExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [SockTyp, StringTyp, IntTyp])
		then UnitTyp
		else type_err pos ("BindExp: " ^ not_eq t (TupleTyp [SockTyp, StringTyp, IntTyp]))
	    end
	  | typeExp' (ListenExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [SockTyp, IntTyp])
		then UnitTyp
		else type_err pos ("ListenExp: " ^ not_eq t (TupleTyp [SockTyp, IntTyp]))
	    end
	  | typeExp' (AcceptExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t SockTyp 
		then (TupleTyp [SockTyp, StringTyp, IntTyp])
		else type_err pos ("AcceptExp: " ^ not_eq t SockTyp)
	    end
	  | typeExp' (ConnectExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [SockTyp, StringTyp, IntTyp])
		then UnitTyp
		else type_err pos ("ConnectExp: " ^ not_eq t (TupleTyp [SockTyp, StringTyp, IntTyp]))
	    end
	  | typeExp' (SendExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [SockTyp, StringTyp])
		then IntTyp
		else type_err pos ("SendExp: " ^ not_eq t (TupleTyp [SockTyp, StringTyp]))
	    end
	  | typeExp' (RecvExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [SockTyp, IntTyp])
		then StringTyp
		else type_err pos ("RecvExp: " ^ not_eq t (TupleTyp [SockTyp, IntTyp]))
	    end

	  | typeExp' (SockExp _) =
	    SockTyp
	  | typeExp' (NowExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t UnitTyp 
		then IntTyp
		else type_err pos ("NowExp: " ^ not_eq t UnitTyp)
	    end
	  | typeExp' (OpenExp (ot,e)) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp
		then FileTyp
		else type_err pos ("OpenExp: " ^ not_eq t  StringTyp)
	    end
	  | typeExp' (WriteExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [FileTyp, StringTyp])
		then IntTyp
		else type_err pos ("WriteExp: " ^ not_eq t (TupleTyp [FileTyp, StringTyp]))
	    end
	  | typeExp' (ReadExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [FileTyp, IntTyp])
		then StringTyp
		else type_err pos ("ReadExp: " ^ not_eq t (TupleTyp [FileTyp, IntTyp]))
	    end
	  | typeExp' (DeleteExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp
		then UnitTyp
		else type_err pos ("DeleteExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (RenameExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [StringTyp, StringTyp])
		then UnitTyp
		else type_err pos ("RenameExp: " ^ not_eq t (TupleTyp [StringTyp, StringTyp]))
	    end
	  | typeExp' (FileExp _) =
	    FileTyp
	  | typeExp' (SizeExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp
		then IntTyp
		else type_err pos ("SizeExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (SleepExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t IntTyp
		then UnitTyp
		else type_err pos ("SleepExp: " ^ not_eq t IntTyp)
	    end
	  | typeExp' (IndexOfExp (iot, e)) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [StringTyp, StringTyp])
		then IntTyp
		else type_err pos ("IndexOfExp: " ^ not_eq t (TupleTyp [StringTyp, StringTyp]))
	    end
	  | typeExp' (SubstringExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t (TupleTyp [StringTyp, IntTyp, IntTyp])
		then StringTyp
		else type_err pos ("SubstringExp: " ^ not_eq t (TupleTyp [StringTyp, IntTyp, IntTyp]))
	    end
	  | typeExp' (ExistsExp e) =
	    let 
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp
		then BoolTyp
		else type_err pos ("ExistsExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (MultExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 IntTyp
		then (if eq_typ t2 IntTyp
		      then IntTyp
		      else type_err pos ("MultExp1: " ^ not_eq t2 IntTyp))
		else type_err pos ("MultExp2: " ^ not_eq t1 IntTyp)
	    end
	  | typeExp' (DivExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 IntTyp
		then (if eq_typ t2 IntTyp
		      then IntTyp
		      else type_err pos ("DivExp1: " ^ not_eq t2 IntTyp))
		else type_err pos ("DivExp2: " ^ not_eq t1 IntTyp)
	    end
	  | typeExp' (NegExp e) =
	    let
		val t = typeExp' e
	    in 
		if eq_typ t IntTyp
		then IntTyp
		else (if eq_typ t BoolTyp
		      then BoolTyp
		      else type_err pos ("NegExp: " ^ not_eq t BoolTyp))
	    end
    in
	typeExp'
    end
	
and typePat pos latt G p =
    let
	fun typePat' NilPat = 
	    nil
	  | typePat' (PtPat(e,x,pat)) =
	    let 
		val t = typeExp pos latt G p e
		val G' = typePat' pat
	    in 
		case t of
		    PCTyp(t',p) => VarG(x,t')::G'
		  | _ => type_err pos "PtPat"
	    end
	  | typePat' (AllPat pat) = 
	    typePat' pat
	  | typePat' (VarPat x) =
	    [VarG(x,StackTyp)]
    in
	typePat'
    end
	
and splitHelp G (x::x') (t::t') = 
    splitHelp ((VarG(x,t))::G) x' t'
  | splitHelp G nil nil = 
    G
  | splitHelp _ _ _ = 
    raise TypeError "splitHelp"


and membHelp p ((m',p',t)::tail) m =
    if (Id.eqid m m')
    then (if (eq_prot p p') 
	  then t
	  else raise TypeError "membHelp1")
    else membHelp p tail m
  | membHelp _ nil _ = 
    raise TypeError "membHelp2"
   
and extractLab (LabTyp(t,p)::tail) = 
    (p::(extractLabHelper tail t),t)
  | extractLab _ = raise TypeError "extractLab"

and extractLabHelper (LabTyp(t,p)::tail) t' = 
    if (eq_typ t t') 
    then p::(extractLabHelper tail t')
    else raise TypeError "extractLabHelper1"
  | extractLabHelper nil _ = 
    nil
  | extractLabHelper _ _ =
    raise TypeError "extractLabHelper2"

and checkP latt (p::plist) p' = 
    if (leq_prot latt p' p) 
    then checkP latt plist p'
    else raise TypeError "checkP"
  | checkP latt nil p' = 
    ()
    
 
   
(* label -> pc *)

and lookupVarG x (VarG(y,t)::G) = 
    if (Id.eqid x y) 
    then t 
    else lookupVarG x G
  | lookupVarG x (_::G) = 
    lookupVarG x G
  | lookupVarG x nil = 
    raise TypeError "lookupVarG"

and lookupLabG x (LabG(y,t,p)::G) = 
    if (x = y) 
    then (t,p) 
    else lookupLabG x G
  | lookupLabG x (_::G) = 
    lookupLabG x G
  | lookupLabG x nil = 
    raise TypeError "lookupLabG"


and lookupRefG x (RefG(y,t,p)::G) = 
    if (x = y) 
    then (t,p) 
    else lookupRefG x G
  | lookupRefG x (_::G) = 
    lookupRefG x G
  | lookupRefG x nil = 
    raise TypeError "lookupRefG"

 
    
fun typecheck latt e =
   ((typeExp start_pos latt nil (Id.makeid "main") e);
    true)
   handle (TypeError s) => (print ("Type Error: " ^ s ^ "\n");false)


end