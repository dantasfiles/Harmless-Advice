structure Eval =
struct

open Core ProtDom

exception EvalError of string
exception AbortError

val labCount = ref 0
val refCount = ref 0

val zeroTime = Time.now ();

fun newLab () = ((labCount := !labCount + 1);!labCount)
and newRef () = ((refCount := !refCount + 1);!refCount)

and eval latt e = 
    (evalLoop latt nil nil e)
    handle EvalError s => (print ("Evaluation Error: " ^ s ^ "\n"); UnitExp)
	 | AbortError => (print ("Program aborted.\n"); UnitExp)

and evalDebug latt e = 
    (evalDebugLoop latt nil nil e)
    handle EvalError s => (print ("Evaluation Error: " ^ s ^ "\n"); UnitExp)
	 | AbortError => (print ("Program aborted.\n"); UnitExp)

and evalDebugLoop latt S A e =
    if isValue e 
    then e
    else (print (PrettyPrint.ppCExp e ^ "\n\n"); let 
	    val p = Id.makeid "main"
	    val (S', A', p', e') = evalExp NilStExp latt S A p e
	in 
	    if (eq_prot p p') 
	    then evalDebugLoop latt S' A' e'
	    else raise EvalError "evalLoop"
	end)

and evalLoop latt S A e =
    if isValue e 
    then e
    else let 
	    val p = Id.makeid "main"
	    val (S', A', p', e') = evalExp NilStExp latt S A p e
	in 
	    if (eq_prot p p') 
	    then evalLoop latt S' A' e'
	    else raise EvalError "evalLoop"
	end

and isValue UnitExp = 
    true
  | isValue (StringExp _) = 
    true
  | isValue TrueExp = 
    true
  | isValue FalseExp = 
    true
  | isValue (FunExp _) = 
    true
  | isValue (LabExp _) = 
    true
  | isValue (RefExp _) = 
    true
  | isValue (AdvExp(e1,_,_,_)) = 
    isValue e1
  | isValue (TupleExp elist) = 
    List.all isValue elist
  | isValue (LabSetExp(llist,_)) = 
    List.all isValue llist
  | isValue (ObjExp _) = 
    true
  | isValue NilStExp = 
    true
  | isValue (PtStExp(LabExp l, e1, e2)) =
    (isValue e1) andalso (isValue e2)
  | isValue (IntExp _) =
    true
  | isValue (SockExp _) =
    true
  | isValue (FileExp _) =
    true
  | isValue _ = 
    false

and isValuePat NilPat = 
    true
  | isValuePat (PtPat(e, x, pat)) =
    (isValue e) andalso (isValuePat pat)
  | isValuePat (AllPat pat) =
    isValuePat pat
  | isValuePat (VarPat x) = 
    true

and evalExp stack latt S A p =
    let 
	fun evalExp' (SeqExp(e1,e2)) = 
	    if (isValue e1) 
	    then (S, A, p, e2)
	    else let
		    val (S', A', p', e1') = evalExp' e1
		in 
		    (S', A', p', SeqExp(e1', e2))
		end
	  (*| evalExp' (SeqExp(e1, e2)) = 
	    let
		val (S', A', p', e1') = evalExp' e1
	    in 
		(S', A', p', SeqExp(e1', e2))
	    end*)
	  | evalExp' (PrintExp (StringExp s)) = 
	    (print s; 
	     (S, A, p, UnitExp))
	  | evalExp' (PrintExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', PrintExp e')
	    end
	  | evalExp' (IfExp(TrueExp, e1, _)) =
	    (S, A, p, e1)
	  | evalExp' (IfExp(FalseExp, _, e2)) =
	    (S, A, p, e2)
	  | evalExp' (IfExp(e1,e2,e3)) =
	     let 
		 val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', IfExp(e1',e2,e3))
	    end
	  | evalExp' (AppExp(FunExp(p',x,t,e), e2)) = 
	    if isValue e2
	    then if eq_prot p' p
		 then (S, A, p, substExp e2 x e)
		 else raise EvalError "AppExp"
	    else let
		    val (S', A', p'', e2') = evalExp' e2
		in
		    (S', A', p'', AppExp(FunExp(p', x, t, e), e2'))
		end
	  | evalExp' (AppExp(e1, e2)) =
	    let
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', AppExp(e1', e2))
	    end
	  | evalExp' (AdvInstExp(AdvExp(e1,x,p',e2))) = 
	    if (leq_prot latt p' p)
	    then (S, AdvA(e1,x,p,e2)::A, p, UnitExp)
	    else raise EvalError "AdvInstExp"
	  | evalExp' (AdvInstExp(e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', AdvInstExp e')
	    end
	  | evalExp' (NewExp(p',t)) = 
	    let 
		val l = newLab()
	    in 
		(LabS(l,t,p')::S, A, p, LabExp l)
	    end
	  | evalExp' (PCExp(LabExp l, e)) = 
	    if isValue e
	    then let 
		    val (_,p') = lookupLabS l S
		in 
		    if leq_prot latt p' p
		    then (S, A, p, advComp A l e)
		    else raise EvalError "PCExp"
		end
	    else let 
		    val (S', A', p', e') = evalExp' e
		in
		    (S', A', p', PCExp(LabExp l, e'))
		end
	  | evalExp' (PCExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', PCExp(e1', e2))
	    end
	  | evalExp' (NewRefExp(p', e)) = 
	    if isValue e
	    then let 
		    val r = newRef ()
		in 
		    if (leq_prot latt p' p)
		    then (RefS(r,e,p')::S, A, p, RefExp r)
		    else raise EvalError "NewRefExp"
		end 
	    else let 
		    val (S', A', p'', e') = evalExp' e
		in
		    (S', A', p'', NewRefExp(p',e'))
		end
	  | evalExp' (DerefExp (RefExp r)) = 
	    (let 
		 val (v,p') = lookupRefS r S
	     in 
		 if (leq_prot latt p p')
		 then (S, A, p, v)
		 else raise EvalError "DerefExp"
	     end)
	  | evalExp' (DerefExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', DerefExp e')
	    end
	  | evalExp' (AssignExp(RefExp r, e)) = 
	    if isValue e
	    then let 
		    val (v',p') = lookupRefS r S
		in 
		    if leq_prot latt p' p
		    then (RefS(r,e,p')::S, A, p, UnitExp)
		    else raise EvalError "AssignExp"
		end
	    else let 
		    val (S', A', p', e') = evalExp' e
		in
		    (S', A', p', AssignExp(RefExp r, e'))
		end
	  | evalExp' (AssignExp(e1, e2)) = 
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', AssignExp(e1', e2))
	    end
	  | evalExp' (LowerExp(p',UnitExp)) = 
	    if leq_prot latt p' p
	    then (S, A, p, UnitExp)
	    else raise EvalError "LowerExp1"
	  | evalExp' (LowerExp(p', e)) =
	    if leq_prot latt p' p
	    then 
		let 
		    val (S', A', p'', e') = evalExp stack latt S A p' e
		in
		    (S', A', p, LowerExp(p', e'))
		end
	    else raise EvalError "LowerExp2"
	  | evalExp' (TupleExp (es)) =
	    let 
		val (S', A', p', es') = splitHelp2 stack latt S A p es
	    in
		(S', A', p', TupleExp (es'))
	    end 
	  | evalExp' (SplitExp(xlist, TupleExp(elist), e)) =
	    if (List.all (fn(x) => isValue x) elist)
	    then (S, A, p, splitHelp e elist xlist)
	    else let 
		    val (S', A', p', elist') = splitHelp2 stack latt S A p elist
		in
		    (S', A', p', SplitExp(xlist,TupleExp(elist'),e))
		end 
	  | evalExp' (SplitExp (xs, e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', SplitExp (xs, e1', e2))
	    end
	  | evalExp' (UnionExp(LabSetExp(llist1, p''),
				      p', 
				      LabSetExp(llist2,p'''))) =
	    if (leq_prot latt p' p'') andalso (leq_prot latt p' p''')
	    then (S, A, p, LabSetExp(llist1@llist2, p'))
	    else raise EvalError "UnionExp"
	  | evalExp' (UnionExp(LabSetExp(llist1,p''), p', e)) =
	    let 
		val (S', A', p''', e') = evalExp' e
	    in
		(S', A', p''', UnionExp(LabSetExp(llist1,p''), p', e'))
	    end
	  | evalExp' (UnionExp(e1, p', e2)) =
	    let 
		val (S', A', p'', e1') = evalExp' e1
	    in
		(S', A', p'', UnionExp(e1', p', e2))
	    end
	  | evalExp' (MembExp(ObjExp(mlist),m)) =
	    let 
		val (m',t,p',x,e) = membHelp mlist m
	    in 
		if eq_prot p p'
		then (S, A, p, substExp (ObjExp(mlist)) x e)
		else raise EvalError "MembExp"
	    end
	  | evalExp' (MembExp(e,m)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', MembExp(e', m))
	    end
	  | evalExp' StackExp = 
	    (S, A, p, stack)
	  | evalExp' (PtStExp(e1, e2, e3)) =
	    if isValue e1
	    then (if isValue e2
		  then (if isValue e3
			then raise EvalError "PtStExp"
			else let 
				val (S', A', p', e3') = evalExp' e3
			    in 
				(S', A', p', PtStExp(e1, e2, e3'))
			    end)
		  else let 
			  val (S', A', p', e2') = evalExp' e2
		      in 
			  (S', A', p', PtStExp(e1, e2', e3))
		      end)
	    else let 
		    val (S', A', p', e1') = evalExp' e1
		in 
		    (S', A', p', PtStExp(e1', e2, e3))
		end
	  | evalExp' (StoreExp(LabExp l,e1,e2)) =
	    if isValue e1
	    then (if isValue e2
		  then (S, A, p, e2)
		  else let
			  val (S', A', p', e2') = evalExp (PtStExp(LabExp l, e1, stack)) latt S A p e2
		      in 
			  (S', A', p', StoreExp(LabExp l, e1, e2'))
		      end)
	    else
		let 
		    val (S', A', p', e1') = evalExp' e1
		in 
		    (S', A', p', StoreExp(LabExp l, e1', e2))
		end
	  | evalExp' (StoreExp(e1, e2, e3)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in 
		(S', A', p', StoreExp(e1', e2, e3))
	    end
	  | evalExp' (CaseExp(e1,pat,e2,e3)) =
	    if isValue e1
	    then (if isValuePat pat 
		  then (case pat_match e1 pat of 
			    SOME sub => (S, A, p, subst_list sub e2)
			  | NONE => (S, A, p, e3))
		  else let 
			  val (S', A', p', pat') = evalPat stack latt S A p pat
		      in 
			  (S', A', p', CaseExp(e1, pat', e2, e3))
		      end)
	    else let 
		    val (S', A', p', e1') = evalExp' e1
		in 
		    (S', A', p', CaseExp(e1',pat,e2,e3))
		end
	  | evalExp' (ConcatExp(StringExp s1, StringExp s2)) =
	    (S, A, p, StringExp (s1 ^ s2))
	  | evalExp' (ConcatExp(StringExp s1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ConcatExp(StringExp s1, e'))
	    end
	  | evalExp' (ConcatExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', ConcatExp(e1', e2))
	    end
	  | evalExp' (PlusExp(IntExp i1, IntExp i2)) =
	    (S, A, p, IntExp (i1 + i2))
	  | evalExp' (PlusExp(IntExp i1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', PlusExp(IntExp i1, e'))
	    end
	  | evalExp' (PlusExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', PlusExp(e1', e2))
	    end	
	  | evalExp' (EqExp(StringExp s1, StringExp s2)) =
	    (S, A, p, (case String.compare (s1, s2) of 
			   EQUAL => TrueExp
			 | _ => FalseExp))
	  | evalExp' (EqExp(IntExp i1, IntExp i2)) =
	    (S, A, p, if (i1 = i2) then TrueExp else FalseExp)
	  | evalExp' (EqExp(TrueExp, TrueExp)) =
	    (S, A, p, TrueExp)
	  | evalExp' (EqExp(TrueExp, FalseExp)) =
	    (S, A, p, FalseExp)
	  | evalExp' (EqExp(FalseExp, TrueExp)) =
	    (S, A, p, FalseExp)
	  | evalExp' (EqExp(FalseExp, FalseExp)) =
	    (S, A, p, TrueExp)
	  | evalExp' (EqExp(StringExp s1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', EqExp(StringExp s1, e'))
	    end
	  | evalExp' (EqExp(IntExp i1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', EqExp(IntExp i1, e'))
	    end
	  | evalExp' (EqExp(TrueExp, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', EqExp(TrueExp, e'))
	    end
	  | evalExp' (EqExp(FalseExp, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', EqExp(FalseExp, e'))
	    end
	  | evalExp' (EqExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', EqExp(e1', e2))
	    end
	  | evalExp' (GTExp(IntExp i1, IntExp i2)) =
	    (S, A, p, if (i1 > i2) then TrueExp else FalseExp)
	  | evalExp' (GTExp(IntExp i1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', GTExp(IntExp i1, e'))
	    end
	  | evalExp' (GTExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', GTExp(e1', e2))
	    end	
	  | evalExp' (AbortExp UnitExp) =
	    raise AbortError
	  | evalExp' (AbortExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', AbortExp e')
	    end
	  | evalExp' (ItoSExp (IntExp i)) =
	    (S, A, p, StringExp (Int.toString i))
	  | evalExp' (ItoSExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ItoSExp e')
	    end
	  | evalExp' (PosExp (pos', e)) =
	    if isValue e
	    then (S, A, p, e)
	    else let 
		    val (S', A', p', e') = evalExp' e
		in 
		    (S', A', p', PosExp (pos', e'))
		end
	  | evalExp' (SocketExp (Active, UnitExp)) =
	    (S, A, p, SockExp (SocketActive (INetSock.TCP.socket ())))
	  | evalExp' (SocketExp (Passive, UnitExp)) =
	    (S, A, p, SockExp (SocketPassive (INetSock.TCP.socket ())))
	  | evalExp' (SocketExp (st, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', SocketExp (st, e'))
	    end
	  | evalExp' (BindExp (TupleExp [SockExp (SocketPassive sock), StringExp ip, IntExp port])) =
	    ((Socket.bind (sock, 
			 INetSock.toAddr (case (NetHostDB.fromString ip) of
					      SOME x => x
					    | _ => raise EvalError "BindExp: bad ip address", 
					 port));
	     (S, A, p, UnitExp)) handle OS.SysErr _ => raise EvalError "bind did not work")
	  | evalExp' (BindExp e) =
	    let 
		(*val _ = print ("bad in bind\n" ^ PrettyPrint.ppCExp e ^ "\n")*)
	(*	val _ = case e of PosExp (p, x) => print (Bool.toString (isValue x))*)
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', BindExp e')
	    end
	  | evalExp' (ListenExp (TupleExp [SockExp (SocketPassive sock), IntExp qsize])) =
	    ((Socket.listen (sock, qsize));
	    (S, A, p, UnitExp))
	  | evalExp' (ListenExp e) =
	    let 
	(*	val _ = print ("bad in listen\n" ^ PrettyPrint.ppCExp e ^ "\n")*)
	(*	val _ = case e of PosExp (p, x) => print (Bool.toString (isValue x))*)
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ListenExp e')
	    end
	  | evalExp' (AcceptExp (SockExp (SocketPassive sock))) =
	    let
		(*val _ = print ("bad in accept")*)
		val (sock', sa) = Socket.accept sock
		val (ia, port) = INetSock.fromAddr sa
		val ip = NetHostDB.toString ia
	    in 
		(S, A, p, TupleExp [SockExp (SocketActive sock'), StringExp ip, IntExp port])
	    end
	  | evalExp' (AcceptExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', AcceptExp e')
	    end
	  | evalExp' (ConnectExp (TupleExp [SockExp (SocketActive sock), StringExp ip, IntExp port])) =
	    (Socket.connect (sock, 
			     INetSock.toAddr (case (NetHostDB.fromString ip) of
						  SOME x => x
						| _ => raise EvalError "BindExp: bad ip address", 
					     port));
	     (S, A, p, UnitExp))
	  | evalExp' (ConnectExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ConnectExp e')
	    end
	  | evalExp' (SendExp (TupleExp [SockExp (SocketActive sock), StringExp s])) =
	   let 
		fun lp vs = if Word8VectorSlice.isEmpty vs
			    then ()
			    else let
				    val n = Socket.sendVec (sock, vs)
				in lp (Word8VectorSlice.subslice (vs, n, NONE))
				end
	    in
		((lp (Word8VectorSlice.full (Byte.stringToBytes s)));
		 (S, A, p, IntExp (size s)))

	   end

	    (*(S, A, p, IntExp(Socket.sendVec(sock, {buf=Byte.stringToBytes s, i=0, sz = NONE})))*)
	    
	  | evalExp' (SendExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', SendExp e')
	    end
	  | evalExp' (RecvExp (TupleExp [SockExp (SocketActive sock), IntExp i])) =
	    (S, A, p, 
	     StringExp (Byte.bytesToString (Socket.recvVec (sock, i))))
	  | evalExp' (RecvExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', RecvExp e')
	    end
	  | evalExp' (NowExp UnitExp) =
	    (S, A, p, IntExp (LargeInt.toInt (*(LargeInt.fromLarge*) (Time.toSeconds (Time.- (Time.now (), zeroTime)))))
	  | evalExp' (NowExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', NowExp e')
	    end
	  | evalExp' (OpenExp (open_type, StringExp s)) =
	    (case open_type of
		Read => (S, A, p, FileExp (FileRead (TextIO.openIn s)))
	      | Write => (S, A, p, FileExp (FileWrite (TextIO.openOut s)))
	      | Append => (S, A, p, FileExp (FileWrite (TextIO.openAppend s))))
	  | evalExp' (OpenExp (ot, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', OpenExp (ot, e'))
	    end
	  | evalExp' (WriteExp (TupleExp [FileExp (FileWrite outstream), StringExp data])) =
	    (TextIO.output (outstream, data);
	     (TextIO.flushOut outstream);
	     (S, A, p, IntExp (size data)))
	  | evalExp' (WriteExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', WriteExp e')
	    end
	  | evalExp' (ReadExp (TupleExp [FileExp (FileRead instream), IntExp n])) =
	    (S, A, p, StringExp (TextIO.inputN (instream, n)))
	  | evalExp' (ReadExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ReadExp e')
	    end
	  | evalExp' (DeleteExp (StringExp s)) =
	    (OS.FileSys.remove s;
	    (S, A, p, UnitExp))
	  | evalExp' (DeleteExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', DeleteExp e')
	    end
	  | evalExp' (RenameExp (TupleExp [StringExp s1, StringExp s2])) =
	    (OS.FileSys.rename {old=s1, new=s2};
	    (S, A, p, UnitExp))
	  | evalExp' (RenameExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', RenameExp e')
	    end
	  | evalExp' (SizeExp (StringExp s)) =
	    (S, A, p, IntExp (size s))
	  | evalExp' (SizeExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', SizeExp e')
	    end
	  | evalExp' (SleepExp (IntExp i)) =
	    ((OS.Process.sleep (Time.fromSeconds (LargeInt.fromInt i)));
	    (S, A, p, UnitExp))
	  | evalExp' (SleepExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', SleepExp e')
	    end
	  | evalExp' (IndexOfExp (iot, TupleExp [StringExp s1, StringExp s2]))  =
	    let 
		val c = String.sub (s2, 0)
		val cs = String.explode s1
		fun indexhelp iot last count (h::t) = 
		    if (h = c) 
		    then (case iot of
			      First => count
			    | Last => indexhelp iot count (count+1) t)
		    else indexhelp iot last (count+1) t
		  | indexhelp iot last count nil =
		    last
		val index = indexhelp iot ~1 0 cs
	    in
		(S, A, p, IntExp (index))
	    end
	  | evalExp' (IndexOfExp (iot, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', IndexOfExp (iot, e'))
	    end
	  | evalExp' (SubstringExp (TupleExp [StringExp s, IntExp i1, IntExp i2])) =
	    (S, A, p, StringExp (String.substring (s, i1, i2)))
	  | evalExp' (SubstringExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', SubstringExp e')
	    end
	  | evalExp' (ExistsExp (StringExp s)) =
		(S, A, p, ((OS.FileSys.fileId s); TrueExp) handle OS.SysErr _ => FalseExp)
	  | evalExp' (ExistsExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', ExistsExp e')
	    end
	  | evalExp' (MultExp(IntExp i1, IntExp i2)) =
	    (S, A, p, IntExp (i1 * i2))
	  | evalExp' (MultExp(IntExp i1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', MultExp(IntExp i1, e'))
	    end
	  | evalExp' (MultExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', MultExp(e1', e2))
	    end	
	  | evalExp' (DivExp(IntExp i1, IntExp i2)) =
	    (S, A, p, IntExp (Real.floor ((Real.fromInt i1) / (Real.fromInt i2))))
	  | evalExp' (DivExp(IntExp i1, e)) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', DivExp(IntExp i1, e'))
	    end
	  | evalExp' (DivExp(e1, e2)) =
	    let 
		val (S', A', p', e1') = evalExp' e1
	    in
		(S', A', p', DivExp(e1', e2))
	    end	
	  | evalExp' (NegExp TrueExp) =
	    (S, A, p, FalseExp)
	  | evalExp' (NegExp FalseExp) =
	    (S, A, p, TrueExp)
	  | evalExp' (NegExp (IntExp i)) =
	    (S, A, p, IntExp (~i))
	  | evalExp' (NegExp e) =
	    let 
		val (S', A', p', e') = evalExp' e
	    in
		(S', A', p', NegExp e')
	    end
	  | evalExp' e =
	    raise EvalError (PrettyPrint.ppCExp e ^ " is unrecognized.")
    in 
	evalExp'
    end

and evalPat stack latt S A p =
    let 
	fun evalPat' (PtPat(e, x, pat)) =
	    if isValue e
	    then (if isValuePat pat
		  then raise EvalError "PtPat"
		  else let 
			  val (S', A', p', pat') = evalPat' pat
		      in 
			  (S', A', p', PtPat(e, x, pat'))
		      end)
	    else let 
		    val (S', A', p', e') = evalExp stack latt S A p e
		in 
		    (S', A', p', PtPat(e', x, pat))
		end
	  | evalPat' (AllPat pat) =
	    if isValuePat pat
	    then raise EvalError "AllPat"
	    else let 
		    val (S', A', p', pat') = evalPat' pat
		in 
		    (S', A', p', AllPat pat')
		end
	  | evalPat' _ = 
	    raise EvalError "evalPat"
    in
	evalPat'
    end

and splitHelp e (v::v') (x::x') =
    splitHelp (substExp v x e) v' x'
  | splitHelp e nil nil = e
  | splitHelp _ _ _ = raise EvalError "splitHelp"

and splitHelp2 stack latt S A p (e::es) =
    if (isValue e)
    then let
	    val (S', A', p', es') = splitHelp2 stack latt S A p es
	in 
	    (S', A', p', e::es')
	end
    else let 
	    val (S', A', p', e') = evalExp stack latt S A p e
	    val (S'', A'', p'', es') = splitHelp2 stack latt S' A' p' es
	in 
	    (S'', A'', p'', e'::es')
	end
  | splitHelp2 stack latt S A p nil = (S, A, p, nil)
	
and membHelp ((m',t,p,x,e)::tail) m = 
    if (Id.eqid m m')
    then (m,t,p,x,e)
    else membHelp tail m
  | membHelp _ _ = raise EvalError "membHelp"
		
and advComp nil l v = 
    UnitExp
  | advComp (AdvA(e1,x,p,e2)::A) l v =
    if satisfies l e1
    then SeqExp(substExp v x (LowerExp(p,e2)), advComp A l v)
    else advComp A l v
    
and satisfies l (LabSetExp(llist,_)) = 
    List.exists (fn(LabExp x) => (x = l) | _ => raise EvalError "satisfies1") llist
  | satisfies l _ = raise EvalError "satisfies2"
			  
(*and removeEvalExp(e) *)

and subst_list sub e =
    foldr (fn ((v,x),e') => substExp v x e) e sub

(* capture avoiding substitution *)
and substExp v x = 
    let 
	fun substExp' UnitExp = 
	    UnitExp
	  | substExp' (StringExp s) = 
	    StringExp s
	  | substExp' TrueExp =
	    TrueExp
	  | substExp' FalseExp =
	    FalseExp
	  | substExp' (IfExp(e1,e2,e3)) =
	    IfExp(substExp' e1, substExp' e2, substExp' e3)
	  | substExp' (FunExp(p,y,t,e)) =
	    FunExp(p, y, t, 
		   if Id.eqid x y 
		   then e 
		   else substExp' e)
	  | substExp' (LabExp l) = 
	    LabExp l
	  | substExp' (RefExp r) =
	    RefExp r
	  | substExp' (ObjExp(mtps)) =
	    ObjExp(map (fn(m,t,p,y,e) => (m,t,p,y,if Id.eqid x y 
						  then e
						  else substExp' e))
		       mtps)
	  | substExp' (VarExp y) = 
	    if Id.eqid x y 
	    then v 
	    else VarExp y
	  | substExp' (SeqExp(e1,e2)) = 
	    SeqExp(substExp' e1, substExp' e2)
	  | substExp' (PrintExp e) = 
	    PrintExp(substExp' e)
	  | substExp' (AppExp(e1,e2)) = 
	    AppExp(substExp' e1, substExp' e2)
	  | substExp' (AdvExp(e1, y, p, e2)) =
	    AdvExp(substExp' e1, y, p, if Id.eqid x y
				       then e2 
				       else substExp' e2)
	  | substExp' (AdvInstExp e) = 
	    AdvInstExp(substExp' e)
	  | substExp' (NewExp(p,t)) = 
	    NewExp(p,t)
	  | substExp' (PCExp(e1,e2)) = 
	    PCExp(substExp' e1, substExp' e2)
	  | substExp' (NewRefExp(p,e)) =
	    NewRefExp(p, substExp' e)
	  | substExp' (DerefExp e) = 
	    DerefExp(substExp' e)
	  | substExp' (AssignExp(e1,e2)) =
	    AssignExp(substExp' e1, substExp' e2)
	  | substExp' (LowerExp(p,e)) = 
	    LowerExp(p, substExp' e)
	  | substExp' (TupleExp es) =
	    TupleExp (map substExp' es)
	  | substExp' (SplitExp(vars, e1, e2)) =
	    if foldr (fn (y,b) => if Id.eqid x y
				  then true
				  else b)
		     false vars
	    then SplitExp (vars, substExp' e1, e2)
	    else SplitExp (vars, substExp' e1, substExp' e2)
	  | substExp' (LabSetExp(es, p)) =
	    LabSetExp(map substExp' es, p)
	  | substExp' (UnionExp(e1, p, e2)) =
	    UnionExp(substExp' e1, p, substExp' e2)
	  | substExp' (MembExp(e, m)) =
	    MembExp(substExp' e, m)
	  | substExp' StackExp =
	    StackExp 
	  | substExp' NilStExp =
	    NilStExp
	  | substExp' (PtStExp(e1, e2, e3)) =
	    PtStExp(substExp' e1, substExp' e2, substExp' e3)
	  | substExp' (StoreExp(e1, e2, e3)) =
	    StoreExp(substExp' e1, substExp' e2, substExp' e3)
	  | substExp' (CaseExp (e1, pat, e2, e3)) =
	    let 
		val (pat', b) = substPat v x pat
	    in 
		CaseExp(substExp' e1, pat', if b then e2 else substExp' e2, substExp' e3)
	    end
	  | substExp' (ConcatExp (e1, e2)) =
	    ConcatExp (substExp' e1, substExp' e2)
	  | substExp' (PlusExp (e1, e2)) =
	    PlusExp (substExp' e1, substExp' e2)
	  | substExp' (EqExp (e1, e2)) =
	    EqExp (substExp' e1, substExp' e2)
	  | substExp' (GTExp (e1, e2)) =
	    GTExp (substExp' e1, substExp' e2)
	  | substExp' (AbortExp e)=
	    AbortExp (substExp' e)
	  | substExp' (IntExp i) =
	    IntExp i
	  | substExp' (ItoSExp e) =
	    ItoSExp (substExp' e)
	  | substExp' (PosExp (pos, e)) =
	    (PosExp (pos, substExp' e))
	  | substExp' (SocketExp (st, e)) =
	    SocketExp (st, substExp' e)
	  | substExp' (BindExp e) =
	    BindExp (substExp' e)	 
	  | substExp' (ListenExp e) =
	    ListenExp (substExp' e)	  
	  | substExp' (AcceptExp e) =
	    AcceptExp (substExp' e)	  
	  | substExp' (ConnectExp e) =
	    ConnectExp (substExp' e)	  
	  | substExp' (SendExp e) =
	    SendExp (substExp' e)	  
	  | substExp' (RecvExp e) =
	    RecvExp (substExp' e)
	  | substExp' (SockExp s) =
	    SockExp s
	  | substExp' (NowExp e) =
	    NowExp (substExp' e)
	  | substExp' (OpenExp (ot, e)) =
	    OpenExp (ot, substExp' e)
	  | substExp' (WriteExp e) =
	    WriteExp (substExp' e)
	  | substExp' (ReadExp e) =
	    ReadExp (substExp' e)
	  | substExp' (DeleteExp e) =
	    DeleteExp (substExp' e)
	  | substExp' (RenameExp e) =
	    RenameExp (substExp' e)
	  | substExp' (FileExp s) =
	    FileExp s
	  | substExp' (SizeExp e) =
	    SizeExp (substExp' e)
	  | substExp' (SleepExp e) =
	    SleepExp (substExp' e)
	  | substExp' (IndexOfExp (ot, e)) =
	    IndexOfExp (ot, substExp' e)
	  | substExp' (SubstringExp e) =
	    SubstringExp (substExp' e)
	  | substExp' (ExistsExp e) =
	    ExistsExp (substExp' e)
	  | substExp' (MultExp (e1, e2)) =
	    MultExp (substExp' e1, substExp' e2)
	  | substExp' (DivExp (e1, e2)) =
	    DivExp (substExp' e1, substExp' e2)
	  | substExp' (NegExp e) =
	    NegExp (substExp' e)

	    

    in 
	if isValue v
	then substExp'
	else raise EvalError "substExp"
    end

and substPat v x =
    let fun substPat' NilPat =
	    (NilPat, false)
	  | substPat' (PtPat(e,y, pat)) =
	    let 
		val (pat', b) = substPat' pat
	    in 
		(PtPat(substExp v x e, y, pat'), (Id.eqid x y) orelse b)
	    end
	  | substPat' (AllPat pat) =
	    let 
		val (pat', b) = substPat' pat
	    in 
		(AllPat pat', b)
	    end
	  | substPat' (VarPat y) = 
	    (VarPat y, Id.eqid x y)
    in 
	substPat'
    end

and lookupLabS l (LabS(l',t,p)::S) = 
    if (l = l') 
    then (t,p) 
    else lookupLabS l S
  | lookupLabS l (_::S) = lookupLabS l S
  | lookupLabS l nil = raise EvalError "lookupLabS"

and lookupRefS r (RefS(r',e,p)::S) = 
    if (r = r') 
    then (e,p) 
    else lookupRefS r S
  | lookupRefS r (_::S) = lookupRefS r S
  | lookupRefS r nil = raise EvalError "lookupRefS"
 
and pat_match NilStExp NilPat =
    SOME nil
  | pat_match (PtStExp (LabExp l, v1, v2)) (PtPat(LabSetExp (ls,p), x, vpat)) =
    (case pat_match v2 vpat of
	SOME sub => if lab_match l (map (fn (LabExp l') => l'
					  | _ => raise EvalError "PtStExp") 
					ls)
		    then SOME ((v1,x)::sub)
		    else NONE
      | NONE => NONE)
  | pat_match (PtStExp(LabExp l, v1, v2)) (AllPat vpat) =
    pat_match v2 vpat
  | pat_match v (VarPat x) =
    SOME [(v,x)]
  | pat_match _ _ = NONE
		    
and lab_match l ls =
    foldr (fn (l',b) => if (l = l') 
			then true 
			else b)
	  false 
	  ls
	  
end