structure Harmless :> HARMLESS = 
struct

open PrettyPrint

fun run s =
    let 
	val tabsyn = Parse.parse s
	val (latt, typ, absyn) = Translate.translate tabsyn
	val tc = TypeCheck.typecheck latt absyn
    in
	if tc
	then print (ppCExp (Eval.eval latt absyn))
	else ()
    end

fun eval s =
    let 
	val tabsyn = Parse.parse s
	val (latt, typ, absyn) = Translate.translate tabsyn
	val tc = TypeCheck.typecheck latt absyn
    in
	if tc
	then print (ppCExp (Eval.evalDebug latt absyn))
	else ()
    end

fun parse s = 
	Parse.parse s

fun translate s = 
    let 
	val tabsyn = Parse.parse s
	val (latt, typ, absyn) = Translate.translate tabsyn
				 
    in 
	print (ppCExp absyn)

    end

fun lattice s = 
    let 
	val tabsyn = Parse.parse s
	val (latt, typ, absyn) = Translate.translate tabsyn
				 
    in 
	print (ProtDom.lattice2string latt)
    end
	
end
	
	