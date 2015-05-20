structure ProtDom :> PROTDOM =
struct

structure Env = RedBlackMapFn(type ord_key=Id.id 
			      val compare = Id.compareid)

type lattice = (Id.id list) Env.map
type p = Id.id

val empty_prot = Env.empty

fun eq_prot p1 p2 = Id.eqid p1 p2

fun add_prot latt p1 p2 = 
    let 
	val latt' = (case Env.find(latt, p2) of
			 NONE => Env.insert(latt, p2, nil)
		       | SOME _ => latt)
    in 
	case Env.find(latt,p1) of
	    NONE => Env.insert(latt', p1, [p2])
	  | SOME p1s => Env.insert(latt', p1, p2::p1s)
    end
    
fun leq_prot latt p1 p2 =
    if (eq_prot p1 p2) 
    then true
    else (case Env.find(latt, p1) of
	      NONE => false
	    | SOME p1s => foldr (fn (p,b) => leq_prot latt p p2) false p1s)

fun lattice2string latt =
    Env.foldli (fn (p,ps,s) => (foldl (fn(p',s') => Id.id2string p ^ " <= " ^ Id.id2string p' ^ "\n" ^ s')) s ps) "" latt


end