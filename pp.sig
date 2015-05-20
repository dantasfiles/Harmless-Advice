signature PRETTYPRINT = 
sig

val ppVar : Id.id -> string 

val ppCTyp : Core.typ -> string

val ppCExp : Core.exp -> string

val ppSTyp : Source.typ -> string

val ppProt : ProtDom.p -> string

end