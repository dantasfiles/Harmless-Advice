signature EVAL =
sig

val eval : ProtDom.lattice -> Core.exp -> Core.exp

val evalDebug : ProtDom.lattice -> Core.exp -> Core.exp

end