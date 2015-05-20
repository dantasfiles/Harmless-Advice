signature TRANSLATE =
sig

    val translate : Source.prog -> ProtDom.lattice * Source.typ * Core.exp

end