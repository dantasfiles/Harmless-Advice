signature HARMLESS =
sig

    val run : string -> unit

    val eval : string -> unit

    val parse : string -> Source.prog
			  
    val translate : string -> unit

    val lattice : string -> unit

end