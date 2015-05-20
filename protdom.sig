signature PROTDOM =
sig

type lattice
type p = Id.id

val empty_prot : lattice

val add_prot : lattice -> p -> p -> lattice

val leq_prot : lattice -> p -> p -> bool

val eq_prot : p -> p -> bool

val lattice2string : lattice -> string

end
