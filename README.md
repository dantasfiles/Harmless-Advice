This is the language interpreter and security case study for *Harmless Advice* by Daniel S. Dantas and David Walker, presented at the ACM symposium on Principles of Programming Languages 

https://dl.acm.org/citation.cfm?id=1111071

> This paper defines an object-oriented language with harmless aspect-oriented advice. A piece of harmless advice is a computation that, like ordinary aspect-oriented advice, executes when control reaches a designated control-flow point. However, unlike ordinary advice, harmless advice is designed to obey a weak noninterference property. Harmless advice may change the termination behavior of computations and use I/O, but it does not otherwise influence the final result of the mainline code. The benefit of harmless advice is that it facilitates local reasoning about program behavior. More specifically, programmers may ignore harmless advice when reasoning about the partial correctness properties of their programs. In addition, programmers may add new pieces of harmless advice to pre-existing programs in typical 'after-the-fact' aspect-oriented style without fear they will break important data invariants used by the mainline code.

> The paper also presents an implementation of the language and a case study using harmless advice to implement security policies."
