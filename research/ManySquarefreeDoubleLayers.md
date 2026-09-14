# Exponentially many full layers at one central-degree value

The exact squarefree-double decomposition includes every multiplicity
pattern, but its layers can overlap substantially even in the sharp valid
examples. For every m>=1, take

    n = 6*m, N = 2^(6*m)-1, g_i = 2^i modulo N, k = 3*m.

The tuple is valid, N is odd, and k is the central degree. There exists a
repeated degree-k value x lying in at least 2^m distinct layers

    sum g(S) + 2*C_m, with |S|=m.

This counts distinct squarefree remainders, not different representations
inside a single layer. It is a symbolic construction for arbitrary m,
with no finite enumeration. It is not a counterexample to min-modulus:
the modulus already equals the predicted sharp odd bound.

The construction uses four coordinates per independent block. In block j,

    2*g_(4j) = g_(4j+1),   2*g_(4j+2) = g_(4j+3).

Choose either the remainder coordinate 4j+1 and halved coordinate 4j+2,
or the remainder coordinate 4j+3 and halved coordinate 4j. Both choices
contribute g_(4j+1)+g_(4j+3) to the same value. Choices in the m blocks
are independent. Reading the coordinates 4j+1 recovers the choice set,
so the resulting 2^m remainders are distinct. Each halved part has m
coins and each remainder has m coordinates, giving total degree 3*m.

The first theorem proves this count for any tuple equipped with an
injective indexing of the four-coordinate blocks and the two doubling
identities. It needs neither validity nor oddness. The second theorem
realizes it inside the valid Mersenne family and also proves that the
common value belongs to the repeated cover.

This rules out a constant bound on the number of full layers through each
value. It does not refute weighted or aggregate overlap estimates. The
remaining goal is a lower bound on the entire repeated-cover union at
both central degrees; generic G1, G2 and G3 remain open.

Both original proofs pass the original Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997 and supported revision
0df444a360eaa60ab8c11dca51a86af692955474. Twelve declaration types and
six existing definition values agree, with standard axioms only. The
supported check composes two existing small roadmap module bodies in its
owned directory to retain both the G2 interface and the already proved
canonical-validity transport. Shared caches are unchanged.
Split Prove2Me export and publication remain.
