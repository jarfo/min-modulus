# Valid odd cyclic tuples embed into every larger dimension

[ValidTupleOddExtension.lean](ValidTupleOddExtension.lean) proves three
uniform extension results, with no finite search.

* If g is a valid n-tuple in an abelian group G and p>n+1, adjoining
  (0,1) to the coordinates (g_i,0) in G x ZMod p preserves validity.
* A valid tuple at odd cyclic order embeds into a valid tuple with one
  additional coordinate at another odd cyclic order.
* Iterating gives a valid tuple in every dimension n+r. The original
  coordinates are preserved through an index embedding and an injective
  additive homomorphism, so every original additive relation persists.

For the first result, projecting a rival multiplicity vector onto the
new cyclic factor gives k_0=1 modulo p. Its total size bounds k_0 by n+1,
so k_0=1 as a natural number. The original validity then forces every
remaining multiplicity to be one. For the cyclic result, choose an odd
prime p>N+n+2 and transport the product tuple through the Chinese
remainder equivalence ZMod(N*p) = ZMod N x ZMod p.

All three original proof bodies pass Lean 4.32 and Lean 4.33.1 against
the original and supported Mathlib revisions. Four exact declaration
types, the ValidTuple definition value, and standard-axiom audits match.
The build uses selective caches and at most four compiler threads.

The construction can carry a fixed structural obstruction into the
range of arbitrarily large dimensions. The current application under
construction is an invisible cubic coefficient for every diagonal probe
matrix. That application is not yet claimed here.

The enlarged modulus can be large. This construction does not preserve
an upper bound N<2^n-1 and gives no min-modulus counterexample. Matrix
injectivity for unrestricted matrices, the central repeated-sum bounds,
and generic G1/G2/G3 remain open. Platform export and upload of these
three extension statements remain.
