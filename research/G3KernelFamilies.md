# Simultaneous compatible families of kernel witnesses

The earlier G3 construction gives a witness separately for each avoided
coordinate. [G3KernelFamilies.lean](G3KernelFamilies.lean) now constructs a
whole compatible family from one quotient fibre, with a quantitative
lower bound on the number of distinct targets.

Let f:G->H be a homomorphism of additive abelian groups, with H finite,
and let g be a valid n-tuple in G. Let A be any set of coordinate indices.
For arbitrary natural numbers k and r, assume

    |H|*r < binomial(|A|,k).

There is a finite family F of integer coefficient vectors such that:

* F contains zero and has more than r members.
* Every member sums to zero, vanishes outside A, and has weighted target
  h(c)=sum_i c(i)g(i) in ker(f).
* Every difference c-d between members has all coefficients in {-1,0,1}.
* The targets h(c) are pairwise distinct.

Consequently there are at least r distinct nonzero kernel targets,
each represented by a reversible witness supported in A. All differences
between distinct family members are also reversible witnesses, at their
nonzero target differences. The zero vector is a distinguished family
member, not a witness under the existing nonzero-witness definition.

## Construction

Pigeonhole the k-element subsets of A by their sums in H. One fibre E has
more than r subsets. Choose one T in E and put

    c_S = 1_S - 1_T,  for S in E.

The map S->c_S is injective, and c_T=0. All vectors have zero total sum
because S and T have the same cardinality. All weighted targets lie in
ker(f) because S and T have the same projected sum. The common reference
subset is what makes the entire family compatible:

    c_S - c_U = 1_S - 1_U.

If two distinct members had the same target upstairs, their difference
would be a nonzero zero-target witness, contradicting validity. Negating
a difference preserves admissibility because every coefficient is
bounded above by one as well as below by minus one.

## G3 use and remaining gap

Apply the theorem to reduction modulo the Mersenne odd factor q of the
exceptional modulus Kq. Taking A to omit a prescribed coordinate set
forces every vector in the family to avoid that entire set. The number
of nonzero targets is bounded below by any r satisfying

    q*r < binomial(|A|,k).

This strengthens separate witness existence into a simultaneous family
and controls all its pairwise differences. It does not force one common
target across different quotient fibres or different choices of A, and
it does not force the involution target. A relation between those
families, or a stronger use of the cyclic kernel, is still needed.
The count alone does not exceed the K available kernel targets.

## Verification

Four theorems pass Lean 4.32.0 and the supported Lean 4.33.1 revision.
Seven literal declaration types and the three definition values Witness,
ValidTuple and globalBound match exactly. Only standard axioms occur.
The previously verified balanced-kernel and middle-layer sources and
objects were reused as dependencies. No finite enumeration was used.

These results are locally verified and recorded in the mission plan.
No platform theorem node is claimed for this file yet. G1, G2, G3 and
the main arbitrary-n conjecture remain open.
