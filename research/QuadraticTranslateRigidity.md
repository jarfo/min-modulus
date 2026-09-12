# Quadratic translates in the generic proof

Let g be a valid n-tuple, A its coordinate set, C_2=A+A, and let t be
outside A. The new uniform rigidity statement is:

* If g_j+t=g_b+g_c with b!=c, every index a with g_a+t in C_2 belongs
  to {j,b,c}. Hence this translate has at most three coordinate hits.
* If there are at least four hits, every hit is a doubled coordinate.
* For n>=4, A+t contained in C_2 therefore implies A+t contained in 2·A.
  This recovers the affine-doubling class from a quadratic containment.

The first claim follows from validity of squarefree triples. An index a
outside {j,b,c}, together with a representation g_a+t=g_u+g_v, would give
g_a+g_b+g_c=g_j+g_u+g_v. The left side is squarefree and the right side
uses the outside index j, a contradiction. The outside-shift assumption
ensures that j differs from b and c.

A cover A+t contained in 2·A supplies an injection from every C_(d-1)
into D_d: translate the sum by t and replace one selected coin a+t by a
doubled coordinate. Thus every required growth inequality holds. At odd
order the existing general reduction proves N>=2^n-1.

Consequently a hypothetical odd counterexample, for n>=4, has

    {t : A+t is contained in A+A} = A.

For any distinct b,c, the midpoint t=(g_b+g_c)/2 lies outside A. Applying
the escape property and doubling gives some a for which 2g_a+g_b+g_c
lies outside 2·C_2. This is a nonempty-neighbor result for every pair;
it does not establish the number of independent quartic values needed.

All nine declarations in [QuadraticTranslateRigidity.lean](QuadraticTranslateRigidity.lean)
pass both Lean revisions, with fifteen literal type/standard-axiom checks
and seven matching definition values. These statements are uniform in n
and N; the Lean proof uses no finite modulus or tuple enumeration.
General G2 and the full conjecture remain open.

## A counting mechanism to investigate

Over F_2, define a formal derivation by

    delta_M(x_b) = sum_a M[a,b] x_a^2.

Apply it to the squarefree cubic monomials indexed by triples T, evaluate
monomials as residues, and discard the rows in E_4=2·C_2. The resulting
matrix has rows outside E_4 and columns T. Its entry at (y,T) is the parity
of the terms M[a,b] with b in T and
y=2g_a+sum_{c in T without b} g_c. Every row is a repeated quartic value.
Full column rank would give

    |D_4| >= binomial(n+1,2) + binomial(n,3).

This is the absolute quartic bound. It does not by itself prove the
stronger relative inequality |D_4|>=|C_3|, nor the bounds at every degree.

An exact finite probe on the 770 previously saved valid tuples of dimensions
4 through 10 finds a binary matrix M of full column rank in every case.
The fixed identity matrix fails in 154 cases; allowing M to vary succeeds
within at most sixteen trials. Independent expansion by the remaining
coordinate pair and row elimination verifies all 770 saved witnesses.
These are finite certificates for a proposed mechanism, not a general
matrix-existence proof. No new tuple or modulus enumeration was performed.

A simple multiplicity cap cannot replace the independence argument:
(0,20,21,63,66,206,239) modulo 373 is valid, but residue 126 belongs to
six different translates 2a+C_2. The complete seven-multiset validity
check and all six representations are saved with the experiment. This
refutes a cap of four even in the half-degree range n=7,d=4; it does not
refute the growth inequality or G2.

Next mathematical work must establish enough independence or a global
counting inequality. The proved escape property only guarantees individual
neighbors. Keep arbitrary n and all required coin degrees in scope.
