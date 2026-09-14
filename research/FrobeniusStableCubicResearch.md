# Verified Frobenius-stable cubic obstruction

Five proofs strengthen the obstruction to an unrestricted characteristic-two
cubic interpolation bound. Six distinct torus points, closed under squaring,
extract the squarefree coefficient of every homogeneous cubic with unit
weights. The construction works over any characteristic-two field containing
a nontrivial cube root, and is realized over GF(4).

These six points cannot form one full multiplicative cyclic orbit, even
with arbitrary starting point and reordering. Their coordinate cubes force
any proposed orbit multiplier to have cube one, so the fourth point would
repeat the first. This isolates a missing structural hypothesis in that
proposed rank argument. It does not refute CR1, an unrestricted 2^n-2 point
bound, or min-modulus. G1/G2/G3 and CR1 remain open.
The original proofs are in FrobeniusStableCubicInterpolation.lean.

All five results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify five
original target types and dependency sets, two original inline helper types
and two definition values. One shared definition bundle contains the point
configuration and squarefree exponent; no external theorem interface is
needed. One supporting root retains the full symbolic obstruction.

The consolidated DAG has 1268 nodes and 2901 edges. All 829 exact proof dependency sets across 59 bundles match. G1/P6, G2/From7, G3/From7 and CR1 remain open.

CR1 and generic G1/G2/G3 remain open; this is an obstruction to a different rank claim.

* frobeniusCubicPoints_properties: 6312af83-32d0-42b0-86a5-9962f620ef4b
* frobeniusCubicPoints_moments: 550af21b-252b-4bd9-b2f0-c98df4f5fcef
* frobeniusCubicPoints_interpolation: 32ddcb12-ff89-490e-adda-b440dbc7b4e7
* frobeniusCubicPoints_not_cyclic_enumeration: 5388dc12-3936-4d5f-8d6a-ef01111efd60
* frobenius_stable_six_point_counterexample: 640b3df1-2fd2-40f3-98db-ab17590172f4
