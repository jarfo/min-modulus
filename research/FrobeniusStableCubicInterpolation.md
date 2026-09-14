# Frobenius stability does not replace cyclic-orbit structure

A symbolic six-point construction strengthens the existing obstruction to
an unrestricted characteristic-two interpolation bound. Let K be any field
of characteristic two containing w with w^2+w+1=0. Take the six points

    (1,w,1), (1,w+1,1), (1,1,w), (1,1,w+1),
    (1,w,w), (1,w+1,w+1).

They are distinct, every coordinate is nonzero and has cube one, and
coordinatewise squaring exchanges the points in three pairs. For every
homogeneous cubic f, the sum of its six evaluations, all with weight one,
equals the coefficient of x*y*z.

The finite-field instance uses K=GF(4). Thus torus coordinates, unit weights,
and closure under Frobenius do not imply an unrestricted 2^3-1=7 point
lower bound. In particular, adding Frobenius stability to the earlier
six-point obstruction does not repair that proposed rank argument.

The construction is explicitly not one full cyclic multiplicative orbit.
The formal proof allows arbitrary reordering, starting point and coordinate
multipliers. The first two orbit points would force every multiplier to
have cube one; the fourth point would then repeat the first, contradicting
distinctness. The cyclic structure required by the actual min-modulus
character representation has not been reproduced.

This is not a valid cyclic tuple or a counterexample to min-modulus. It does
not refute CR1, whose central degrees start at four, or even an unrestricted
2^n-2 point bound. A future algebraic argument must justify all the orbit
structure it needs; Frobenius invariance alone is insufficient for the
seven-point claim refuted here.

Five original proofs cover the point properties, monomial moments, arbitrary
homogeneous cubics, the cyclic-enumeration obstruction and the GF(4) witness.
The calculations are symbolic in w. No valid-set enumeration or exclusion
campaign is used. The two helpers concerning a cubic root, and the
squarefree exponent definition, come from CharTwoSixPointInterpolation.lean.
Both Lean/Mathlib revisions pass: five proofs, nine exact declaration types,
two definition values, and only standard axioms. All five results are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](FrobeniusStableCubicResearch.md). G1, G2, G3 and CR1 remain open.
