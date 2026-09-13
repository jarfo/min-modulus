# Quadratic incidence counts for repeated values

The elementary inequality

    2*r <= 3+binomial(r,2)

holds for every natural r and is exact at r=2 and r=3. Empty fibres are
handled separately, so the constant term is charged only to occupied
repeated values. This gives, for any tuple, any residual degree k and
any selected finite value set Y,

    2*sum_(x in Y) |R_k(x)|
      <= 3*|D_(k+2) intersect Y|
         + sum_(x in Y) binomial(|R_k(x)|,2).

Neither tuple validity nor oddness is needed for this counting step.
At odd modulus, summing the verified escape supply for a valid tuple
then gives, with E=2*C_(k+1) and k>=1,

    2*(n-(2k+2))*binomial(n,2k)
      <= 3*|D_(2k+2) without E|
         + sum_(x outside E) binomial(|R_(2k)(x)|,2).

These first two results hold in arbitrary degree and are the main
counting improvement. They account exactly for the contribution of
fibres of size two or three, where the earlier inequality
r<=1+binomial(r,2) loses more information.

For quartic degree, write B=binomial(n,2) and let C count the exceptional
unordered anchor pairs defined in `QuarticCollisionBounds.lean`. Its
proved collision cap is 6*B+(n-9)*C. Combining the two estimates shows
that for n>=12 at odd modulus, the explicit hypothesis

    (n-9)*C <= (n-12)*B

implies both

    |D_4 without 2*C_2| >= binomial(n,3),
    |D_4| >= binomial(n+1,2)+binomial(n,3).

This weakens the earlier criterion 3*(n-9)*C<=2*(n-14)*B for n>=14.
The allowed proportion C/B now tends to one as n grows. The hypothesis
is still explicit; it is not asserted for arbitrary valid tuples.
Dense exceptional cases remain to be controlled, and quartic degree
alone does not establish the absolute central inequalities or generic G2.
G1 and G3 also remain open.

All four original proofs pass both Mathlib revisions. Fourteen exact
declaration types and five definition values agree, and the compiler
axiom audit finds only standard Lean axioms. No new definition is needed.
Split Prove2Me export and publication remain.
