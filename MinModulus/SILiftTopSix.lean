import MinModulus.SILiftSporadic
import MinModulus.SILiftClassify

/-!
# The top-stratum child obligations at `n = 6`

The joint induction `S*(n,s)` needs, at the top stratum, that every lift of
every class of `L(n-1, m-1)` to `B(n)` is affine-super-increasing.  For
`n = 6` the child stratum is `(5,1)`, whose class list is the
super-increasing class together with four sporadics, and the parent
modulus is `B(6) = 2 ^ 6 - 2 ^ 2 = 60`.

Both halves are settled here, for an ARBITRARY affine presentation of the
child — any deleted coordinate, any permutation, any unit, any constant,
any sheet pattern:

* the super-increasing child lifts only to affine-`SI₆`;
* each of the four sporadic children admits no valid lift at all.

`n = 6` is the only dimension where sporadic children occur, and it is also
the smallest dimension the general classification reaches.
-/

namespace MinModulus

section TopSix

/-- `1 ≤ 4`, the stratum condition at `(m, t) = (4, 1)`. -/
private lemma h14 : (1 : ℕ) ≤ 4 := by norm_num

/-- **The super-increasing child at `n = 6`.**  Its lifts are exactly the
affine-`SI₆` tuples: the extra entry reduces to `2 ^ 5 - 1`. -/
theorem topSix_si (G : Fin 6 → ZMod (siFull 4 1)) (d : Fin 6)
    (σ : Fin 5 ≃ Fin 5) (u : (ZMod (siFull 4 1))ˣ) (c : ZMod (siFull 4 1))
    (b : ℕ → ℕ)
    (hchild : ∀ i : Fin 5, G (d.succAbove (σ i))
      = (u : ZMod (siFull 4 1)) * ((2 ^ i.val - 1 : ℕ) : ZMod (siFull 4 1))
        + c + (b i.val) • siSheet 4 1)
    (hv : ValidTuple G) :
    siReduce h14
        (((u⁻¹ : (ZMod (siFull 4 1))ˣ) : ZMod (siFull 4 1)) * (G d - c))
      = siReduce h14 ((2 ^ 5 - 1 : ℕ) : ZMod (siFull 4 1)) :=
  siLift_affine_extra h14 (by norm_num) (by norm_num) (by norm_num)
    G d σ u c b hchild hv

/-- **The sporadic children at `n = 6`.**  No affine image of any of the
four sporadic `(5,1)` classes is the deletion-child of a valid tuple
modulo `60`. -/
theorem topSix_sporadic_not_valid (A : Fin 5 → ZMod (siFull 4 1))
    (hA : A = sporA ∨ A = sporB ∨ A = sporC ∨ A = sporD)
    (G : Fin 6 → ZMod (siFull 4 1)) (d : Fin 6)
    (σ : Fin 5 ≃ Fin 5) (u : (ZMod (siFull 4 1))ˣ) (c : ZMod (siFull 4 1))
    (b : ℕ → ℕ)
    (hchild : ∀ i : Fin 5, G (d.succAbove (σ i))
      = (u : ZMod (siFull 4 1)) * A i + c + (b i.val) • siSheet 4 1) :
    ¬ ValidTuple G := by
  intro hv
  have hnorm := siLiftParent_affine_normalize h14 A G d σ u c b hchild hv
  rcases hA with rfl | rfl | rfl | rfl
  · exact sporA_not_valid b _ hnorm
  · exact sporB_not_valid b _ hnorm
  · exact sporC_not_valid b _ hnorm
  · exact sporD_not_valid b _ hnorm

end TopSix

end MinModulus
