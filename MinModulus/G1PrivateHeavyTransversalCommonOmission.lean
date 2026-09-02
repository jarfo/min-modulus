/-
# Common omissions forced by private transversal cycles

Witness combination says that two witnesses at an involution either are
exact negatives or share an omitted coordinate.  A crossed zero/nonzero
incidence rules out exact negation.  Distinct private witnesses therefore
share an omission outside the minimal transversal.  In a transversal
two-cycle, the two avoiding witnesses also share an omission, necessarily
away from both cycle vertices.
-/
import MinModulus.G1PrivateHeavyTransversalSimpleCycle

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A single crossed zero/nonzero coordinate rules out the exact-negation
arm of witness combination and therefore forces a shared omission. -/
theorem exists_common_omission_of_witness_ne_zero_zero
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {c c' : Fin m → ℤ}
    (hc : Witness g h c) (hc' : Witness g h c')
    {x : Fin m} (hcx : c x ≠ 0) (hc'x : c' x = 0) :
    ∃ z : Fin m, c z = -1 ∧ c' z = -1 := by
  by_contra hnone
  have hshare : ∀ z, ¬ (c z = -1 ∧ c' z = -1) := by
    intro z hz
    exact hnone ⟨z, hz⟩
  have hneg := witness_combination g hg hh hc hc' hshare
  have hx := congrFun hneg x
  simp only [Pi.neg_apply, hc'x] at hx
  exact hcx (by omega)

/-- Private witnesses at two distinct vertices of a minimal support
transversal always share an omitted coordinate outside the transversal. -/
theorem
    exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b u : {i : Fin m // i ∈ B}) (hbu : b ≠ u) :
    ∃ z : Fin m, z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      minimalSupportPrivateWitness g h hmin u z = -1 := by
  have hbune : (b : Fin m) ≠ u := by
    intro hval
    exact hbu (Subtype.ext hval)
  have hcuzero := minimalSupportPrivateWitness_eq_zero_of_ne
    g h hmin u b.property hbune
  obtain ⟨z, hcbz, hcuz⟩ :=
    exists_common_omission_of_witness_ne_zero_zero
      g hg hh
      (minimalSupportPrivateWitness_isWitness g h hmin b)
      (minimalSupportPrivateWitness_isWitness g h hmin u)
      (minimalSupportPrivateWitness_ne_zero g h hmin b) hcuzero
  have hzexternal : z ∉ B := by
    intro hzB
    by_cases hzb : z = b
    · have hcuzero' := minimalSupportPrivateWitness_eq_zero_of_ne
        g h hmin u hzB (by
          intro hzu
          exact hbu (Subtype.ext (hzb.symm.trans hzu)))
      omega
    · have hcbzero := minimalSupportPrivateWitness_eq_zero_of_ne
        g h hmin b hzB hzb
      omega
  exact ⟨z, hzexternal, hcbz, hcuz⟩

/-- The two-cycle branch carries two common-omission certificates.  The
private pair shares an omission outside all of `B`; the avoiding pair shares
an omission away from the two cycle vertices. -/
theorem minimalSupportTransversalShift_twoCycle_commonOmissions
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B})
    (hcycle :
      (minimalSupportTransversalShiftTarget g hno hmin)^[2] b = b) :
    let T := minimalSupportTransversalShiftTarget g hno hmin
    let u := T b
    let cb := minimalSupportPrivateWitness g h hmin b
    let cu := minimalSupportPrivateWitness g h hmin u
    let rb := minimalSupportAvoidingWitness g hno b
    let ru := minimalSupportAvoidingWitness g hno u
    ∃ z w : Fin m,
      T u = b ∧ u ≠ b ∧ z ∉ B ∧
      cb z = -1 ∧ cu z = -1 ∧
      w ≠ b ∧ w ≠ u ∧ rb w = -1 ∧ ru w = -1 := by
  dsimp
  let T := minimalSupportTransversalShiftTarget g hno hmin
  let u := T b
  have hback : T u = b := by
    simpa [T, u, Function.iterate_succ_apply] using hcycle
  have hune : u ≠ b :=
    minimalSupportTransversalShiftTarget_ne g hno hmin b
  obtain ⟨z, hzB, hcbz, hcuz⟩ :=
    exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
      g hg hh hmin b u hune.symm
  obtain ⟨w, hrbw, hruw⟩ :=
    exists_common_omission_of_witness_ne_zero_zero
      g hg hh
      (minimalSupportAvoidingWitness_isWitness g hno b)
      (minimalSupportAvoidingWitness_isWitness g hno u)
      (minimalSupportAvoidingWitness_target_ne_zero g hno hmin b)
      (minimalSupportAvoidingWitness_eq_zero g hno u)
  have hwb : w ≠ b := by
    intro hwb
    subst w
    have := minimalSupportAvoidingWitness_eq_zero g hno b
    omega
  have hwu : w ≠ u := by
    intro hwu
    subst w
    have := minimalSupportAvoidingWitness_eq_zero g hno u
    omega
  exact ⟨z, w, hback, hune, hzB, hcbz, hcuz,
    hwb, hwu, hrbw, hruw⟩

end MinModulus
