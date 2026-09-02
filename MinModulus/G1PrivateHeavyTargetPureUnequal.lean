/-
# Normalizing witnesses distinct from the retained pure target

The pure target has coefficient `2` at one center, `-1` at two endpoints,
and `0` everywhere else.  Consequently any directed coefficient gap from a
witness with floor `-1` into the pure target must occur at the center.  The
other witness has coefficient `-1` or `0` there.  Its protected heavy
coordinate therefore moves away from the center, while validity supplies a
reverse gap at a second coordinate.  Privacy localizes that reverse gap to
the witness owner or outside the transversal.

This argument needs only distinctness, not equality of the two private
owners, so it simultaneously strengthens the unequal same-owner and
different-owner arms of the preceding comparison.
-/
import MinModulus.G1PrivateHeavyTargetPureEquality

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A floor-`-1` vector can have a directed gap into a nondegenerate pure
edge only at its coefficient-`2` center. -/
theorem coefficientGap_into_pureEdge_eq_center
    (c : Fin (m + 1) → ℤ) (e z x i : Fin (m + 1))
    (hez : e ≠ z) (hex : e ≠ x) (hxz : x ≠ z)
    (hcFloor : ∀ a, -1 ≤ c a)
    (hi : c i + 2 ≤ pureEdgeCoeffs e z x i) :
    i = e := by
  by_cases hie : i = e
  · exact hie
  by_cases hiz : i = z
  · subst i
    have hc := hcFloor z
    simp [pureEdgeCoeffs, Ne.symm hez, Ne.symm hxz] at hi
    omega
  by_cases hix : i = x
  · subst i
    have hc := hcFloor x
    simp [pureEdgeCoeffs, Ne.symm hex, hxz] at hi
    omega
  have hc := hcFloor i
  simp [pureEdgeCoeffs, hie, hiz, hix] at hi
  omega

omit [DecidableEq G] in
/-- Exact center-drop/reverse-gap geometry for any protected private-heavy
witness distinct from the retained pure target. -/
theorem minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hc : Witness g h c)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m) (hk : 2 ≤ c k.succ)
    (hkLocation : k.succ = owner ∨ k.succ ∉ B)
    (hne : c ≠ minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)) :
    ∃ x : Fin (m + 1), ∃ e : Fin m, ∃ j : Fin (m + 1),
      x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ y, minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) y = -1 ↔
        y = z ∨ y = x) ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) =
        pureEdgeCoeffs e.succ z x ∧
      (c e.succ = -1 ∨ c e.succ = 0) ∧
      k.succ ≠ e.succ ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) j + 2 ≤ c j ∧
      j ≠ e.succ ∧ (j = owner ∨ j ∉ B) ∧
      ((owner : Fin (m + 1)) = e.succ → k.succ ∉ B ∧ j ∉ B) := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  have hp : Witness g h p :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  obtain ⟨x, e, hxz, hez, hex, homit, heTwo, hshape⟩ := hpure
  obtain ⟨i, hiGap⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg hc hp (by simpa [p, u] using hne)
  have hiPure : c i + 2 ≤ pureEdgeCoeffs e.succ z x i := by
    calc
      c i + 2 ≤ p i := hiGap
      _ = pureEdgeCoeffs e.succ z x i := by
        simpa [p, u] using congrFun hshape i
  have hiCenter : i = e.succ := coefficientGap_into_pureEdge_eq_center
    c e.succ z x i hez hex hxz hc.2.1 hiPure
  have hcCenterCases : c e.succ = -1 ∨ c e.succ = 0 := by
    have hcFloor := hc.2.1 e.succ
    have hcenterGap : c e.succ + 2 ≤
        pureEdgeCoeffs e.succ z x e.succ := by
      simpa [hiCenter] using hiPure
    have hpureCenter : pureEdgeCoeffs e.succ z x e.succ = 2 := by
      simp [pureEdgeCoeffs, hez, hex]
    rw [hpureCenter] at hcenterGap
    omega
  obtain ⟨j, hjGap⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg hp hc (by
      intro heq
      apply hne
      simpa [p, u] using heq.symm)
  have hjCenter : j ≠ e.succ := by
    intro hje
    subst j
    have hpCenter : p e.succ = 2 := by simpa [p, u] using heTwo
    rcases hcCenterCases with hcNeg | hcZero <;> omega
  have hjLocation : j = owner ∨ j ∉ B := by
    by_cases hjo : j = owner
    · exact Or.inl hjo
    · right
      intro hjB
      have hcZero := hprivate j hjB hjo
      have hpFloor := hp.2.1 j
      omega
  have hkCenter : k.succ ≠ e.succ := by
    intro hke
    rw [hke] at hk
    rcases hcCenterCases with hcNeg | hcZero <;> omega
  refine ⟨x, e, j, hxz, hez, hex, homit, heTwo, hshape,
    hcCenterCases, hkCenter, ?_, hjCenter, hjLocation, ?_⟩
  · simpa [p, u] using hjGap
  · intro hownerCenter
    constructor
    · rcases hkLocation with hkOwner | hkExternal
      · exact (hkCenter (hkOwner.trans hownerCenter)).elim
      · exact hkExternal
    · rcases hjLocation with hjOwner | hjExternal
      · exact (hjCenter (hjOwner.trans hownerCenter)).elim
      · exact hjExternal

end MinModulus
