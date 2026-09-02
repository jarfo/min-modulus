/-
# Nonvacuous local-light exact-profile descent

Combine the protected minimal-support descent with the two localized
lightness splits.  A singleton transversal gives the exact half-modulus
recursion.  For a larger transversal, a locally light pure root and private
family fire critical crossing.  Failure of either local condition retains a
structured pure-edge-heavy or private-heavy residual.
-/
import MinModulus.G1ProfilePureEdgeLightSplit

namespace MinModulus

open Finset

/-- The selected private-heavy residual retains the protected quarter layer,
its actual minimal transversal, the longer recursive tuple already obtained
by deleting that transversal, and the concrete private tail-heavy witness. -/
def ProfilePrivateTailHeavyDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    ∃ B : Finset (Fin (n + 1)),
    ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
      t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧
      ∃ b : {b : Fin (n + 1) // b ∈ B}, ∃ k : Fin n,
        2 ≤ minimalSupportPrivateWitness g (M : ZMod N)
          hmin b k.succ

/-- Generic assembly of the local pure-root/private-family splits around one
already constructed protected minimal descent. -/
theorem critical_largeCross_or_singletonHalfDescent_or_localHeavy_of_rootSplit
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hexWitness : ∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c)
    (hroot :
      (∃ r : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        r ∈ criticalCanonicalReducedCollisions g ∧
          2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r) ∨
        WitnessTailHeavyPureEdge g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (t : ZMod (2 ^ (s + 1) * q)) (qv : Fin (n + 1) → ℤ)
    (B : Finset (Fin (n + 1)))
    (ht : t + t =
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hqv : Witness g t qv)
    (hBsub : B ⊆ Finset.univ \ coefficientSupport qv)
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hrec : AdmitsValidTupleWithWitness
      (n + 1 - B.card) (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g := by
  have hBpos : 0 < B.card := by
    obtain ⟨c, hc⟩ := hexWitness
    exact Finset.card_pos.mpr
      (MinimalWitnessSupportTransversal.nonempty_of_witness hmin hc)
  by_cases hBcard : 2 ≤ B.card
  · rcases hroot with ⟨r, hr, hrweight⟩ | hpureHeavy
    · by_cases hlocal : MinimalSupportPrivateWitnessesTailLight g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
      · exact Or.inl
          (critical_largeCross_of_highWeightCanonical_and_minimalSupportPrivate_localLight
            hq hnseven g hg r hr hrweight hmin hlocal hBcard)
      · obtain ⟨b, k, hk⟩ :=
          exists_minimalSupportPrivateWitness_tailHeavy_of_not_localLight
            g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin hlocal
        exact Or.inr (Or.inr (Or.inr
          ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard, b, k, hk⟩))
    · exact Or.inr (Or.inr (Or.inl hpureHeavy))
  · have hBone : B.card = 1 := by omega
    exact Or.inr (Or.inl (by simpa [hBone] using hrec))

/-- Nonvacuous local-light endpoint for the `(0,0,2)` exact profile. -/
theorem critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_or_localHeavy
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hMpos : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
  let hh := half_add_half hN
  have hs : 1 ≤ s :=
    one_le_criticalIndex_of_zeroZeroTwo_profile hq g hg hprofile
  have hM : 2 ^ s * q = 2 * (2 ^ (s - 1) * q) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have hK : 0 < 2 ^ (s - 1) * q :=
    mul_pos (pow_pos (by norm_num) _) (Odd.pos hq)
  have hroot0 := exists_zeroZeroTwo_pureEdgeCanonical_weight_or_tailHeavy
    g hh (half_ne_zero hN hMpos) hprofile
  have hroot :
      (∃ r : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        r ∈ criticalCanonicalReducedCollisions g ∧
          2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r) ∨
        WitnessTailHeavyPureEdge g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
    rcases hroot0 with ⟨r, hr, hrweight⟩ | hheavy
    · exact Or.inl ⟨r, by
        simpa [hh, criticalCanonicalReducedCollisions] using hr, hrweight⟩
    · exact Or.inr hheavy
  obtain ⟨t, qv, ht, hqv, B, hBsub, hmin, hrec, _hprivate⟩ :=
    exactTriangleZeroZeroTwo_minimalSupportDescent
      hN hM hK g hg hprofile
  have hexWitness : ∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c := by
    obtain ⟨cAB, _cBD, _cDA, _a, _b, _d, hcAB, _hcBD, _hcDA,
      _hab, _hbd, _hda, _hAB, _hBD, _hDA, _hABd, _hBDa, _hDAb⟩ :=
        hprofile
    exact ⟨cAB, hcAB⟩
  exact critical_largeCross_or_singletonHalfDescent_or_localHeavy_of_rootSplit
    hq hnseven g hg hexWitness hroot t qv B ht hqv hBsub hmin hrec

/-- Nonvacuous local-light endpoint for the all-zero exact profile. -/
theorem critical_largeCross_or_allZero_singletonHalfDescent_or_localHeavy
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hMpos : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
  let hh := half_add_half hN
  have hs : 1 ≤ s := one_le_criticalIndex_of_allZero_profile
    hq g hg hprofile
  have hM : 2 ^ s * q = 2 * (2 ^ (s - 1) * q) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have hK : 0 < 2 ^ (s - 1) * q :=
    mul_pos (pow_pos (by norm_num) _) (Odd.pos hq)
  have hroot0 := exists_allZero_pureEdgeCanonical_weight_or_tailHeavy
    g hg hh (half_ne_zero hN hMpos) hprofile
  have hroot :
      (∃ r : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        r ∈ criticalCanonicalReducedCollisions g ∧
          2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r) ∨
        WitnessTailHeavyPureEdge g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
    rcases hroot0 with ⟨r, hr, hrweight⟩ | hheavy
    · exact Or.inl ⟨r, by
        simpa [hh, criticalCanonicalReducedCollisions] using hr, hrweight⟩
    · exact Or.inr hheavy
  obtain ⟨t, qv, ht, hqv, B, hBsub, hmin, hrec, _hprivate⟩ :=
    exactTriangleAllZero_minimalSupportDescent
      hN hM hK g hg hprofile
  have hexWitness : ∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c := by
    obtain ⟨cAB, _cBD, _cDA, _a, _b, _d, hcAB, _hcBD, _hcDA,
      _hab, _hbd, _hda, _hAB, _hBD, _hDA, _hABd, _hBDa, _hDAb⟩ :=
        hprofile
    exact ⟨cAB, hcAB⟩
  exact critical_largeCross_or_singletonHalfDescent_or_localHeavy_of_rootSplit
    hq hnseven g hg hexWitness hroot t qv B ht hqv hBsub hmin hrec

end MinModulus
