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

/-- The pure-edge-heavy residual retains the same protected descent data as
the private-heavy branch instead of discarding the already constructed
minimal transversal and longer recursive tuple. -/
def ProfilePureEdgeTailHeavyDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    ∃ B : Finset (Fin (n + 1)),
      MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
      t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧ WitnessTailHeavyPureEdge g (M : ZMod N)

/-- The selected private-heavy residual retains the protected quarter layer,
its actual minimal transversal, the longer recursive tuple already obtained
by deleting that transversal, and the concrete private tail-heavy witness. -/
def ProfilePrivateTailHeavyDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    ∃ B : Finset (Fin (n + 1)),
      MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
      t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧
      ∃ b : {b : Fin (n + 1) // b ∈ B},
        ∃ c : Fin (n + 1) → ℤ, ∃ k : Fin n,
          Witness g (M : ZMod N) c ∧ c b ≠ 0 ∧
          (∀ a ∈ B, a ≠ b → c a = 0) ∧ 2 ≤ c k.succ

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
      ProfilePureEdgeTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
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
          ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
            b, minimalSupportPrivateWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin b,
            k, minimalSupportPrivateWitness_isWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin b,
            minimalSupportPrivateWitness_ne_zero g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin b,
            (fun a ha hne ↦ minimalSupportPrivateWitness_eq_zero_of_ne g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
                hmin b ha hne),
            hk⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard, hpureHeavy⟩))
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
      ProfilePureEdgeTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
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

/-- Sharpened `(0,0,2)` endpoint using the shared endpoints of its heavy pure
edge and protected quarter pair.  If the displayed edge is tail-heavy, the
external transversal can meet it only at its center, so it is already a
private heavy witness.  No pure-edge double-hit branch survives. -/
theorem critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_or_privateHeavy
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g := by
  classical
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
  obtain ⟨t, x, y, a, b, d, c, B,
    hxy, hab, hxa, hxb, hya, hyb, hda, hdb,
    hc, homit, hcd, hpure, ht, hqv, hBsub, hmin, hrec, _hprivate⟩ :=
    exactTriangleZeroZeroTwo_linkedMinimalSupportDescent
      hN hM hK g hg hprofile
  have hBpos : 0 < B.card := Finset.card_pos.mpr
    (MinimalWitnessSupportTransversal.nonempty_of_witness hmin hc)
  by_cases hBcard : 2 ≤ B.card
  · by_cases hlight : ∀ k : Fin n, c k.succ ≤ 1
    · obtain ⟨r, hr, hrweight⟩ :=
        exists_exactPairTwo_pureEdgeCanonical_weight
          g hh (half_ne_zero hN hMpos) hc a b d hab homit
            hda hdb hcd hlight
      have hrCritical : r ∈ criticalCanonicalReducedCollisions g := by
        simpa [hh, criticalCanonicalReducedCollisions] using hr
      by_cases hlocal : MinimalSupportPrivateWitnessesTailLight g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
      · exact Or.inl
          (critical_largeCross_of_highWeightCanonical_and_minimalSupportPrivate_localLight
            hq hnseven g hg r hrCritical hrweight hmin hlocal hBcard)
      · obtain ⟨owner, k, hk⟩ :=
          exists_minimalSupportPrivateWitness_tailHeavy_of_not_localLight
            g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin hlocal
        exact Or.inr (Or.inr
          ⟨t, balancedPairCoeffs x y a b, B, hmin, ht, hqv, hBsub,
            hrec, hBcard, owner,
            minimalSupportPrivateWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            k, minimalSupportPrivateWitness_isWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            minimalSupportPrivateWitness_ne_zero g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            (fun u hu hne ↦ minimalSupportPrivateWitness_eq_zero_of_ne g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
                hmin owner hu hne),
            hk⟩)
    · push Not at hlight
      obtain ⟨k, hk⟩ := hlight
      have haNotB : a ∉ B := by
        intro haB
        have haOutside := hBsub haB
        have haNotSupport := (Finset.mem_sdiff.mp haOutside).2
        apply haNotSupport
        rw [coefficientSupport_balancedPairCoeffs
          x y a b hxy hab hxa hxb hya hyb]
        simp
      have hbNotB : b ∉ B := by
        intro hbB
        have hbOutside := hBsub hbB
        have hbNotSupport := (Finset.mem_sdiff.mp hbOutside).2
        apply hbNotSupport
        rw [coefficientSupport_balancedPairCoeffs
          x y a b hxy hab hxa hxb hya hyb]
        simp
      obtain ⟨z, hzB, hcz⟩ := hmin.1 c hc
      have hzSupport : z ∈ ({d, a, b} : Finset (Fin (n + 1))) := by
        apply pureEdgeCoeffs_ne_zero_mem d a b z
        rwa [← hpure]
      have hdB : d ∈ B := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzSupport
        rcases hzSupport with hzd | hza | hzb
        · simpa [hzd] using hzB
        · exact False.elim (haNotB (hza ▸ hzB))
        · exact False.elim (hbNotB (hzb ▸ hzB))
      have hprivateZero : ∀ u ∈ B, u ≠ d → c u = 0 := by
        intro u huB hud
        by_contra hcu
        have huSupport : u ∈ ({d, a, b} : Finset (Fin (n + 1))) := by
          apply pureEdgeCoeffs_ne_zero_mem d a b u
          rwa [← hpure]
        simp only [Finset.mem_insert, Finset.mem_singleton] at huSupport
        rcases huSupport with hud' | hua | hub
        · exact hud hud'
        · exact haNotB (hua ▸ huB)
        · exact hbNotB (hub ▸ huB)
      exact Or.inr (Or.inr
        ⟨t, balancedPairCoeffs x y a b, B, hmin, ht, hqv, hBsub,
          hrec, hBcard, ⟨d, hdB⟩, c, k, hc,
          by simpa using (show c d ≠ 0 by omega),
          hprivateZero, by omega⟩)
  · have hBone : B.card = 1 := by omega
    exact Or.inr (Or.inl (by simpa [hBone] using hrec))

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
      ProfilePureEdgeTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
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

/-- Sharpened all-zero endpoint using the aligned `cBD` pure edge.  Its center
`y` and endpoint `d` are protected, so the minimal transversal can meet its
three-coordinate support only at the other endpoint `b`.  A tail-heavy edge
is consequently private at `b`, and no double-hit branch survives. -/
theorem critical_largeCross_or_allZero_singletonHalfDescent_or_privateHeavy
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g := by
  classical
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
  obtain ⟨t, x, d, y, z, b, c, B,
    hxd, hyz, hxy, hxz, hdy, hdz, hyb, hyd, hbd,
    hc, homit, hcy, hpure, ht, hqv, hBsub, hmin, hrec, _hprivate⟩ :=
    exactTriangleAllZero_linkedMinimalSupportDescent
      hN hM hK g hg hprofile
  have hBpos : 0 < B.card := Finset.card_pos.mpr
    (MinimalWitnessSupportTransversal.nonempty_of_witness hmin hc)
  by_cases hBcard : 2 ≤ B.card
  · by_cases hlight : ∀ k : Fin n, c k.succ ≤ 1
    · obtain ⟨r, hr, hrweight⟩ :=
        exists_exactPairTwo_pureEdgeCanonical_weight
          g hh (half_ne_zero hN hMpos) hc b d y hbd homit
            hyb hyd hcy hlight
      have hrCritical : r ∈ criticalCanonicalReducedCollisions g := by
        simpa [hh, criticalCanonicalReducedCollisions] using hr
      by_cases hlocal : MinimalSupportPrivateWitnessesTailLight g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
      · exact Or.inl
          (critical_largeCross_of_highWeightCanonical_and_minimalSupportPrivate_localLight
            hq hnseven g hg r hrCritical hrweight hmin hlocal hBcard)
      · obtain ⟨owner, k, hk⟩ :=
          exists_minimalSupportPrivateWitness_tailHeavy_of_not_localLight
            g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin hlocal
        exact Or.inr (Or.inr
          ⟨t, balancedPairCoeffs x d y z, B, hmin, ht, hqv, hBsub,
            hrec, hBcard, owner,
            minimalSupportPrivateWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            k, minimalSupportPrivateWitness_isWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            minimalSupportPrivateWitness_ne_zero g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin owner,
            (fun u hu hne ↦ minimalSupportPrivateWitness_eq_zero_of_ne g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
                hmin owner hu hne),
            hk⟩)
    · push Not at hlight
      obtain ⟨k, hk⟩ := hlight
      have hyNotB : y ∉ B := by
        intro hyB
        have hyOutside := hBsub hyB
        have hyNotSupport := (Finset.mem_sdiff.mp hyOutside).2
        apply hyNotSupport
        rw [coefficientSupport_balancedPairCoeffs
          x d y z hxd hyz hxy hxz hdy hdz]
        simp
      have hdNotB : d ∉ B := by
        intro hdB
        have hdOutside := hBsub hdB
        have hdNotSupport := (Finset.mem_sdiff.mp hdOutside).2
        apply hdNotSupport
        rw [coefficientSupport_balancedPairCoeffs
          x d y z hxd hyz hxy hxz hdy hdz]
        simp
      obtain ⟨u, huB, hcu⟩ := hmin.1 c hc
      have huSupport : u ∈ ({y, b, d} : Finset (Fin (n + 1))) := by
        apply pureEdgeCoeffs_ne_zero_mem y b d u
        rwa [← hpure]
      have hbB : b ∈ B := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at huSupport
        rcases huSupport with huy | hub | hud
        · exact False.elim (hyNotB (huy ▸ huB))
        · simpa [hub] using huB
        · exact False.elim (hdNotB (hud ▸ huB))
      have hprivateZero : ∀ u ∈ B, u ≠ b → c u = 0 := by
        intro u huB hub
        by_contra hcu'
        have huSupport' : u ∈ ({y, b, d} : Finset (Fin (n + 1))) := by
          apply pureEdgeCoeffs_ne_zero_mem y b d u
          rwa [← hpure]
        simp only [Finset.mem_insert, Finset.mem_singleton] at huSupport'
        rcases huSupport' with huy | hub' | hud
        · exact hyNotB (huy ▸ huB)
        · exact hub hub'
        · exact hdNotB (hud ▸ huB)
      have hcb : c b ≠ 0 := by
        have hcb' : c b = -1 := (homit b).2 (Or.inl rfl)
        omega
      exact Or.inr (Or.inr
        ⟨t, balancedPairCoeffs x d y z, B, hmin, ht, hqv, hBsub,
          hrec, hBcard, ⟨b, hbB⟩, c, k, hc,
          by simpa using hcb, hprivateZero, by omega⟩)
  · have hBone : B.card = 1 := by omega
    exact Or.inr (Or.inl (by simpa [hBone] using hrec))

end MinModulus
