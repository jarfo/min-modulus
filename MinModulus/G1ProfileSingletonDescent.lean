/-
# Exact-profile singleton descent

The pure-star dichotomy forces a minimal protected support transversal to be
a singleton whenever critical crossing is small in dimension at least seven.
This file combines that dichotomy with the previously existential protected
quarter descent.  The result directly exposes the recursive object needed by
the global lower-bound induction: a valid `n`-tuple at half the modulus,
still carrying the transported quarter witness.
-/
import MinModulus.G1AllZeroPureStar
import MinModulus.GlobalRoadmap

namespace MinModulus

open Finset

/-- Forgetting the retained witness leaves an admitted valid tuple. -/
theorem AdmitsValidTupleWithWitness.admitsValidTuple
    {n N : ℕ} {h : ZMod N}
    (hex : AdmitsValidTupleWithWitness n N h) : AdmitsValidTuple n N := by
  obtain ⟨g, hg, _c, _hc⟩ := hex
  exact ⟨g, hg⟩

/-- A critical `(0,0,2)` profile forces positive two-adic depth: its quarter
point makes the modulus divisible by four, while the cofactor is odd. -/
theorem one_le_criticalIndex_of_zeroZeroTwo_profile
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    1 ≤ s := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hquarter := exactTriangleZeroZeroTwo_quarterPoint
    g hg (half_add_half hN) hprofile
  exact one_le_criticalIndex_of_four_dvd hq
    (quarterPoint_four_dvd_zmod hN hquarter)

/-- A critical all-zero profile likewise forces positive two-adic depth. -/
theorem one_le_criticalIndex_of_allZero_profile
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    1 ≤ s := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hfour : 4 ∣ 2 ^ (s + 1) * q := by
    obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
      hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
    exact four_dvd_of_triangle_all_zero_zmod hN g hg
      hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hABd hBDa hDAb
  exact one_le_criticalIndex_of_four_dvd hq hfour

/-- In dimension at least seven, an all-tail-light `(0,0,2)` profile either
fires critical large crossing or directly supplies the recursive valid
`n`-tuple at half modulus, with its previous-layer half witness retained. -/
theorem critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_of_seven_le
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hs : 1 ≤ s :=
    one_le_criticalIndex_of_zeroZeroTwo_profile hq g hg hprofile
  have hM : 2 ^ s * q = 2 * (2 ^ (s - 1) * q) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have hK : 0 < 2 ^ (s - 1) * q :=
    mul_pos (pow_pos (by norm_num) _) (Odd.pos hq)
  obtain ⟨t, qv, ht, hqv, hdesc⟩ :=
    exactTriangleZeroZeroTwo_minimalSupportDescent
      hN hM hK g hg hprofile
  obtain ⟨B, _hBsub, hmin, hrec, _hprivate⟩ := hdesc
  rcases
      critical_largeCross_or_zeroZeroTwo_minimalSupport_card_eq_one_of_seven_le
        hq hnseven g hg hprofile hmin hallLight with hcross | hBcard
  · exact Or.inl hcross
  · exact Or.inr (by simpa [hBcard] using hrec)

/-- In dimension at least seven, an all-tail-light all-zero profile has the
same exact recursive alternative. -/
theorem critical_largeCross_or_allZero_singletonHalfDescent_of_seven_le
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTupleWithWitness n (2 ^ s * q)
        ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hs : 1 ≤ s := one_le_criticalIndex_of_allZero_profile
    hq g hg hprofile
  have hM : 2 ^ s * q = 2 * (2 ^ (s - 1) * q) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have hK : 0 < 2 ^ (s - 1) * q :=
    mul_pos (pow_pos (by norm_num) _) (Odd.pos hq)
  obtain ⟨t, qv, ht, hqv, hdesc⟩ :=
    exactTriangleAllZero_minimalSupportDescent
      hN hM hK g hg hprofile
  obtain ⟨B, _hBsub, hmin, hrec, _hprivate⟩ := hdesc
  rcases
      critical_largeCross_or_allZero_minimalSupport_card_eq_one_of_seven_le
        hq hnseven g hg hprofile hmin hallLight with hcross | hBcard
  · exact Or.inl hcross
  · exact Or.inr (by simpa [hBcard] using hrec)

/-- Forgetting the retained quarter witness gives the exact recursive
alternative consumed by the global lower-bound induction. -/
theorem critical_largeCross_or_zeroZeroTwo_admitsHalf_of_seven_le
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTuple n (2 ^ s * q) := by
  rcases critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_of_seven_le
      hq hnseven g hg hprofile hallLight with hcross | hrec
  · exact Or.inl hcross
  · exact Or.inr hrec.admitsValidTuple

/-- The all-zero profile has the same global-induction interface. -/
theorem critical_largeCross_or_allZero_admitsHalf_of_seven_le
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTuple n (2 ^ s * q) := by
  rcases critical_largeCross_or_allZero_singletonHalfDescent_of_seven_le
      hq hnseven g hg hprofile hallLight with hcross | hrec
  · exact Or.inl hcross
  · exact Or.inr hrec.admitsValidTuple

end MinModulus
