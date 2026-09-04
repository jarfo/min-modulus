/-
# Reduction of the primitive Mersenne-capacity residual

The preceding endpoint splits the full-odd-factor middle branch into exact
Mersenne order and two proper-divisor capacity inequalities.  This file turns
those alternatives into structural information.

* the middle binomial coefficient is at least the average binomial layer;
* the merged proper-divisor arm forces cycle length at least `51`;
* the separated proper-divisor arm forces cycle length at least `72930`;
* at exact Mersenne order, a primary union whose translated subset cube fits
  in the odd kernel cannot contain anything beyond the leaf range.

The numerical cutoffs are consequences of general inequalities.  They are
not finite-instance proofs of G1.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneCapacity

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The middle binomial layer is at least the average of all `d+1` layers. -/
theorem two_pow_le_succ_mul_middleChoose (d : ℕ) :
    2 ^ d ≤ (d + 1) * d.choose (d / 2) := by
  rw [← Nat.sum_range_choose]
  calc
    (∑ k ∈ Finset.range (d + 1), d.choose k) ≤
        ∑ _k ∈ Finset.range (d + 1), d.choose (d / 2) := by
      exact Finset.sum_le_sum fun k _hk ↦ Nat.choose_le_middle k d
    _ = (d + 1) * d.choose (d / 2) := by simp

/-- The proper-divisor inequality in the merged three-residue arm has no
solutions below cycle length `51`. -/
theorem fiftyOne_le_of_threeResidueCentral_le_mersenne
    {d u t f : ℕ} (hdu : d ≤ u) (ht : 3 ≤ t)
    (hmain : 3 * (u.choose (u / 2) * t.choose (t / 2) *
      f.choose (f / 2)) ≤ 2 ^ d - 1) :
    51 ≤ d := by
  have hchooseDU : d.choose (d / 2) ≤ u.choose (u / 2) := by
    exact (Nat.choose_le_choose (d / 2) hdu).trans
      (Nat.choose_le_middle (d / 2) u)
  have hchooseT : 3 ≤ t.choose (t / 2) := by
    calc
      3 ≤ t.choose 1 := by simpa using ht
      _ ≤ t.choose (t / 2) := Nat.choose_le_middle 1 t
  have hchooseF : 1 ≤ f.choose (f / 2) := by
    calc
      1 = f.choose 0 := by simp
      _ ≤ f.choose (f / 2) := Nat.choose_le_middle 0 f
  have hscaled : 9 * d.choose (d / 2) ≤ 2 ^ d - 1 := by
    calc
      9 * d.choose (d / 2) =
          3 * (d.choose (d / 2) * 3 * 1) := by ring
      _ ≤ 3 * (u.choose (u / 2) * t.choose (t / 2) *
          f.choose (f / 2)) := by
        exact Nat.mul_le_mul_left 3
          (Nat.mul_le_mul (Nat.mul_le_mul hchooseDU hchooseT) hchooseF)
      _ ≤ 2 ^ d - 1 := hmain
  by_contra hnot
  have hd : d ≤ 50 := by omega
  interval_cases d <;> norm_num [Nat.choose] at hscaled

/-- The proper-divisor inequality in the distinct-coset arm forces an
enormous cycle.  The constant is `3 * choose(17,8)`. -/
theorem seventyTwoThousandNineHundredThirty_le_of_distinctCentral_le_mersenne
    {d s : ℕ} (hs : 16 ≤ s)
    (hmain : 3 * (d.choose (d / 2) *
      (s + 1).choose ((s + 1) / 2)) ≤ 2 ^ d - 1) :
    72930 ≤ d := by
  have hchooseD : 0 < d.choose (d / 2) :=
    Nat.choose_pos (Nat.div_le_self d 2)
  have hchooseS : 24310 ≤ (s + 1).choose ((s + 1) / 2) := by
    calc
      24310 = (17 : ℕ).choose 8 := by norm_num [Nat.choose]
      _ ≤ (s + 1).choose 8 := Nat.choose_le_choose 8 (by omega)
      _ ≤ (s + 1).choose ((s + 1) / 2) :=
        Nat.choose_le_middle 8 (s + 1)
  have hscaled : 72930 * d.choose (d / 2) < 2 ^ d := by
    have hle : 72930 * d.choose (d / 2) ≤
        3 * (d.choose (d / 2) *
          (s + 1).choose ((s + 1) / 2)) := by
      calc
        72930 * d.choose (d / 2) =
            3 * (d.choose (d / 2) * 24310) := by ring
        _ ≤ 3 * (d.choose (d / 2) *
            (s + 1).choose ((s + 1) / 2)) := by
          exact Nat.mul_le_mul_left 3
            (Nat.mul_le_mul_left (d.choose (d / 2)) hchooseS)
    have hpowPos : 0 < 2 ^ d := pow_pos (by decide) d
    omega
  have havg := two_pow_le_succ_mul_middleChoose d
  have hcancel : 72930 < d + 1 := by
    apply (Nat.mul_lt_mul_right hchooseD).mp
    exact hscaled.trans_le havg
  omega

/-- At exact Mersenne order, the general valid-subtuple capacity leaves no
room for even one coordinate beyond an injective `d`-coordinate leaf range. -/
theorem primaryUnion_eq_leafRange_of_exactMersenne_capacity
    {d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (U : Finset (Fin n))
    (hsub : (Finset.univ : Finset (Fin d)).image leaf ⊆ U)
    (hcap : 2 ^ (U.card - 1) ≤ 2 ^ d - 1) :
    U = (Finset.univ : Finset (Fin d)).image leaf := by
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hLsub : L ⊆ U := hsub
  have hUcard : U.card ≤ d := by
    by_contra hnot
    have hdu : d ≤ U.card - 1 := by omega
    have hpow : 2 ^ d ≤ 2 ^ (U.card - 1) :=
      Nat.pow_le_pow_right (by omega) hdu
    have hpowPos : 0 < 2 ^ d := pow_pos (by decide) d
    omega
  have hcardEq : U.card = L.card := by
    have hcardLe : L.card ≤ U.card := Finset.card_le_card hLsub
    omega
  exact (Finset.eq_of_subset_of_card_le hLsub (by omega)).symm

/-- The Mersenne-capacity split with its proper-divisor arms converted to
uniform dimension lower bounds. -/
theorem PrimitiveMiddleWindowedCriticalCosetResidual.mersenneDimensionSplit
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (hresidual :
      PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf) :
    q = 2 ^ d - 1 ∨
      (∃ u t f : ℕ,
        51 ≤ d ∧ d ≤ u ∧ 3 ≤ t ∧
        (∀ i j k : ℕ, u.choose i * t.choose j * f.choose k ≤ q) ∧
        3 * (u.choose (u / 2) * t.choose (t / 2) *
          f.choose (f / 2)) ≤ 2 ^ d - 1 ∧
        48 * (u.choose (u / 2) * f.choose (f / 2)) < 2 ^ B.card) ∨
      (∃ s : ℕ,
        72930 ≤ d ∧ 16 ≤ s ∧
        (∀ i j : ℕ, d.choose i * (s + 1).choose j ≤ q) ∧
        3 * (d.choose (d / 2) * (s + 1).choose ((s + 1) / 2)) ≤
          2 ^ d - 1 ∧
        388960 * d.choose (d / 2) < 2 ^ B.card) := by
  rcases hresidual.mersenneCapacitySplit
      g hg y hyq hfullOdd B hretained hcritical leaf hleaf
        R hRcycle hRne base hdouble hspan with
    hExact | hmerged | hdistinct
  · exact Or.inl hExact
  · rcases hmerged with
      ⟨u, t, f, hdu, ht, hcap, hcentral, hcrit⟩
    exact Or.inr (Or.inl ⟨u, t, f,
      fiftyOne_le_of_threeResidueCentral_le_mersenne hdu ht hcentral,
      hdu, ht, hcap, hcentral, hcrit⟩)
  · rcases hdistinct with ⟨s, hs, hcap, hcentral, hcrit⟩
    exact Or.inr (Or.inr ⟨s,
      seventyTwoThousandNineHundredThirty_le_of_distinctCentral_le_mersenne
        hs hcentral,
      hs, hcap, hcentral, hcrit⟩)

/-- In the exact-Mersenne branch, the merged primary union is exactly the
leaf range (and hence has at least seventeen leaves); otherwise the original
distinct-coset capacity arm remains. -/
theorem PrimitiveMiddleWindowedCriticalCosetResidual.exactMersenneCollapse
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (hqExact : q = 2 ^ d - 1)
    (hresidual :
      PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf) :
    (∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      ∃ S U : Finset (Fin n), ∃ k₀ : ℤ,
        U = (Finset.univ : Finset (Fin d)).image leaf ∧
        16 ≤ S.card ∧ 17 ≤ d ∧
        PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ ∧
        48 * U.card.choose (U.card / 2) < 2 ^ B.card) ∨
      (∃ s : ℕ,
        16 ≤ s ∧
        (∀ i j : ℕ, d.choose i * (s + 1).choose j ≤ q) ∧
        388960 * d.choose (d / 2) < 2 ^ B.card) := by
  classical
  rcases hresidual with
    ⟨p, S, k₀, _hprimitive, hScard, _hSsub, _hmiddle, _hrows,
      _hScomplete, _hwindow, hCcard, hcase⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r S
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  let U : Finset (Fin n) := L ∪ C
  rcases hcase with hmerged | hdistinct
  · rcases hmerged with
      ⟨hUcap, _hUcoset, _hUgap, _hfive, _hseparated,
        hsecondary, hcritical⟩
    have hcapMersenne : 2 ^ (U.card - 1) ≤ 2 ^ d - 1 := by
      simpa only [hqExact] using hUcap
    have hUeq : U = L := by
      apply primaryUnion_eq_leafRange_of_exactMersenne_capacity leaf hleaf U
      · exact Finset.subset_union_left
      · simpa only [L] using hcapMersenne
    have hCsub : C ⊆ U := Finset.subset_union_right
    have hCcardLe : C.card ≤ U.card := Finset.card_le_card hCsub
    have hUcard : U.card = d := by
      rw [hUeq]
      simp only [L]
      rw [Finset.card_image_of_injective _ hleaf]
      simp
    have hdSeventeen : 17 ≤ d := by
      rw [hCcard, hUcard] at hCcardLe
      omega
    exact Or.inl ⟨p, S, U, k₀, by simpa only [L] using hUeq,
      hScard, hdSeventeen, hsecondary, hcritical⟩
  · rcases hdistinct with ⟨_hcross, hcap, hcritical⟩
    exact Or.inr ⟨S.card, hScard, hcap, hcritical⟩

end MinModulus
