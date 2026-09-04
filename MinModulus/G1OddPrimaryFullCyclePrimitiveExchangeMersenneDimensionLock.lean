/-
# Dimension lock for the exact Mersenne leaf residual

At modulus `2^6 * (2^d - 1)`, the universal valid-tuple cardinality
bound already gives `n <= d + 6`.  This has two strong consequences for
the exact-Mersenne leaf endpoint.

* Any coordinate family disjoint from an injective `d`-coordinate leaf
  range has cardinality at most six.  Hence the separated exact-Mersenne
  coset arm, whose inserted primary class has at least seventeen coordinates,
  is impossible.
* In the merged arm the leaf cycle plus the five separated deleted
  coordinates gives the reverse inequality `d + 6 <= n`.  Thus equality
  holds throughout: `n = d + 6`, `|B| = d + 4`, and exactly five deleted
  coordinates lie outside the leaf cycle.  Criticality then forces
  `d <= 57`; the saturated primary fiber gives `17 <= d`.

This is a general cardinality rigidity argument, not an enumeration of the
remaining dimensions.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLeafSaturation

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A valid tuple over the sixth-stratum exact Mersenne modulus has dimension
at most the Mersenne exponent plus six. -/
theorem exactMersenne_validTuple_dimension_le
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (hq : q = 2 ^ d - 1) :
    n ≤ d + 6 := by
  have hcard := two_pow_pred_le_card_of_validTuple g hg
  rw [ZMod.card] at hcard
  have hdpos : 0 < 2 ^ d := pow_pos (by decide) d
  have hambient : 2 ^ 6 * q < 2 ^ (d + 6) := by
    rw [hq, pow_add]
    norm_num
    omega
  have hpow : 2 ^ (n - 1) < 2 ^ (d + 6) := hcard.trans_lt hambient
  have hexp : n - 1 < d + 6 :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow
  omega

/-- A valid tuple over the sixth-stratum exact Mersenne modulus has room for
at most six coordinates disjoint from an injective `d`-coordinate family. -/
theorem exactMersenne_disjoint_leafRange_card_le_six
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (C : Finset (Fin n))
    (hdisjoint : Disjoint
      ((Finset.univ : Finset (Fin d)).image leaf) C)
    (hq : q = 2 ^ d - 1) :
    C.card ≤ 6 := by
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hunionCard : L.card + C.card = (L ∪ C).card := by
    rw [Finset.card_union_of_disjoint hdisjoint]
  have hunionLe : (L ∪ C).card ≤ n := by
    simpa using Finset.card_le_univ (L ∪ C)
  have hnUpper := exactMersenne_validTuple_dimension_le g hg hq
  omega

/-- In the critical merged endpoint, exact Mersenne order locks the ambient
and transversal dimensions; criticality also bounds the Mersenne exponent. -/
theorem exactMersenne_critical_dimension_lock
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (hq : q = 2 ^ d - 1)
    (hlower :
      ((Finset.univ : Finset (Fin d)).image leaf).card + 4 ≤ B.card) :
    n = d + 6 ∧ B.card = d + 4 ∧ d ≤ 57 := by
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hBcardLe : B.card ≤ n := by
    simpa using Finset.card_le_univ B
  have hnLower : d + 6 ≤ n := by
    change L.card + 4 ≤ B.card at hlower
    omega
  have hnUpper := exactMersenne_validTuple_dimension_le g hg hq
  have hn : n = d + 6 := by omega
  have hBcard : B.card = d + 4 := by omega
  have hdUpper : d ≤ 57 := by
    by_contra hdNot
    have hpowLe : 2 ^ 6 ≤ n := by
      rw [hn]
      norm_num
      omega
    have hlog : 6 ≤ Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      exact hpowLe
    have hbound : stratumBound n 6 = 2 ^ 6 * q := by
      rw [stratumBound, min_eq_left hlog, hq, hn, pow_add]
      norm_num
      omega
    rw [hbound] at hcritical
    omega
  exact ⟨hn, hBcard, hdUpper⟩

/-- The exact-Mersenne merged survivor after the universal dimension bound is
installed.  Its apparent large-dimensional family is locked to a finite
codimension-six window, with exactly five deleted coordinates off the leaf
cycle. -/
def PrimitiveMiddleExactMersenneDimensionLockedResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S T Sfull : Finset (Fin n), ∃ k₀ w : ℤ,
      PrimitiveMiddleExactMersenneFixedPresentationData
        g y B leaf p S T Sfull k₀ w ∧
      let r := primitiveMiddleInsertedCoordinate p k₀
      let C := insert r Sfull
      let L := (Finset.univ : Finset (Fin d)).image leaf
      ∃ missing : Fin d,
        (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
        leaf missing = r ∧
        C = L ∧ Sfull = L.erase r ∧ Sfull.card + 1 = d ∧
        w = -2 ∧
        (∀ i, addOrderOf (g (leaf i) - base) = q) ∧
        2 ^ (L.card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ L,
          g b - g c ∈ AddSubgroup.zmultiples y) ∧
        L.card + 4 ≤ B.card ∧
        5 ≤ (B \ L).card ∧
        (∀ b ∈ B \ L, ∀ c ∈ L,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        PrimitiveSaturatedSecondaryResidueCapacity g y B L p k₀ ∧
        48 * L.card.choose (L.card / 2) < 2 ^ B.card ∧
        n = d + 6 ∧ B.card = d + 4 ∧
        (B \ L).card = 5 ∧ 17 ≤ d ∧ d ≤ 57

/-- The separated exact-Mersenne arm is too large even for the universal
valid-tuple cardinality floor.  The surviving merged arm has exact ambient,
transversal, and external-fiber dimensions. -/
theorem PrimitiveMiddleExactMersenneLeafSaturationResidual.toDimensionLockedResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hq : q = 2 ^ d - 1)
    (hresidual :
      PrimitiveMiddleExactMersenneLeafSaturationResidual
        g y B leaf base) :
    PrimitiveMiddleExactMersenneDimensionLockedResidual
      g y B leaf base := by
  classical
  rcases hresidual with ⟨p, S, T, Sfull, k₀, w, hfixed, hcase⟩
  rcases hfixed with
    ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
      hrows, hcomplete, hwindow⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r Sfull
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  change
    ((∃ missing : Fin d,
        (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
        leaf missing = r ∧
        C = L ∧ Sfull = L.erase r ∧ Sfull.card + 1 = d ∧
        w = -2 ∧
        (∀ i, addOrderOf (g (leaf i) - base) = q) ∧
        2 ^ (L.card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ L,
          g b - g c ∈ AddSubgroup.zmultiples y) ∧
        L.card + 4 ≤ B.card ∧
        5 ≤ (B \ L).card ∧
        (∀ b ∈ B \ L, ∀ c ∈ L,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        PrimitiveSaturatedSecondaryResidueCapacity g y B L p k₀ ∧
        48 * L.card.choose (L.card / 2) < 2 ^ B.card) ∨
      ((∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        (∀ i j : ℕ,
          d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
        388960 * d.choose (d / 2) < 2 ^ B.card)) at hcase
  rcases hcase with hmerged | hseparated
  · rcases hmerged with
      ⟨missing, hpunctured, hmissing, hCeq, hSeq, hcard,
        hw, hleafOrder, hLcap, hLcoset, hLgap, hfive,
        hseparated, hsecondary, hcriticalBound⟩
    obtain ⟨hn, hBcard, hdUpper⟩ :=
      exactMersenne_critical_dimension_lock
        g hg B hretained hcritical leaf hleaf hq hLgap
    have hLcard : L.card = d := by
      simp only [L]
      rw [Finset.card_image_of_injective _ hleaf]
      simp
    have hrNotB : r ∉ B := by
      intro hrB
      have hbad : missing ≠ missing :=
        (hpunctured missing).1 (by simpa only [hmissing] using hrB)
      exact hbad rfl
    have hSsubL : Sfull ⊆ L := by
      rw [hSeq]
      exact Finset.erase_subset _ _
    have hBinterL : B ∩ L = Sfull := by
      ext b
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hbB, hbL⟩
        rw [hSeq]
        exact Finset.mem_erase.mpr
          ⟨fun hbr ↦ hrNotB (hbr ▸ hbB), hbL⟩
      · intro hbS
        exact ⟨hSsub hbS, hSsubL hbS⟩
    have hdecomp := Finset.card_sdiff_add_card_inter B L
    rw [hBinterL, hBcard] at hdecomp
    have hexternal : (B \ L).card = 5 := by omega
    have hdLower : 17 ≤ d := by omega
    refine ⟨p, S, T, Sfull, k₀, w, ?_, ?_⟩
    · exact ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
        hrows, hcomplete, hwindow⟩
    · change ∃ missing : Fin d,
        (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
        leaf missing = r ∧
        C = L ∧ Sfull = L.erase r ∧ Sfull.card + 1 = d ∧
        w = -2 ∧
        (∀ i, addOrderOf (g (leaf i) - base) = q) ∧
        2 ^ (L.card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ L,
          g b - g c ∈ AddSubgroup.zmultiples y) ∧
        L.card + 4 ≤ B.card ∧
        5 ≤ (B \ L).card ∧
        (∀ b ∈ B \ L, ∀ c ∈ L,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        PrimitiveSaturatedSecondaryResidueCapacity g y B L p k₀ ∧
        48 * L.card.choose (L.card / 2) < 2 ^ B.card ∧
        n = d + 6 ∧ B.card = d + 4 ∧
        (B \ L).card = 5 ∧ 17 ≤ d ∧ d ≤ 57
      exact ⟨missing, hpunctured, hmissing, hCeq, hSeq, hcard,
        hw, hleafOrder, hLcap, hLcoset, hLgap, hfive,
        hseparated, hsecondary, hcriticalBound, hn, hBcard,
        hexternal, hdLower, hdUpper⟩
  · rcases hseparated with ⟨hcross, _hcap, _hcriticalBound⟩
    have hdisjoint : Disjoint L C := by
      rw [Finset.disjoint_left]
      intro b hbL hbC
      exact (hcross b hbL b hbC) (by simp)
    have hCle : C.card ≤ 6 :=
      exactMersenne_disjoint_leafRange_card_le_six
        g hg leaf hleaf C (by simpa only [L] using hdisjoint) hq
    have hCcard : C.card = Sfull.card + 1 := by
      have hrNotS : r ∉ Sfull := by
        intro hrS
        have hrB : r ∈ B := hSsub hrS
        rcases hmiddle with hk | hk
        · exact p.x_not_mem (by
            simpa only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
              using hrB)
        · have hkNe : k₀ ≠ -1 := by omega
          exact p.z_not_mem (by
            simpa only [r, primitiveMiddleInsertedCoordinate, hkNe,
              if_false] using hrB)
      simp only [C, Finset.card_insert_of_notMem hrNotS]
    omega

end MinModulus
