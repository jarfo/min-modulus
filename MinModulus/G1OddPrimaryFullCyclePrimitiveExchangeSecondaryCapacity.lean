/-
# Product capacity of the primary and secondary residue cosets

The equal-coset critical branch now has two complete and separated coordinate
families: the primary union and the saturated secondary deleted-owner fiber.
Fixed-cardinality subset layers from both families inject jointly into the
odd kernel.  Thus every product of their binomial layers is bounded by the
odd factor.

Combining that capacity with the exact sixth-stratum inequality
`16*q < 2^|B|` gives a uniform critical product bound.  Since the secondary
fiber has at least three owners, its level-one layer contributes a factor
three and leaves the explicit central residual

    48 * choose(|U|, floor(|U|/2)) < 2^|B|.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeSecondarySaturation

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The complete secondary residue fiber together with every fixed-layer
product capacity against the primary coset. -/
def PrimitiveSaturatedSecondaryResidueCapacity
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Prop :=
  ∃ T : Finset (Fin n), ∃ k₁ : ℤ, ∃ t : Fin n,
    3 ≤ T.card ∧ T ⊆ B \ U ∧ t ∈ T ∧
    k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧ k₁ ≠ k₀ ∧
    (∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧
      p.weight b = 2 * k₁ ∧
      g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z) =
        -(k₁ •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z))) ∧
    (∀ b : ↥B,
      ((b : Fin n) ∈ T ↔
        g (b : Fin n) - g t ∈ AddSubgroup.zmultiples y)) ∧
    (∀ b ∈ T, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y) ∧
    ∀ i j : ℕ, U.card.choose i * T.card.choose j ≤ q

/-- Forget only the fixed-layer capacity inequalities. -/
theorem PrimitiveSaturatedSecondaryResidueCapacity.toSaturatedFiber
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hcapacity : PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀) :
    PrimitiveSaturatedSecondaryResidueFiber g y B U p k₀ := by
  rcases hcapacity with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hrows,
      hcomplete, hseparated, _hcap⟩
  exact ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hrows,
    hcomplete, hseparated⟩

/-- Two complete separated residue cosets supply all products of their
fixed-cardinality binomial layers inside the odd kernel. -/
theorem PrimitiveSaturatedSecondaryResidueFiber.toCapacity
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hU : U.Nonempty)
    (hUcoset : ∀ b ∈ U, ∀ c ∈ U,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hsecondary : PrimitiveSaturatedSecondaryResidueFiber g y B U p k₀) :
    PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ := by
  classical
  rcases hsecondary with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hrows,
      hcomplete, hseparated⟩
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hdisjoint : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro b hbU hbT
    exact (Finset.mem_sdiff.mp (hTsub hbT)).2 hbU
  have hTcoset : ∀ b ∈ T, ∀ c ∈ T,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbT c hcT
    have hbB := (Finset.mem_sdiff.mp (hTsub hbT)).1
    have hcB := (Finset.mem_sdiff.mp (hTsub hcT)).1
    have hbParallel := (hcomplete ⟨b, hbB⟩).1 hbT
    have hcParallel := (hcomplete ⟨c, hcB⟩).1 hcT
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
    convert hsub using 1
    module
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  have hcap : ∀ i j : ℕ,
      U.card.choose i * T.card.choose j ≤ q := by
    intro i j
    have h := choose_mul_choose_le_addOrderOf_of_disjoint_kernelCosets
      g hg y U T hU hT hdisjoint hUcoset hTcoset i j
    simpa only [horder] using h
  exact ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hrows,
    hcomplete, hseparated, hcap⟩

/-- Exact critical comparison for arbitrary layers of the primary and
secondary residue cosets. -/
theorem sixteen_mul_primarySecondary_choose_lt_two_pow_transversalCard
    {q : ℕ} (B U T : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hcap : ∀ i j : ℕ, U.card.choose i * T.card.choose j ≤ q)
    (i j : ℕ) :
    16 * (U.card.choose i * T.card.choose j) < 2 ^ B.card := by
  calc
    16 * (U.card.choose i * T.card.choose j) ≤ 16 * q :=
      Nat.mul_le_mul_left 16 (hcap i j)
    _ < 2 ^ B.card :=
      sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
        B hretained hcritical

/-- The level-one layer of a three-owner secondary fiber strengthens the
primary central-binomial residual by a factor three. -/
theorem fortyEight_mul_primaryCentralChoose_lt_two_pow_transversalCard
    {q : ℕ} (B U T : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hTcard : 3 ≤ T.card)
    (hcap : ∀ i j : ℕ, U.card.choose i * T.card.choose j ≤ q) :
    48 * U.card.choose (U.card / 2) < 2 ^ B.card := by
  have hchoose : 3 ≤ T.card.choose 1 := by
    simpa using hTcard
  have hproduct : 3 * U.card.choose (U.card / 2) ≤ q := by
    calc
      3 * U.card.choose (U.card / 2) ≤
          T.card.choose 1 * U.card.choose (U.card / 2) :=
        Nat.mul_le_mul_right _ hchoose
      _ = U.card.choose (U.card / 2) * T.card.choose 1 := by ac_rfl
      _ ≤ q := hcap (U.card / 2) 1
  calc
    48 * U.card.choose (U.card / 2) =
        16 * (3 * U.card.choose (U.card / 2)) := by ring
    _ ≤ 16 * q := Nat.mul_le_mul_left 16 hproduct
    _ < 2 ^ B.card :=
      sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
        B hretained hcritical

/-- Lossless composition of the five-owner iteration: extract a secondary
residue triple, saturate it on the same canonical presentation, and install
all product-layer bounds against the primary coset. -/
theorem exists_primitiveSaturatedSecondaryResidueCapacity_of_five_separated
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hwindow :
      (∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2)
    (hU : U.Nonempty)
    (hUcoset : ∀ b ∈ U, ∀ c ∈ U,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hrU : primitiveMiddleInsertedCoordinate p k₀ ∈ U)
    (hfive : 5 ≤ (B \ U).card)
    (hseparated : ∀ b ∈ B \ U, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y) :
    PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ := by
  have hsecondary :=
    exists_primitiveSecondaryResidueFiber_of_five_separated
      g y B U p k₀ hprimitive hyq hfullOdd hmiddle hwindow
        hrU hfive hseparated
  have hsaturated := hsecondary.toSaturated
    g y B U p k₀ hprimitive hyq hfullOdd hseparated
  exact hsaturated.toCapacity
    g hg y hyq hfullOdd B U p k₀ hU hUcoset

/-- The composed capacity package exposes the factor-three central critical
residual without discarding its complete secondary fiber data. -/
theorem PrimitiveSaturatedSecondaryResidueCapacity.exists_centralCriticalBound
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hcapacity : PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀) :
    ∃ T : Finset (Fin n),
      3 ≤ T.card ∧
        48 * U.card.choose (U.card / 2) < 2 ^ B.card := by
  rcases hcapacity with
    ⟨T, _k₁, _t, hTcard, _hTsub, _htT, _hk₁Mem, _hk₁Ne,
      _hrows, _hcomplete, _hseparated, hcap⟩
  exact ⟨T, hTcard,
    fortyEight_mul_primaryCentralChoose_lt_two_pow_transversalCard
      B U T hretained hcritical hTcard hcap⟩

end MinModulus
