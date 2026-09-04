/-
# Rejoining the complete external fiber to the repair trichotomy

The exact-Mersenne five-external-row endpoint contains a complete secondary
fiber `T` of cardinality at least three.  Its parameter is either adjacent to
the primary parameter, in which case every owner has a genuine heavy leaf
competitor, or it is the unique antipodal parameter.  In the latter case the
repair fiber trichotomy gives a common omission or two full residual matrices.
This module performs that concrete rejoin on the original presentation.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairFiberTrichotomy

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Coordinates in `T` viewed as deleted owners in the subtype `↥B`. -/
noncomputable def deletedOwnerSubfiber
    {n : ℕ} (B T : Finset (Fin n)) : Finset ↥B :=
  Finset.univ.filter (fun b : ↥B ↦ (b : Fin n) ∈ T)

@[simp] theorem mem_deletedOwnerSubfiber_iff
    {n : ℕ} (B T : Finset (Fin n)) (b : ↥B) :
    b ∈ deletedOwnerSubfiber B T ↔ (b : Fin n) ∈ T := by
  classical
  simp [deletedOwnerSubfiber]

/-- Lifting a coordinate finset contained in `B` to the owner subtype does
not change its cardinality. -/
theorem card_deletedOwnerSubfiber
    {n : ℕ} (B T : Finset (Fin n)) (hT : T ⊆ B) :
    (deletedOwnerSubfiber B T).card = T.card := by
  classical
  let valEmb : ↥B ↪ Fin n := Function.Embedding.subtype _
  have hmap : (deletedOwnerSubfiber B T).map valEmb = T := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, hb, hbi⟩ := Finset.mem_map.mp hi
      have hbT := (mem_deletedOwnerSubfiber_iff B T b).mp hb
      simpa only [valEmb, Function.Embedding.coe_subtype] using hbi ▸ hbT
    · intro hiT
      let b : ↥B := ⟨i, hT hiT⟩
      apply Finset.mem_map.mpr
      refine ⟨b, ?_, rfl⟩
      exact (mem_deletedOwnerSubfiber_iff B T b).2 hiT
  calc
    (deletedOwnerSubfiber B T).card =
        ((deletedOwnerSubfiber B T).map valEmb).card := by
          rw [Finset.card_map]
    _ = T.card := congrArg Finset.card hmap

/-- Exact heavy-row payload supplied by an adjacent external parameter. -/
def MersenneLeafAdjacentHeavyRow
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (b : ↥B) : Prop :=
  ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧ p.scalar b • y = s • v ∧
    ∃ c : Fin n → ℤ, Witness g (p.scalar b • y) c ∧
      (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
      ∃ i : Fin n,
        i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧ 2 ≤ c i

/-- Concrete complete-fiber split.  A secondary fiber of size at least three
with one fixed external parameter produces an adjacent heavy row, a common
omission, or two distinct complete residual matrices. -/
theorem completeExternalFiber_adjacentHeavy_or_common_or_twoResidualMatrices
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ k : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (T : Finset (Fin n)) (hTcard : 3 ≤ T.card)
    (hTsub : T ⊆ B \ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hparameter : (k = k₀ + 1 ∨ k₀ = k + 1) ∨
      (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (hrows : ∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧ p.weight b = 2 * k) :
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    let E := deletedOwnerSubfiber B T
    (∃ b, b ∈ E ∧ MersenneLeafAdjacentHeavyRow g y v B p leaf b) ∨
      (∃ b, b ∈ E ∧ AntipodalRepairCommonOmission
        g (p.scalar b • y) ((Finset.univ : Finset (Fin d)).image leaf)) ∨
      ∃ b₁, b₁ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₁ ∧
        ∃ b₂, b₂ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₂ ∧ b₁ ≠ b₂ := by
  dsimp only
  have hTsubB : T ⊆ B := fun i hi ↦ (Finset.mem_sdiff.mp (hTsub hi)).1
  have hEcard : 3 ≤ (deletedOwnerSubfiber B T).card := by
    rw [card_deletedOwnerSubfiber B T hTsubB]
    exact hTcard
  have hoff : ∀ b : ↥B, b ∈ deletedOwnerSubfiber B T →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf := by
    intro b hbE
    exact (Finset.mem_sdiff.mp
      (hTsub ((mem_deletedOwnerSubfiber_iff B T b).mp hbE))).2
  rcases hparameter with hadjacent | hantipodal
  · left
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t, htT⟩ := hTne
    let b : ↥B := ⟨t, hTsubB htT⟩
    refine ⟨b, (mem_deletedOwnerSubfiber_iff B T b).2 htT, ?_⟩
    exact p.exists_mersenneLeaf_heavy_competitor_of_adjacent
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic k₀ k hmiddle
        r hr hdeleted b (hoff b ((mem_deletedOwnerSubfiber_iff B T b).2 htT))
          hadjacent (hrows b htT).1 (hrows b htT).2
  · right
    exact p.antipodal_mersenneLeaf_fiber_trichotomy
      g hg y root v B hyq hfullOdd hprimitive hd hv leaf hleaf e
        hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hprimaryWeight
          (deletedOwnerSubfiber B T) hEcard hoff hr hantipodal
            (fun b hbE ↦ (hrows b
              ((mem_deletedOwnerSubfiber_iff B T b).mp hbE)).1)
            (fun b hbE ↦ (hrows b
              ((mem_deletedOwnerSubfiber_iff B T b).mp hbE)).2)

/-- The secondary complete fiber stored by the five-external-row package
therefore satisfies the concrete adjacent-heavy/common-omission/two-matrix
trichotomy on the same private presentation. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.secondaryFiber_trichotomy
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (L : Finset (Fin n))
    (hL : L = (Finset.univ : Finset (Fin d)).image leaf)
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows
      g y B L p k₀) :
    ∃ T : Finset (Fin n), ∃ k : ℤ,
      3 ≤ T.card ∧ T ⊆ B \ L ∧
      ((k = k₀ + 1 ∨ k₀ = k + 1) ∨
        (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2)) ∧
      (let f : Fin d → Fin n := fun i ↦ leaf (e i)
       let E := deletedOwnerSubfiber B T
       (∃ b, b ∈ E ∧ MersenneLeafAdjacentHeavyRow g y v B p leaf b) ∨
         (∃ b, b ∈ E ∧ AntipodalRepairCommonOmission
           g (p.scalar b • y)
             ((Finset.univ : Finset (Fin d)).image leaf)) ∨
         ∃ b₁, b₁ ∈ E ∧
             AntipodalRepairResidualMatrix
               g y B p f ⟨0, by omega⟩ r v b₁ ∧
           ∃ b₂, b₂ ∈ E ∧
             AntipodalRepairResidualMatrix
               g y B p f ⟨0, by omega⟩ r v b₂ ∧ b₁ ≠ b₂) := by
  rcases hfive with
    ⟨T, k, _t, _F, hTcard, _hTle, _hFle, hTsub, _htT,
      _hkMem, _hkNe, hparameter, hrows, _hTexact, _hTadjacent,
      _hTcomplete, _hTseparated, _hpartition, _hdisjoint,
      _hcard, _hprofiles, _hFcase, _hcap, _hcritical⟩
  refine ⟨T, k, hTcard, hTsub, hparameter, ?_⟩
  exact completeExternalFiber_adjacentHeavy_or_common_or_twoResidualMatrices
    g hg y root v B p hyq hfullOdd hprimitive hd hv leaf hleaf e
      hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hmiddle
        hprimaryWeight T hTcard (by simpa only [hL] using hTsub) hr
          hparameter (fun b hbT ↦ ⟨(hrows b hbT).1, (hrows b hbT).2.1⟩)

end MinModulus
