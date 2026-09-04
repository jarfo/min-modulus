/-
# Fiber trichotomy for antipodal repair residuals

The rowwise antipodal endpoint has three outcomes: a common omission, exact
repair cancellation, or a complete leaf residual.  Exact cancellation is
owner-injective in a fixed off-leaf pure-edge fiber.  Consequently, among
three owners, absence of a common omission forces two distinct residual
owners.  This module records the finite combinatorial principle and its
specialization to the canonical antipodal repair predicates.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairCancellationFiber

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- If every element of a set of size at least three is common, cancelling,
or residual, and at most one element can cancel, then either a common element
exists or two distinct residual elements exist. -/
theorem common_or_two_residual_of_three_le_of_cancel_unique
    {α : Type*} [DecidableEq α]
    (E : Finset α) (hE : 3 ≤ E.card)
    (Common Cancel Residual : α → Prop)
    (houtcome : ∀ b, b ∈ E → Common b ∨ Cancel b ∨ Residual b)
    (hcancelUnique : ∀ b₁, b₁ ∈ E → Cancel b₁ →
      ∀ b₂, b₂ ∈ E → Cancel b₂ → b₁ = b₂) :
    (∃ b, b ∈ E ∧ Common b) ∨
      ∃ b₁, b₁ ∈ E ∧ Residual b₁ ∧
        ∃ b₂, b₂ ∈ E ∧ Residual b₂ ∧ b₁ ≠ b₂ := by
  classical
  by_cases hcommon : ∃ b, b ∈ E ∧ Common b
  · exact Or.inl hcommon
  · right
    let C := E.filter Cancel
    let R := E.filter Residual
    have hcover : E ⊆ C ∪ R := by
      intro b hbE
      rcases houtcome b hbE with hbCommon | hbCancel | hbResidual
      · exact False.elim (hcommon ⟨b, hbE, hbCommon⟩)
      · exact Finset.mem_union_left R (Finset.mem_filter.mpr ⟨hbE, hbCancel⟩)
      · exact Finset.mem_union_right C (Finset.mem_filter.mpr ⟨hbE, hbResidual⟩)
    have hC : C.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro b₁ hb₁ b₂ hb₂
      have hb₁' := Finset.mem_filter.mp hb₁
      have hb₂' := Finset.mem_filter.mp hb₂
      exact hcancelUnique b₁ hb₁'.1 hb₁'.2 b₂ hb₂'.1 hb₂'.2
    have hcard : E.card ≤ C.card + R.card :=
      calc
        E.card ≤ (C ∪ R).card := Finset.card_le_card hcover
        _ ≤ C.card + R.card := Finset.card_union_le C R
    have hR : 1 < R.card := by omega
    obtain ⟨b₁, hb₁R, b₂, hb₂R, hb₁b₂⟩ := Finset.one_lt_card.mp hR
    have hb₁ := Finset.mem_filter.mp hb₁R
    have hb₂ := Finset.mem_filter.mp hb₂R
    exact ⟨b₁, hb₁.1, hb₁.2, b₂, hb₂.1, hb₂.2, hb₁b₂⟩

/-- Fiber-level specialization of the preceding principle.  The cancellation
predicate is the exact canonical antipodal repair cancellation, whose
owner-injectivity follows from validity and the off-leaf condition. -/
theorem antipodalRepairFiber_common_or_two_residual
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f)
    (hE : 3 ≤ E.card)
    (Common Residual : ↥B → Prop)
    (houtcome : ∀ b, b ∈ E → Common b ∨
      AntipodalRepairCancellation g y B p f center r b ∨ Residual b) :
    (∃ b, b ∈ E ∧ Common b) ∨
      ∃ b₁, b₁ ∈ E ∧ Residual b₁ ∧
        ∃ b₂, b₂ ∈ E ∧ Residual b₂ ∧ b₁ ≠ b₂ := by
  apply common_or_two_residual_of_three_le_of_cancel_unique
    E hE Common
      (AntipodalRepairCancellation g y B p f center r) Residual houtcome
  intro b₁ hb₁E hb₁Cancel b₂ hb₂E hb₂Cancel
  exact antipodalRepairCancellation_owner_injective
    g hg y B p f center r b₁ b₂
      (hoff b₁ hb₁E) (hoff b₂ hb₂E) hb₁Cancel hb₂Cancel

/-- Four rowwise alternatives compress to the closure-oriented fiber
trichotomy: one adjacent-heavy row, one common-omission row, or two distinct
residual rows.  Exact cancellation disappears because it is owner-unique. -/
theorem antipodalRepairFiber_adjacent_or_common_or_two_residual
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f)
    (hE : 3 ≤ E.card)
    (Adjacent Common Residual : ↥B → Prop)
    (houtcome : ∀ b, b ∈ E → Adjacent b ∨ Common b ∨
      AntipodalRepairCancellation g y B p f center r b ∨ Residual b) :
    (∃ b, b ∈ E ∧ Adjacent b) ∨
      (∃ b, b ∈ E ∧ Common b) ∨
        ∃ b₁, b₁ ∈ E ∧ Residual b₁ ∧
          ∃ b₂, b₂ ∈ E ∧ Residual b₂ ∧ b₁ ≠ b₂ := by
  classical
  by_cases hadjacent : ∃ b, b ∈ E ∧ Adjacent b
  · exact Or.inl hadjacent
  · right
    apply antipodalRepairFiber_common_or_two_residual
      g hg y B p f center r E hoff hE Common Residual
    intro b hbE
    rcases houtcome b hbE with hbAdjacent | hbCommon | hbCancel | hbResidual
    · exact False.elim (hadjacent ⟨b, hbE, hbAdjacent⟩)
    · exact Or.inl hbCommon
    · exact Or.inr (Or.inl hbCancel)
    · exact Or.inr (Or.inr hbResidual)

/-- Two opposite-target leaf witnesses share an omitted leaf. -/
def AntipodalRepairCommonOmission
    {n : ℕ} (g : Fin n → G) (target : G) (L : Finset (Fin n)) : Prop :=
  ∃ cPlus cMinus : Fin n → ℤ, ∃ j : Fin n,
    Witness g target cPlus ∧ Witness g (-target) cMinus ∧
      j ∈ L ∧ cPlus j = -1 ∧ cMinus j = -1

/-- Complete residual-incidence matrix carried by one antipodal external row.
Besides the original binary subsets and exact nonzero residual witnesses, the
package retains every row support and degree, both signed column degrees, and
the total incidence mass. -/
noncomputable def AntipodalRepairResidualMatrix
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G)
    (b : ↥B) : Prop :=
  ∃ s : ℕ, ∃ A M : Finset (Fin d),
    0 < s ∧ s < 2 ^ d - 1 ∧ p.scalar b • y = s • v ∧
      Disjoint A M ∧ A.card = M.card ∧ z ∈ A ∧
      (binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) = binarySubsetValue M + s) ∧
      (∀ m, m ∈ M →
        let residual := normalizedPrivateRepairResidual
          g y B p f z A M m
        Witness g (-((a m.val + s) • v)) residual ∧
          -((a m.val + s) • v) ≠ 0 ∧ residual r = 0 ∧
          residual (f m) = 0 ∧
          ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image f →
            residual j = 0) ∧
      (∀ m, m ∈ M →
        normalizedPrivateRepairResidualLeafSupport
          g y B p f z A M m = (A.erase z) ∪ (M.erase m)) ∧
      (∀ m, m ∈ M →
        (normalizedPrivateRepairResidualLeafSupport
          g y B p f z A M m).card = 2 * (M.card - 1)) ∧
      (∀ i, i ∈ A → i ≠ z →
        (M.filter (fun m ↦ normalizedPrivateRepairResidual
          g y B p f z A M m (f i) = -1)).card = M.card) ∧
      (∀ i, i ∈ M →
        (M.filter (fun m ↦ normalizedPrivateRepairResidual
          g y B p f z A M m (f i) = 1)).card = M.card - 1) ∧
      (∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m).card) = M.card * (2 * (M.card - 1))

/-- The full rowwise antipodal endpoint, compressed into exactly the three
predicates needed by fiber counting.  In the third arm no incidence data is
discarded. -/
theorem TwoRetainedCanonicalPrivatePresentation.antipodal_mersenneLeaf_row_trichotomy
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
    (k₀ k : ℤ)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    AntipodalRepairCommonOmission g (p.scalar b • y)
        ((Finset.univ : Finset (Fin d)).image leaf) ∨
      AntipodalRepairCancellation g y B p f center r b ∨
      AntipodalRepairResidualMatrix g y B p f ⟨0, by omega⟩ r v b := by
  dsimp only
  obtain ⟨_hownerNeg, hshape, s, hs0, hsq, htarget,
      cPlus, cMinus, qrel, _i, hcPlus, _hplusOff, hcMinus,
      _hminusOff, _hminusR, _hiLeaf, _hiLocalized, _hiGap, _hqrel,
      _hdefect, _hqcenter, _hqb, houtcome⟩ :=
    p.exists_antipodal_mersenneLeaf_repairResidual_dichotomy
      g hg y root v B hyq hfullOdd hprimitive hd hv leaf hleaf e
        hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hprimaryWeight
          b hb hr hantipodal howner hweight
  rcases houtcome with hcommon |
      ⟨A, M, _hneg, hdisjoint, hcard, hzero, _hcPrivate,
        _hqPrivate, harithmetic, hrepairs⟩
  · left
    obtain ⟨j, hjLeaf, hjPlus, hjMinus⟩ := hcommon
    exact ⟨cPlus, cMinus, j, hcPlus, hcMinus,
      hjLeaf, hjPlus, hjMinus⟩
  · have hmiddle : k₀ = -1 ∨ k₀ = 0 := by
      rcases hantipodal with ⟨hk₀, _⟩ | ⟨hk₀, _⟩
      · exact Or.inl hk₀
      · exact Or.inr hk₀
    have hrPrimitive : r = primitiveMiddleInsertedCoordinate p k₀ := by
      simpa only [primitiveMiddleInsertedCoordinate] using hr
    have hf : Function.Injective (fun j ↦ leaf (e j)) :=
      hleaf.comp e.injective
    have hrows : ∀ j, j ≠ ⟨0, by omega⟩ →
        normalizedCanonicalPrivateRow g y B p (leaf (e j)) =
          signedPairCoeffs (leaf (e j)) r := by
      intro j hjzero
      have hjB : leaf (e j) ∈ B := (hleafMem j).2 hjzero
      rw [normalizedCanonicalPrivateRow_of_mem
        g y B p (leaf (e j)) hjB, hrPrimitive]
      exact p.primitive_primaryMiddle_owner_mul_coeff_eq_signedPair
        g y B hyq hfullOdd hprimitive ⟨leaf (e j), hjB⟩ k₀ hmiddle
          (hprimaryWeight j hjB)
    have hpoint : ∀ m, m ∈ M →
        (((qrel - normalizedCanonicalPrivateRow
              g y B p (leaf (e m)) = p.coeff b) ∧
            A = {⟨0, by omega⟩} ∧ M = {m}) ∨
          (let residual := normalizedPrivateRepairResidual
              g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M m;
            Witness g (-((a m.val + s) • v)) residual ∧
              -((a m.val + s) • v) ≠ 0 ∧ residual r = 0 ∧
              residual (leaf (e m)) = 0 ∧
              ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image
                  (fun i ↦ leaf (e i)) → residual j = 0)) := by
      intro m hmM
      have hm := hrepairs m hmM
      dsimp only at hm
      rcases hm with ⟨_hrepair, _hrepairRoot, _hrepairOwner,
          hcancel | hresidual⟩
      · exact Or.inl hcancel
      · right
        obtain ⟨hWitness, _htargetEq, htargetNe, hrootZero,
          hownerZero, hoff⟩ := hresidual
        exact ⟨hWitness, htargetNe, hrootZero, hownerZero, hoff⟩
    have hfamily := singletonCancellation_or_all_residual
      (d := d) (by omega) s hs0 A M harithmetic
      (fun m ↦ qrel - normalizedCanonicalPrivateRow
          g y B p (leaf (e m)) = p.coeff b)
      (fun m ↦
        let residual := normalizedPrivateRepairResidual
          g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M m;
        Witness g (-((a m.val + s) • v)) residual ∧
          -((a m.val + s) • v) ≠ 0 ∧ residual r = 0 ∧
          residual (leaf (e m)) = 0 ∧
          ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image
              (fun i ↦ leaf (e i)) → residual j = 0)
      hpoint
    rcases hfamily with
        ⟨m, hmM, hcancel, _hA, _hM, _hpow, _hscalar⟩ | hall
    · right
      left
      have hm := hrepairs m hmM
      dsimp only at hm
      exact ⟨hshape, m,
        qrel - normalizedCanonicalPrivateRow g y B p (leaf (e m)),
        hm.1, hcancel⟩
    · right
      right
      refine ⟨s, A, M, hs0, hsq, htarget, hdisjoint, hcard, hzero,
        harithmetic, hall, ?_, ?_, ?_, ?_, ?_⟩
      · intro m hmM
        exact normalizedPrivateRepairResidualLeafSupport_eq
          g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
            A M hdisjoint hcard hzero hrows m hmM
      · intro m hmM
        exact card_normalizedPrivateRepairResidualLeafSupport
          g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
            A M hdisjoint hcard hzero hrows m hmM
      · intro i hiA hiz
        exact normalizedPrivateRepairResidual_negativeIncidence_complete
          g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
            A M hdisjoint hcard hzero hrows i hiA hiz
      · intro i hiM
        exact card_normalizedPrivateRepairResidual_positiveIncidence
          g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
            A M hdisjoint hcard hzero hrows i hiM
      · exact sum_card_normalizedPrivateRepairResidualLeafSupport
          g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
            A M hdisjoint hcard hzero hrows

/-- Complete antipodal fiber endpoint.  In a fiber of at least three
off-leaf owners with the same antipodal parameter, the rowwise endpoint and
owner-injectivity of exact cancellation force either one common-omission row
or two distinct rows carrying the complete residual-incidence matrix. -/
theorem TwoRetainedCanonicalPrivatePresentation.antipodal_mersenneLeaf_fiber_trichotomy
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
    (k₀ k : ℤ)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (E : Finset ↥B) (hE : 3 ≤ E.card)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : ∀ b : ↥B, b ∈ E →
      p.coeff b (b : Fin n) = -1 ∨ p.coeff b (b : Fin n) = 1)
    (hweight : ∀ b : ↥B, b ∈ E → p.weight b = 2 * k) :
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    (∃ b, b ∈ E ∧ AntipodalRepairCommonOmission
        g (p.scalar b • y) ((Finset.univ : Finset (Fin d)).image leaf)) ∨
      ∃ b₁, b₁ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₁ ∧
        ∃ b₂, b₂ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₂ ∧ b₁ ≠ b₂ := by
  dsimp only
  have hleafImage :
      (Finset.univ : Finset (Fin d)).image (fun i ↦ leaf (e i)) =
        (Finset.univ : Finset (Fin d)).image leaf := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr ⟨e i, Finset.mem_univ _, hij⟩
    · intro hj
      obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
      refine Finset.mem_image.mpr ⟨e.symm i, Finset.mem_univ _, ?_⟩
      simpa using hij
  apply antipodalRepairFiber_common_or_two_residual
    g hg y B p (fun i ↦ leaf (e i))
      (if k₀ = -1 then p.z else p.x) r E
  · intro b hbE
    simpa only [hleafImage] using hoff b hbE
  · exact hE
  · intro b hbE
    exact p.antipodal_mersenneLeaf_row_trichotomy
      g hg y root v B hyq hfullOdd hprimitive hd hv leaf hleaf e
        hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hprimaryWeight
          b (hoff b hbE) hr hantipodal (howner b hbE) (hweight b hbE)

end MinModulus
