/-
# Quantitative charge of the complete Mersenne external fiber

The qualitative fiber trichotomy can be retained quantitatively.  In an
antipodal fiber every owner is common, cancelling, or residual, while the
cancelling set has cardinality at most one.  Splitting every common omission
into its retained-root and deleted-primary charges gives

  |E| <= |Root| + |Primary| + 1 + |Residual|.

For an adjacent parameter, every owner in the complete fiber carries a heavy
leaf competitor.  These are the two exact counting outputs needed by the next
global incidence comparison.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneCommonOmissionCharge

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Classically filtered owners satisfying a proposition.  Naming the
filter keeps quantitative theorem statements independent of synthesized
decidability instances. -/
noncomputable def ownersSatisfying
    {α : Type*} (E : Finset α) (P : α → Prop) : Finset α := by
  classical
  exact E.filter P

@[simp] theorem mem_ownersSatisfying_iff
    {α : Type*} [DecidableEq α] (E : Finset α) (P : α → Prop) (b : α) :
    b ∈ ownersSatisfying E P ↔ b ∈ E ∧ P b := by
  classical
  simp [ownersSatisfying]

/-- Quantitative version of owner-unique cancellation: a finite family
covered by common, cancelling, and residual predicates has size at most the
two charge counts plus one. -/
theorem card_le_common_add_one_add_residual_of_cancel_unique
    {α : Type*} [DecidableEq α]
    (E : Finset α) (Common Cancel Residual : α → Prop)
    (houtcome : ∀ b, b ∈ E → Common b ∨ Cancel b ∨ Residual b)
    (hcancelUnique : ∀ b₁, b₁ ∈ E → Cancel b₁ →
      ∀ b₂, b₂ ∈ E → Cancel b₂ → b₁ = b₂) :
    E.card ≤ (ownersSatisfying E Common).card + 1 +
      (ownersSatisfying E Residual).card := by
  classical
  let C := ownersSatisfying E Common
  let K := ownersSatisfying E Cancel
  let R := ownersSatisfying E Residual
  have hcover : E ⊆ (C ∪ K) ∪ R := by
    intro b hbE
    rcases houtcome b hbE with hbCommon | hbCancel | hbResidual
    · exact Finset.mem_union_left R
        (Finset.mem_union_left K
          ((mem_ownersSatisfying_iff E Common b).2 ⟨hbE, hbCommon⟩))
    · exact Finset.mem_union_left R
        (Finset.mem_union_right C
          ((mem_ownersSatisfying_iff E Cancel b).2 ⟨hbE, hbCancel⟩))
    · exact Finset.mem_union_right (C ∪ K)
        ((mem_ownersSatisfying_iff E Residual b).2 ⟨hbE, hbResidual⟩)
  have hK : K.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b₁ hb₁ b₂ hb₂
    have hb₁' := (mem_ownersSatisfying_iff E Cancel b₁).mp hb₁
    have hb₂' := (mem_ownersSatisfying_iff E Cancel b₂).mp hb₂
    exact hcancelUnique b₁ hb₁'.1 hb₁'.2 b₂ hb₂'.1 hb₂'.2
  have hcard : E.card ≤ C.card + K.card + R.card :=
    calc
      E.card ≤ ((C ∪ K) ∪ R).card := Finset.card_le_card hcover
      _ ≤ (C ∪ K).card + R.card := Finset.card_union_le (C ∪ K) R
      _ ≤ C.card + K.card + R.card := by
        have hCK := Finset.card_union_le C K
        omega
  simpa only [C, K, R] using (show
    E.card ≤ C.card + 1 + R.card by omega)

/-- If each owner satisfying `P` satisfies `Q` or `R`, its filtered count is
bounded by the sum of the two target filtered counts. -/
theorem card_filter_le_add_card_filter_of_imp_or
    {α : Type*} [DecidableEq α] (E : Finset α) (P Q R : α → Prop)
    (hroute : ∀ b, b ∈ E → P b → Q b ∨ R b) :
    (ownersSatisfying E P).card ≤
      (ownersSatisfying E Q).card + (ownersSatisfying E R).card := by
  classical
  have hsubset : ownersSatisfying E P ⊆
      ownersSatisfying E Q ∪ ownersSatisfying E R := by
    intro b hbP
    have hbP' := (mem_ownersSatisfying_iff E P b).mp hbP
    rcases hroute b hbP'.1 hbP'.2 with hbQ | hbR
    · exact Finset.mem_union_left _
        ((mem_ownersSatisfying_iff E Q b).2 ⟨hbP'.1, hbQ⟩)
    · exact Finset.mem_union_right _
        ((mem_ownersSatisfying_iff E R b).2 ⟨hbP'.1, hbR⟩)
  calc
    (ownersSatisfying E P).card ≤
        (ownersSatisfying E Q ∪ ownersSatisfying E R).card :=
      Finset.card_le_card hsubset
    _ ≤ (ownersSatisfying E Q).card + (ownersSatisfying E R).card :=
      Finset.card_union_le _ _

/-- Quantitative complete-fiber endpoint.  For an adjacent parameter every
owner is heavy.  For the unique antipodal parameter the fiber cardinality is
charged to retained-root omissions, deleted-primary omissions, one possible
cancellation, and full residual matrices. -/
theorem completeExternalFiber_allAdjacentHeavy_or_card_le_omissionCharges_add_one_add_residualMatrices
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
    (T : Finset (Fin n))
    (hTsub : T ⊆ B \ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hparameter : (k = k₀ + 1 ∨ k₀ = k + 1) ∨
      (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (hrows : ∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧ p.weight b = 2 * k) :
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    let E := deletedOwnerSubfiber B T
    (∀ b, b ∈ E → MersenneLeafAdjacentHeavyRow g y v B p leaf b) ∨
      E.card ≤
        (ownersSatisfying E (fun b ↦ AntipodalRepairRootCommonOmission
          g (p.scalar b • y) r)).card +
        (ownersSatisfying E (fun b ↦ AntipodalRepairPrimaryOmissionCharge
          g y B p f ⟨0, by omega⟩ r (p.scalar b • y))).card + 1 +
        (ownersSatisfying E (fun b ↦ AntipodalRepairResidualMatrix
          g y B p f ⟨0, by omega⟩ r v b)).card := by
  dsimp only
  have hoff : ∀ b : ↥B, b ∈ deletedOwnerSubfiber B T →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf := by
    intro b hbE
    exact (Finset.mem_sdiff.mp
      (hTsub ((mem_deletedOwnerSubfiber_iff B T b).mp hbE))).2
  rcases hparameter with hadjacent | hantipodal
  · left
    intro b hbE
    have hbT := (mem_deletedOwnerSubfiber_iff B T b).mp hbE
    exact p.exists_mersenneLeaf_heavy_competitor_of_adjacent
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic k₀ k hmiddle
        r hr hdeleted b (hoff b hbE) hadjacent
          (hrows b hbT).1 (hrows b hbT).2
  · right
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    let E := deletedOwnerSubfiber B T
    let Common : ↥B → Prop := fun b ↦ AntipodalRepairCommonOmission
      g (p.scalar b • y) ((Finset.univ : Finset (Fin d)).image leaf)
    let Cancel : ↥B → Prop := fun b ↦
      AntipodalRepairCancellation g y B p f
        (if k₀ = -1 then p.z else p.x) r b
    let Residual : ↥B → Prop := fun b ↦
      AntipodalRepairResidualMatrix
        g y B p f ⟨0, by omega⟩ r v b
    let Root : ↥B → Prop := fun b ↦ AntipodalRepairRootCommonOmission
      g (p.scalar b • y) r
    let Primary : ↥B → Prop := fun b ↦
      AntipodalRepairPrimaryOmissionCharge
        g y B p f ⟨0, by omega⟩ r (p.scalar b • y)
    have houtcome : ∀ b, b ∈ E → Common b ∨ Cancel b ∨ Residual b := by
      intro b hbE
      exact p.antipodal_mersenneLeaf_row_trichotomy
        g hg y root v B hyq hfullOdd hprimitive hd hv leaf hleaf e
          hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hprimaryWeight
            b (hoff b (by simpa only [E] using hbE)) hr hantipodal
              (hrows b ((mem_deletedOwnerSubfiber_iff B T b).mp
                (by simpa only [E] using hbE))).1
              (hrows b ((mem_deletedOwnerSubfiber_iff B T b).mp
                (by simpa only [E] using hbE))).2
    have hcancelUnique : ∀ b₁, b₁ ∈ E → Cancel b₁ →
        ∀ b₂, b₂ ∈ E → Cancel b₂ → b₁ = b₂ := by
      intro b₁ hb₁E hb₁Cancel b₂ hb₂E hb₂Cancel
      exact antipodalRepairCancellation_owner_injective
        g hg y B p f (if k₀ = -1 then p.z else p.x) r b₁ b₂
          (by
            simpa only [f, image_univ_comp_equiv leaf e] using
              hoff b₁ (by simpa only [E] using hb₁E))
          (by
            simpa only [f, image_univ_comp_equiv leaf e] using
              hoff b₂ (by simpa only [E] using hb₂E))
          hb₁Cancel hb₂Cancel
    have hbase := card_le_common_add_one_add_residual_of_cancel_unique
      E Common Cancel Residual houtcome hcancelUnique
    have hcommonRoute : ∀ b, b ∈ E → Common b → Root b ∨ Primary b := by
      intro b _hbE hbCommon
      exact p.antipodal_mersenneLeaf_commonOmission_root_or_primaryCharge
        g y B hyq hfullOdd hprimitive hd leaf e r hrzero hdeleted hleafMem
          k₀ hmiddle hprimaryWeight hr (p.scalar b • y) hbCommon
    have hcommonCount := card_filter_le_add_card_filter_of_imp_or
      E Common Root Primary hcommonRoute
    simpa only [E, Common, Residual, Root, Primary, f] using
      (show E.card ≤
          (ownersSatisfying E Root).card +
            (ownersSatisfying E Primary).card + 1 +
            (ownersSatisfying E Residual).card by omega)

/-- The secondary fiber stored by the exact five-external-row package has the
quantitative charge above, with its size-at-least-three and original external
coordinate containment retained. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.secondaryFiber_quantitativeCharge
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
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows g y B L p k₀) :
    ∃ T : Finset (Fin n),
      3 ≤ T.card ∧ T ⊆ B \ L ∧
      (let f : Fin d → Fin n := fun i ↦ leaf (e i)
       let E := deletedOwnerSubfiber B T
       (∀ b, b ∈ E → MersenneLeafAdjacentHeavyRow g y v B p leaf b) ∨
         E.card ≤
           (ownersSatisfying E (fun b ↦ AntipodalRepairRootCommonOmission
             g (p.scalar b • y) r)).card +
           (ownersSatisfying E (fun b ↦ AntipodalRepairPrimaryOmissionCharge
             g y B p f ⟨0, by omega⟩ r (p.scalar b • y))).card + 1 +
           (ownersSatisfying E (fun b ↦ AntipodalRepairResidualMatrix
             g y B p f ⟨0, by omega⟩ r v b)).card) := by
  rcases hfive with
    ⟨T, k, _t, _F, hTcard, _hTle, _hFle, hTsub, _htT,
      _hkMem, _hkNe, hparameter, hrows, _hTexact, _hTadjacent,
      _hTcomplete, _hTseparated, _hpartition, _hdisjoint,
      _hcard, _hprofiles, _hFcase, _hcap, _hcritical⟩
  refine ⟨T, hTcard, hTsub, ?_⟩
  exact completeExternalFiber_allAdjacentHeavy_or_card_le_omissionCharges_add_one_add_residualMatrices
    g hg y root v B p hyq hfullOdd hprimitive hd hv leaf hleaf e
      hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hmiddle
        hprimaryWeight T (by simpa only [hL] using hTsub) hr hparameter
          (fun b hbT ↦ ⟨(hrows b hbT).1, (hrows b hbT).2.1⟩)

end MinModulus
