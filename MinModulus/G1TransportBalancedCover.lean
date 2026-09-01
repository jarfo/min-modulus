import MinModulus.G1TransportFaceCoverage

namespace MinModulus

open Finset

/-- Equality in the finite union bound forces the indexed family to be
pairwise disjoint. -/
theorem pairwiseDisjoint_of_card_biUnion_eq_sum_card
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (B : ι → Finset α)
    (hcard : (I.biUnion B).card = I.sum (fun i ↦ (B i).card)) :
    (I : Set ι).PairwiseDisjoint B := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha] at hcard
      have hUnionLe : (B a ∪ I.biUnion B).card ≤
          (B a).card + (I.biUnion B).card := Finset.card_union_le _ _
      have hRestLe : (I.biUnion B).card ≤
          I.sum (fun i ↦ (B i).card) := Finset.card_biUnion_le
      have hRestEq : (I.biUnion B).card =
          I.sum (fun i ↦ (B i).card) := by omega
      have hHeadEq : (B a ∪ I.biUnion B).card =
          (B a).card + (I.biUnion B).card := by omega
      have hHeadDisj : Disjoint (B a) (I.biUnion B) :=
        Finset.card_union_eq_card_add_card.mp hHeadEq
      have hRestPair := ih hRestEq
      intro i hi j hj hij
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hi hj
      rcases hi with rfl | hi
      · rcases hj with rfl | hj
        · exact False.elim (hij rfl)
        · exact hHeadDisj.mono_right
            (Finset.subset_biUnion_of_mem B hj)
      · rcases hj with rfl | hj
        · exact hHeadDisj.symm.mono_left
            (Finset.subset_biUnion_of_mem B hi)
        · exact hRestPair hi hj hij

/-- A set covered by a pairwise-disjoint indexed family splits exactly into
its intersections with that family. -/
theorem card_eq_sum_card_inter_of_subset_biUnion_of_pairwiseDisjoint
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hpair : (I : Set ι).PairwiseDisjoint B)
    (hcover : A ⊆ I.biUnion B) :
    A.card = I.sum (fun i ↦ (A ∩ B i).card) := by
  have hinterPair : (I : Set ι).PairwiseDisjoint
      (fun i ↦ A ∩ B i) := by
    intro i hi j hj hij
    exact (hpair hi hj hij).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hunion : I.biUnion (fun i ↦ A ∩ B i) = A := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
      exact Finset.mem_inter.mp hxi |>.1
    · intro x hxA
      rcases Finset.mem_biUnion.mp (hcover hxA) with ⟨i, hi, hxi⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_inter.mpr ⟨hxA, hxi⟩⟩
  calc
    A.card = (I.biUnion (fun i ↦ A ∩ B i)).card :=
      congrArg Finset.card hunion.symm
    _ = I.sum (fun i ↦ (A ∩ B i).card) :=
      Finset.card_biUnion hinterPair

/-- Balanced finite-cover rigidity.  Pairwise-disjoint target pieces and a
source family with the same piecewise cardinalities cannot cover with slack:
the unions coincide and the source pieces must also be pairwise disjoint. -/
theorem balanced_biUnion_cover_rigidity
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A B : ι → Finset α)
    (hA : (I : Set ι).PairwiseDisjoint A)
    (hcard : ∀ i ∈ I, (A i).card = (B i).card)
    (hcover : I.biUnion A ⊆ I.biUnion B) :
    I.biUnion A = I.biUnion B ∧
      (I : Set ι).PairwiseDisjoint B := by
  have hsum : I.sum (fun i ↦ (A i).card) =
      I.sum (fun i ↦ (B i).card) := by
    exact Finset.sum_congr rfl hcard
  have hAcard : (I.biUnion A).card =
      I.sum (fun i ↦ (A i).card) := Finset.card_biUnion hA
  have hBcardLe : (I.biUnion B).card ≤
      I.sum (fun i ↦ (B i).card) := Finset.card_biUnion_le
  have hcardEq : (I.biUnion A).card = (I.biUnion B).card := by
    have hAB := Finset.card_le_card hcover
    omega
  have hunionEq : I.biUnion A = I.biUnion B :=
    Finset.eq_of_subset_of_card_le hcover hcardEq.ge
  have hBexact : (I.biUnion B).card =
      I.sum (fun i ↦ (B i).card) := by omega
  exact ⟨hunionEq,
    pairwiseDisjoint_of_card_biUnion_eq_sum_card I B hBexact⟩

/-- The balanced cover is encoded by an exact nonnegative incidence matrix:
every target row and every source column is partitioned by the corresponding
intersections. -/
theorem balanced_biUnion_cover_incidence_margins
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A B : ι → Finset α)
    (hA : (I : Set ι).PairwiseDisjoint A)
    (hcard : ∀ i ∈ I, (A i).card = (B i).card)
    (hcover : I.biUnion A ⊆ I.biUnion B) :
    (∀ i ∈ I, (A i).card =
        I.sum (fun j ↦ (A i ∩ B j).card)) ∧
      (∀ j ∈ I, (B j).card =
        I.sum (fun i ↦ (A i ∩ B j).card)) := by
  obtain ⟨hunion, hB⟩ :=
    balanced_biUnion_cover_rigidity I A B hA hcard hcover
  constructor
  · intro i hi
    apply card_eq_sum_card_inter_of_subset_biUnion_of_pairwiseDisjoint
      (A i) I B hB
    intro x hxi
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩
  · intro j hj
    have hcol := card_eq_sum_card_inter_of_subset_biUnion_of_pairwiseDisjoint
      (B j) I A hA (by
        intro x hxj
        rw [hunion]
        exact Finset.mem_biUnion.mpr ⟨j, hj, hxj⟩)
    simpa [Finset.inter_comm] using hcol

/-- Without assuming coverage, balanced families have an exact dichotomy:
either some target value escapes every source, or the two families form the
rigid equal-union incidence decomposition above. -/
theorem balanced_biUnion_exists_escape_or_rigidity
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A B : ι → Finset α)
    (hA : (I : Set ι).PairwiseDisjoint A)
    (hcard : ∀ i ∈ I, (A i).card = (B i).card) :
    (∃ x ∈ I.biUnion A, x ∉ I.biUnion B) ∨
      (I.biUnion A = I.biUnion B ∧
        (I : Set ι).PairwiseDisjoint B ∧
        (∀ i ∈ I, (A i).card =
          I.sum (fun j ↦ (A i ∩ B j).card)) ∧
        (∀ j ∈ I, (B j).card =
          I.sum (fun i ↦ (A i ∩ B j).card))) := by
  classical
  by_cases hcover : I.biUnion A ⊆ I.biUnion B
  · right
    obtain ⟨hunion, hB⟩ :=
      balanced_biUnion_cover_rigidity I A B hA hcard hcover
    obtain ⟨hrow, hcol⟩ :=
      balanced_biUnion_cover_incidence_margins I A B hA hcard hcover
    exact ⟨hunion, hB, hrow, hcol⟩
  · left
    simpa only [Finset.not_subset] using hcover

section RestorationBalancedCover

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The complete local data needed for one live restoration transport edge.
The source and target faces of the datum both have half the padding weight of
`target`. -/
structure LiveRestorationEdgeDatum
    (g : Fin (m + 1) → G) (h : G) where
  root : ReducedSubsetSumCollision g h
  target : ReducedSubsetSumCollision g h
  drop : Fin m
  other : Fin m
  root_support_le_target : (reducedCollisionSupport root).card ≤
    (reducedCollisionSupport target).card
  dropped_nonempty :
    (reducedCollisionDroppedSupport root target).Nonempty
  drop_ne_other : drop ≠ other
  root_positive_card : root.val.1.card = 1
  root_negative_pair : root.val.2 = {drop, other}
  drop_avoids_target : drop ∉ reducedCollisionSupport target
  other_mem_target_negative : other ∈ target.val.2
  rootPositive_inter_targetNegative :
    (root.val.1 ∩ target.val.2).Nonempty

/-- Excluded source value face of a live edge datum. -/
noncomputable def LiveRestorationEdgeDatum.sourceValueFace
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) : Finset G :=
  restorationFanForcedExcludedValueSlice e.root e.target e.drop

/-- Transported target value face of a live edge datum. -/
noncomputable def LiveRestorationEdgeDatum.targetValueFace
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) : Finset G :=
  restorationFanExcludedTransportValueSlice e.target e.drop

/-- Padding weight carried by either half-face of a live edge datum. -/
def LiveRestorationEdgeDatum.weight
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) : ℕ :=
  reducedCollisionWeight (m := m) e.target

/-- Exact target-face weight of a live edge datum. -/
theorem LiveRestorationEdgeDatum.two_mul_card_targetValueFace
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (e : LiveRestorationEdgeDatum g h) :
    2 * e.targetValueFace.card = e.weight := by
  exact two_mul_card_restorationFanExcludedTransportValueSlice
    hg e.target e.drop e.drop_avoids_target

/-- Exact source-face weight of a live edge datum. -/
theorem LiveRestorationEdgeDatum.two_mul_card_sourceValueFace
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (e : LiveRestorationEdgeDatum g h) :
    2 * e.sourceValueFace.card = e.weight := by
  exact two_mul_card_restorationFanForcedExcludedValueSlice
    hg e.root e.target e.root_support_le_target e.dropped_nonempty
      e.drop e.other e.root_positive_card e.root_negative_pair
        e.drop_avoids_target e.other_mem_target_negative
          e.rootPositive_inter_targetNegative

/-- Distinct canonical targets make the transported target faces of a finite
live edge family pairwise disjoint. -/
theorem liveRestorationEdgeDatum_targetValueFaces_pairwiseDisjoint
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I) :
    (I : Set ι).PairwiseDisjoint
      (fun i ↦ (e i).targetValueFace) := by
  intro i hi j hj hij
  have htargetNe : (e i).target ≠ (e j).target := by
    intro heq
    exact hij (hinjective hi hj heq)
  exact canonical_restorationFanExcludedTransportValueSlices_disjoint
    hg hh hh0 (e i).target (e j).target
      (hcanonical i hi) (hcanonical j hj) htargetNe
        (e i).drop (e j).drop

/-- Global escape-or-rigidity for a finite family of genuine canonical
restoration edges.  Since source and target mass balance edge by edge,
failure of a global escape forces equal unions, pairwise-disjoint sources,
and exact row/column incidence margins. -/
theorem liveRestorationEdgeDatum_exists_globalEscape_or_balancedRigidity
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I) :
    (∃ x ∈ I.biUnion (fun i ↦ (e i).targetValueFace),
        x ∉ I.biUnion (fun i ↦ (e i).sourceValueFace)) ∨
      (I.biUnion (fun i ↦ (e i).targetValueFace) =
          I.biUnion (fun i ↦ (e i).sourceValueFace) ∧
        (I : Set ι).PairwiseDisjoint
          (fun i ↦ (e i).sourceValueFace) ∧
        (∀ i ∈ I, (e i).targetValueFace.card =
          I.sum (fun j ↦
            ((e i).targetValueFace ∩ (e j).sourceValueFace).card)) ∧
        (∀ j ∈ I, (e j).sourceValueFace.card =
          I.sum (fun i ↦
            ((e i).targetValueFace ∩ (e j).sourceValueFace).card))) := by
  apply balanced_biUnion_exists_escape_or_rigidity I
    (fun i ↦ (e i).targetValueFace)
    (fun i ↦ (e i).sourceValueFace)
  · exact liveRestorationEdgeDatum_targetValueFaces_pairwiseDisjoint
      hg hh hh0 I e hcanonical hinjective
  · intro i hi
    have htarget := (e i).two_mul_card_targetValueFace hg
    have hsource := (e i).two_mul_card_sourceValueFace hg
    omega

end RestorationBalancedCover

end MinModulus
