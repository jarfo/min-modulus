import MinModulus.G1TransportSameRootObstruction

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A reduced collision with one positive and two negative coordinates has
support cardinality three. -/
theorem reducedCollisionSupport_card_eq_three_of_one_two
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    (reducedCollisionSupport r).card = 3 := by
  rw [reducedCollisionSupport,
    Finset.card_union_of_disjoint r.property.1, hAcard, hBcard]

/-- In the live genuine-dominant residual, every other canonical collision
has support cardinality at least six. -/
theorem genuineDominant_liveRoot_all_other_support_card_six_le
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    ∀ v ∈ criticalCanonicalReducedCollisions g, v ≠ r →
      6 ≤ (reducedCollisionSupport v).card := by
  intro v hv hvr
  have hgrowth :=
    genuineDominant_two_tail_all_other_eighthWeight_growth
      hqodd g hg r hr hres hBcard v hv hvr
  have hrootCard :=
    reducedCollisionSupport_card_eq_three_of_one_two r hAcard hBcard
  omega

/-- Consequently the dominant collision is the unique canonical collision
with the live one-positive/two-negative profile.  No non-root canonical target
can itself be re-used as a live restoration root. -/
theorem genuineDominant_liveRoot_unique_one_two_profile
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    ∀ v ∈ criticalCanonicalReducedCollisions g,
      v.val.1.card = 1 → v.val.2.card = 2 → v = r := by
  intro v hv hvA hvB
  by_contra hvr
  have hsix := genuineDominant_liveRoot_all_other_support_card_six_le
    hqodd g hg r hr hres hAcard hBcard v hv hvr
  have hthree :=
    reducedCollisionSupport_card_eq_three_of_one_two v hvA hvB
  omega

/-- Any prospective live restoration edge whose root is canonical in the
critical family must therefore use the original dominant root. -/
theorem liveRestorationEdgeDatum_root_eq_dominant_of_canonical
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2)
    (e : LiveRestorationEdgeDatum g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (heroot : e.root ∈ criticalCanonicalReducedCollisions g) :
    e.root = r := by
  apply genuineDominant_liveRoot_unique_one_two_profile
    hqodd g hg r hr hres hAcard hBcard e.root heroot
  · exact e.root_positive_card
  · rw [e.root_negative_pair]
    simp [e.drop_ne_other]

omit [DecidableEq G] in
/-- More generally, the transported target of any live edge is disjoint from
the excluded source of every other live edge with the same root. -/
theorem liveRestorationEdgeDatum_targetSubset_disjoint_sourceSubset_of_root_eq
    {g : Fin (m + 1) → G} {h : G}
    (e f : LiveRestorationEdgeDatum g h)
    (hroot : e.root = f.root) :
    Disjoint
      (restorationFanExcludedTransportSubsetSlice e.target e.drop)
      (restorationFanForcedExcludedSubsetSlice f.root f.target f.drop) := by
  classical
  have hsource :=
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      f.root f.target f.root_support_le_target f.dropped_nonempty
      f.drop f.other f.root_positive_card f.root_negative_pair
      f.drop_avoids_target f.other_mem_target_negative
      f.rootPositive_inter_targetNegative
  have hotherB : f.other ∈ f.root.val.2 := by
    rw [f.root_negative_pair]
    simp
  have hotherRoot : f.other ∈ reducedCollisionSupport f.root :=
    Finset.mem_union_right _ hotherB
  have hotherErase : f.other ∈
      (reducedCollisionSupport f.root).erase f.drop :=
    Finset.mem_erase.mpr ⟨Ne.symm f.drop_ne_other, hotherRoot⟩
  rw [Finset.disjoint_left]
  intro T hTarget hSource
  have hRootUpper :=
    restorationFanExcludedTransportSubsetSlice_subset_rootUpper
      e.root e.target e.drop e.other e.root_positive_card
      e.root_negative_pair e.other_mem_target_negative
      e.rootPositive_inter_targetNegative hTarget
  have hotherERoot : f.other ∈ reducedCollisionSupport e.root := by
    rw [hroot]
    exact hotherRoot
  have hotherT :=
    (mem_blockedSignatureUpperSubsetLayer_iff.mp hRootUpper) hotherERoot
  rw [hsource] at hSource
  have hAvoid := (mem_booleanConstraintFace_iff.mp hSource).2
  exact Finset.disjoint_left.mp hAvoid hotherT hotherErase

/-- Validity transfers the all-same-root cross-edge obstruction to values. -/
theorem liveRestorationEdgeDatum_targetValue_disjoint_sourceValue_of_root_eq
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (e f : LiveRestorationEdgeDatum g h)
    (hroot : e.root = f.root) :
    Disjoint e.targetValueFace f.sourceValueFace := by
  classical
  rw [LiveRestorationEdgeDatum.targetValueFace,
    LiveRestorationEdgeDatum.sourceValueFace,
    restorationFanExcludedTransportValueSlice,
    restorationFanForcedExcludedValueSlice,
    Finset.disjoint_image (ssum_injective g hg)]
  exact
    liveRestorationEdgeDatum_targetSubset_disjoint_sourceSubset_of_root_eq
      e f hroot

/-- A family whose live edges all have the same root has transported union
disjoint from its entire source union. -/
theorem liveRestorationEdgeDatum_targetUnion_disjoint_sourceUnion_of_roots_eq
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (r : ReducedSubsetSumCollision g h)
    (hroot : ∀ i ∈ I, (e i).root = r) :
    Disjoint (I.biUnion (fun i ↦ (e i).targetValueFace))
      (I.biUnion (fun i ↦ (e i).sourceValueFace)) := by
  rw [Finset.disjoint_left]
  intro x hxTarget hxSource
  rcases Finset.mem_biUnion.mp hxTarget with ⟨i, hi, hxi⟩
  rcases Finset.mem_biUnion.mp hxSource with ⟨j, hj, hxj⟩
  have hijRoot : (e i).root = (e j).root :=
    (hroot i hi).trans (hroot j hj).symm
  exact Finset.disjoint_left.mp
    (liveRestorationEdgeDatum_targetValue_disjoint_sourceValue_of_root_eq
      hg (e i) (e j) hijRoot) hxi hxj

/-- A live edge's transported target value face is nonempty. -/
theorem LiveRestorationEdgeDatum.targetValueFace_nonempty
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (e : LiveRestorationEdgeDatum g h) : e.targetValueFace.Nonempty := by
  have hcard := e.two_mul_card_targetValueFace hg
  have hweight : 0 < e.weight := by
    simp [LiveRestorationEdgeDatum.weight, reducedCollisionWeight]
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty] at hcard
  simp at hcard
  omega

/-- Hence no nonempty rigid restoration permutation system can have every
edge root canonical in the live genuine-dominant family: uniqueness forces
all roots to be the dominant root, but same-root target and source unions are
disjoint rather than equal. -/
theorem not_liveRestorationPermutationSystem_of_all_roots_canonical
    {ι : Type*} [DecidableEq ι]
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2)
    (I : Finset ι)
    (e : ι → LiveRestorationEdgeDatum g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (heroot : ∀ i ∈ I, (e i).root ∈ criticalCanonicalReducedCollisions g) :
    ¬LiveRestorationPermutationSystem g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) I e := by
  intro S
  have hroot : ∀ i ∈ I, (e i).root = r := by
    intro i hi
    exact liveRestorationEdgeDatum_root_eq_dominant_of_canonical
      hqodd g S.valid r hr hres hAcard hBcard (e i) (heroot i hi)
  have hdisj :=
    liveRestorationEdgeDatum_targetUnion_disjoint_sourceUnion_of_roots_eq
      S.valid I e r hroot
  obtain ⟨i, hi⟩ := S.index_nonempty
  obtain ⟨x, hx⟩ := (e i).targetValueFace_nonempty S.valid
  have hxTarget : x ∈ I.biUnion (fun i ↦ (e i).targetValueFace) :=
    Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  have hxSource : x ∈ I.biUnion (fun i ↦ (e i).sourceValueFace) := by
    rw [← S.target_union_eq_source_union]
    exact hxTarget
  exact Finset.disjoint_left.mp hdisj hxTarget hxSource

end MinModulus
