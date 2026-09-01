import MinModulus.G1TransportFaceMatching

namespace MinModulus

open Finset

variable {m : ℕ}

/-- A candidate face fixing at least `d` more coordinates than a consistent
source face captures at most a `2^-d` fraction of the source. -/
theorem pow_mul_card_booleanConstraintFaces_inter_le_of_constraintGrowth
    {F D F' D' : Finset (Fin m)}
    (hFD : Disjoint F D) (d : ℕ)
    (hgrowth : (F ∪ D).card + d ≤ (F' ∪ D').card) :
    2 ^ d * (booleanConstraintFace F D ∩
        booleanConstraintFace F' D').card ≤
      (booleanConstraintFace F D).card := by
  classical
  by_cases hcross : Disjoint (F ∪ F') (D ∪ D')
  · let C := F ∪ D
    let U := (F ∪ F') ∪ (D ∪ D')
    have hcandidate : F' ∪ D' ⊆ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxF' | hxD'
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxF')
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxD')
    have hconstraintGrowth : C.card + d ≤ U.card :=
      hgrowth.trans (Finset.card_le_card hcandidate)
    have hUle : U.card ≤ m := by
      simpa [U] using Finset.card_le_univ U
    have hexp : d + (m - U.card) ≤ m - C.card := by omega
    have hpow := Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) hexp
    rw [booleanConstraintFaces_inter,
      card_booleanConstraintFace (F ∪ F') (D ∪ D') hcross,
      card_booleanConstraintFace F D hFD]
    have hU : (F ∪ F') ∪ (D ∪ D') = U := rfl
    rw [hU]
    simpa [pow_add, Nat.mul_comm, C] using hpow
  · rw [booleanConstraintFaces_inter,
      booleanConstraintFace_eq_empty_of_not_disjoint hcross]
    simp

/-- A cover of a finite set by an indexed family is bounded by the sum of
the intersections with the covered set. -/
theorem card_le_sum_card_inter_of_subset_biUnion
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hcover : A ⊆ I.biUnion B) :
    A.card ≤ I.sum (fun i ↦ (A ∩ B i).card) := by
  have hsub : A ⊆ I.biUnion (fun i ↦ A ∩ B i) := by
    intro x hxA
    rcases Finset.mem_biUnion.mp (hcover hxA) with ⟨i, hiI, hxi⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, hiI, Finset.mem_inter.mpr ⟨hxA, hxi⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- In particular, covering a consistent Boolean face by faces that each fix
at least `d` additional coordinates requires at least `2^d` members. -/
theorem pow_le_card_of_booleanConstraintFace_subset_biUnion_of_constraintGrowth
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F D : Finset (Fin m))
    (F' D' : ι → Finset (Fin m))
    (hFD : Disjoint F D) (d : ℕ)
    (hgrowth : ∀ i ∈ I,
      (F ∪ D).card + d ≤ (F' i ∪ D' i).card)
    (hcover : booleanConstraintFace F D ⊆
      I.biUnion (fun i ↦ booleanConstraintFace (F' i) (D' i))) :
    2 ^ d ≤ I.card := by
  classical
  let A := booleanConstraintFace F D
  let B : ι → Finset (Finset (Fin m)) := fun i ↦
    booleanConstraintFace (F' i) (D' i)
  have hcoverCard : A.card ≤ I.sum (fun i ↦ (A ∩ B i).card) :=
    card_le_sum_card_inter_of_subset_biUnion A I B hcover
  have hinter : ∀ i ∈ I,
      2 ^ d * (A ∩ B i).card ≤ A.card := by
    intro i hi
    exact pow_mul_card_booleanConstraintFaces_inter_le_of_constraintGrowth
      hFD d (hgrowth i hi)
  have hscaled : 2 ^ d * A.card ≤ I.card * A.card := by
    calc
      2 ^ d * A.card ≤
          2 ^ d * I.sum (fun i ↦ (A ∩ B i).card) :=
        Nat.mul_le_mul_left _ hcoverCard
      _ = I.sum (fun i ↦ 2 ^ d * (A ∩ B i).card) := by
        rw [Finset.mul_sum]
      _ ≤ I.sum (fun _ ↦ A.card) := by
        exact Finset.sum_le_sum hinter
      _ = I.card * A.card := by simp
  have hApos : 0 < A.card := by
    rw [Finset.card_pos]
    exact ⟨F, mem_booleanConstraintFace_iff.mpr
      ⟨Finset.Subset.rfl, hFD⟩⟩
  exact Nat.le_of_mul_le_mul_right hscaled hApos

section RestorationFaces

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Support growth of a prospective next target gives exponential decay of
its overlap with the current transported restoration face. -/
theorem pow_supportGrowth_mul_card_restorationFanTransportFace_inter_nextExcluded_le
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m)
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty)
    (d : ℕ)
    (hsupportGrowth : (reducedCollisionSupport q).card + d ≤
      (reducedCollisionSupport q').card) :
    2 ^ d * (restorationFanExcludedTransportSubsetSlice q j ∩
        restorationFanForcedExcludedSubsetSlice r' q' j').card ≤
      (restorationFanExcludedTransportSubsetSlice q j).card := by
  rw [restorationFanExcludedTransportSubsetSlice_eq_booleanConstraintFace,
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq']
  apply pow_mul_card_booleanConstraintFaces_inter_le_of_constraintGrowth
    (restorationFanExcludedTransport_constraints_disjoint q j hjq) d
  rw [card_restorationFanExcludedTransport_constraints q j hjq,
    card_restorationFanForcedExcluded_constraints
      r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq']
  omega

/-- Under validity, support-growth decay transfers unchanged to the value
faces used in the global packing. -/
theorem pow_supportGrowth_mul_card_restorationFanTransportValueFace_inter_nextExcluded_le
    {g : Fin (m + 1) → G} {h : G}
    (hg : ValidTuple g)
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m)
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty)
    (d : ℕ)
    (hsupportGrowth : (reducedCollisionSupport q).card + d ≤
      (reducedCollisionSupport q').card) :
    2 ^ d * (restorationFanExcludedTransportValueSlice q j ∩
        restorationFanForcedExcludedValueSlice r' q' j').card ≤
      (restorationFanExcludedTransportValueSlice q j).card := by
  rw [restorationFanExcludedTransportValueSlice,
    restorationFanForcedExcludedValueSlice,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  exact
    pow_supportGrowth_mul_card_restorationFanTransportFace_inter_nextExcluded_le
      q j hjq r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq'
        d hsupportGrowth

/-- The transported target value face has exactly half of its collision's
padding weight. -/
theorem two_mul_card_restorationFanExcludedTransportValueSlice
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q) :
    2 * (restorationFanExcludedTransportValueSlice q j).card =
      reducedCollisionWeight (m := m) q := by
  rw [restorationFanExcludedTransportValueSlice,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    two_mul_card_restorationFanExcludedTransportSubsetSlice q j hjq]

/-- If a transported target value face is covered by finitely many live
excluded successor sources, their total target padding weight is at least the
current target's weight.  This is the aggregate bridge to the canonical-star
weight budget. -/
theorem reducedCollisionWeight_le_sum_of_transportValueFace_cover
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (I : Finset ι)
    (r' q' : ι → ReducedSubsetSumCollision g h)
    (j' k' : ι → Fin m)
    (hcard' : ∀ i ∈ I, (reducedCollisionSupport (r' i)).card ≤
      (reducedCollisionSupport (q' i)).card)
    (hdrop' : ∀ i ∈ I,
      (reducedCollisionDroppedSupport (r' i) (q' i)).Nonempty)
    (hAcard' : ∀ i ∈ I, (r' i).val.1.card = 1)
    (hB' : ∀ i ∈ I, (r' i).val.2 = {j' i, k' i})
    (hjq' : ∀ i ∈ I, j' i ∉ reducedCollisionSupport (q' i))
    (hkq' : ∀ i ∈ I, k' i ∈ (q' i).val.2)
    (hAq' : ∀ i ∈ I, ((r' i).val.1 ∩ (q' i).val.2).Nonempty)
    (hcover : restorationFanExcludedTransportValueSlice q j ⊆
      I.biUnion (fun i ↦
        restorationFanForcedExcludedValueSlice (r' i) (q' i) (j' i))) :
    reducedCollisionWeight (m := m) q ≤
      I.sum (fun i ↦ reducedCollisionWeight (m := m) (q' i)) := by
  classical
  let A := restorationFanExcludedTransportValueSlice q j
  let B : ι → Finset G := fun i ↦
    restorationFanForcedExcludedValueSlice (r' i) (q' i) (j' i)
  have hcoverCard : A.card ≤ I.sum (fun i ↦ (A ∩ B i).card) :=
    card_le_sum_card_inter_of_subset_biUnion A I B hcover
  have hinterLe : I.sum (fun i ↦ (A ∩ B i).card) ≤
      I.sum (fun i ↦ (B i).card) := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.card_le_card Finset.inter_subset_right
  calc
    reducedCollisionWeight (m := m) q = 2 * A.card :=
      (two_mul_card_restorationFanExcludedTransportValueSlice
        hg q j hjq).symm
    _ ≤ 2 * I.sum (fun i ↦ (B i).card) :=
      Nat.mul_le_mul_left 2 (hcoverCard.trans hinterLe)
    _ = I.sum (fun i ↦ 2 * (B i).card) := by
      rw [Finset.mul_sum]
    _ = I.sum (fun i ↦ reducedCollisionWeight (m := m) (q' i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact two_mul_card_restorationFanForcedExcludedValueSlice
        hg (r' i) (q' i) (hcard' i hi) (hdrop' i hi)
          (j' i) (k' i) (hAcard' i hi) (hB' i hi) (hjq' i hi)
            (hkq' i hi) (hAq' i hi)

end RestorationFaces

end MinModulus
