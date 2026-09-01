import MinModulus.G1TransportOddProjection

namespace MinModulus

open Finset

variable {m : ℕ}

/-- A Boolean face with coordinates in `F` forced to one and coordinates in
`D` forced to zero. -/
noncomputable def booleanConstraintFace
    (F D : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  blockedSignatureUpperSubsetLayer F ∩ blockedSignatureSubsetLayer D

@[simp]
theorem mem_booleanConstraintFace_iff
    {F D S : Finset (Fin m)} :
    S ∈ booleanConstraintFace F D ↔ F ⊆ S ∧ Disjoint S D := by
  classical
  rw [booleanConstraintFace, Finset.mem_inter,
    mem_blockedSignatureUpperSubsetLayer_iff,
    blockedSignatureSubsetLayer, Finset.mem_powerset]
  constructor
  · rintro ⟨hFS, hSD⟩
    refine ⟨hFS, ?_⟩
    rw [Finset.disjoint_left]
    intro x hxS hxD
    exact (Finset.mem_sdiff.mp (hSD hxS)).2 hxD
  · rintro ⟨hFS, hSD⟩
    refine ⟨hFS, ?_⟩
    intro x hxS
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, Finset.disjoint_left.mp hSD hxS⟩

/-- Inclusion of nonempty Boolean faces is exactly reverse inclusion of their
required and forbidden constraint sets. -/
theorem booleanConstraintFace_subset_iff
    {F D F' D' : Finset (Fin m)}
    (hFD : Disjoint F D) :
    booleanConstraintFace F D ⊆ booleanConstraintFace F' D' ↔
      F' ⊆ F ∧ D' ⊆ D := by
  constructor
  · intro hsub
    have hFmem : F ∈ booleanConstraintFace F D :=
      mem_booleanConstraintFace_iff.mpr ⟨Finset.Subset.rfl, hFD⟩
    have hFtarget := mem_booleanConstraintFace_iff.mp (hsub hFmem)
    refine ⟨hFtarget.1, ?_⟩
    intro x hxD'
    by_contra hxD
    let S := insert x F
    have hSD : Disjoint S D := by
      rw [Finset.disjoint_left]
      intro y hyS hyD
      rcases Finset.mem_insert.mp hyS with rfl | hyF
      · exact hxD hyD
      · exact Finset.disjoint_left.mp hFD hyF hyD
    have hSmem : S ∈ booleanConstraintFace F D :=
      mem_booleanConstraintFace_iff.mpr
        ⟨Finset.subset_insert x F, hSD⟩
    have hStarget := mem_booleanConstraintFace_iff.mp (hsub hSmem)
    exact Finset.disjoint_left.mp hStarget.2
      (Finset.mem_insert_self x F) hxD'
  · rintro ⟨hF, hD⟩ S hS
    have hface := mem_booleanConstraintFace_iff.mp hS
    exact mem_booleanConstraintFace_iff.mpr
      ⟨hF.trans hface.1, hface.2.mono_right hD⟩

/-- Under consistency, two Boolean faces are equal exactly when both pairs of
constraint sets are equal. -/
theorem booleanConstraintFace_eq_iff
    {F D F' D' : Finset (Fin m)}
    (hFD : Disjoint F D) (hF'D' : Disjoint F' D') :
    booleanConstraintFace F D = booleanConstraintFace F' D' ↔
      F = F' ∧ D = D' := by
  constructor
  · intro heq
    have hfwdSub : booleanConstraintFace F D ⊆
        booleanConstraintFace F' D' := by
      intro S hS
      rwa [← heq]
    have hbackSub : booleanConstraintFace F' D' ⊆
        booleanConstraintFace F D := by
      intro S hS
      rwa [heq]
    have hforward := (booleanConstraintFace_subset_iff hFD).mp
      hfwdSub
    have hback := (booleanConstraintFace_subset_iff hF'D').mp
      hbackSub
    exact ⟨Finset.Subset.antisymm hback.1 hforward.1,
      Finset.Subset.antisymm hback.2 hforward.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Intersecting two Boolean faces simply accumulates both sets of
constraints. -/
theorem booleanConstraintFaces_inter
    (F D F' D' : Finset (Fin m)) :
    booleanConstraintFace F D ∩ booleanConstraintFace F' D' =
      booleanConstraintFace (F ∪ F') (D ∪ D') := by
  classical
  ext S
  simp only [Finset.mem_inter, mem_booleanConstraintFace_iff,
    Finset.union_subset_iff, Finset.disjoint_union_right]
  tauto

/-- Exact cardinality of a consistent Boolean face. -/
theorem card_booleanConstraintFace
    (F D : Finset (Fin m)) (hFD : Disjoint F D) :
    (booleanConstraintFace F D).card =
      2 ^ (m - (F ∪ D).card) := by
  rw [booleanConstraintFace,
    card_upperSubsetLayer_inter_blockedSubsetLayer F D hFD]

/-- An inconsistent Boolean face is empty. -/
theorem booleanConstraintFace_eq_empty_of_not_disjoint
    {F D : Finset (Fin m)} (hFD : ¬Disjoint F D) :
    booleanConstraintFace F D = ∅ := by
  classical
  ext S
  simp only [Finset.notMem_empty, iff_false]
  intro hS
  have hface := mem_booleanConstraintFace_iff.mp hS
  exact hFD (hface.2.mono_left hface.1)

/-- Distinct consistent Boolean faces with the same number of constrained
coordinates overlap in at most half of either face. -/
theorem two_mul_card_booleanConstraintFaces_inter_le_of_constraintCard_eq_of_ne
    {F D F' D' : Finset (Fin m)}
    (hFD : Disjoint F D)
    (hcard : (F ∪ D).card = (F' ∪ D').card)
    (hne : booleanConstraintFace F D ≠ booleanConstraintFace F' D') :
    2 * (booleanConstraintFace F D ∩
        booleanConstraintFace F' D').card ≤
      (booleanConstraintFace F D).card := by
  classical
  by_cases hcross : Disjoint (F ∪ F') (D ∪ D')
  · let C := F ∪ D
    let C' := F' ∪ D'
    have hnotSub : ¬C' ⊆ C := by
      intro hsub
      have hCC' : C' = C :=
        Finset.eq_of_subset_of_card_le hsub (by simpa [C, C'] using hcard.le)
      have hFF' : F = F' := by
        apply Finset.Subset.antisymm
        · intro x hxF
          have hxC : x ∈ C := Finset.mem_union_left _ hxF
          have hxC' : x ∈ C' := hCC'.symm ▸ hxC
          rcases Finset.mem_union.mp hxC' with hxF' | hxD'
          · exact hxF'
          · exact False.elim (Finset.disjoint_left.mp hcross
              (Finset.mem_union_left _ hxF)
              (Finset.mem_union_right _ hxD'))
        · intro x hxF'
          have hxC' : x ∈ C' := Finset.mem_union_left _ hxF'
          have hxC : x ∈ C := hCC' ▸ hxC'
          rcases Finset.mem_union.mp hxC with hxF | hxD
          · exact hxF
          · exact False.elim (Finset.disjoint_left.mp hcross
              (Finset.mem_union_right _ hxF')
              (Finset.mem_union_left _ hxD))
      have hDD' : D = D' := by
        apply Finset.Subset.antisymm
        · intro x hxD
          have hxC : x ∈ C := Finset.mem_union_right _ hxD
          have hxC' : x ∈ C' := hCC'.symm ▸ hxC
          rcases Finset.mem_union.mp hxC' with hxF' | hxD'
          · exact False.elim (Finset.disjoint_left.mp hcross
              (Finset.mem_union_right _ hxF')
              (Finset.mem_union_left _ hxD))
          · exact hxD'
        · intro x hxD'
          have hxC' : x ∈ C' := Finset.mem_union_right _ hxD'
          have hxC : x ∈ C := hCC' ▸ hxC'
          rcases Finset.mem_union.mp hxC with hxF | hxD
          · exact False.elim (Finset.disjoint_left.mp hcross
              (Finset.mem_union_left _ hxF)
              (Finset.mem_union_right _ hxD'))
          · exact hxD
      exact hne (by rw [hFF', hDD'])
    have hproper : C ⊂ C ∪ C' := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      intro heq
      apply hnotSub
      intro x hxC'
      have : x ∈ C ∪ C' := Finset.mem_union_right _ hxC'
      rw [← heq] at this
      exact this
    have hconstraintGrowth : C.card + 1 ≤ (C ∪ C').card := by
      have := Finset.card_lt_card hproper
      omega
    have hUnionEq : (F ∪ F') ∪ (D ∪ D') = C ∪ C' := by
      simp only [C, C']
      ext x
      simp only [Finset.mem_union]
      tauto
    have hAllLe : (C ∪ C').card ≤ m := by
      simpa using Finset.card_le_univ (C ∪ C')
    have hexp : m - (C ∪ C').card + 1 ≤ m - C.card := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp
    rw [booleanConstraintFaces_inter,
      card_booleanConstraintFace (F ∪ F') (D ∪ D') hcross,
      card_booleanConstraintFace F D hFD, hUnionEq]
    simpa [pow_succ, Nat.mul_comm, C] using hpow
  · rw [booleanConstraintFaces_inter,
      booleanConstraintFace_eq_empty_of_not_disjoint hcross]
    simp

section RestorationFaces

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- In the live singleton-positive profile, the excluded source slice is the
face forcing the restoration support and dropped coordinate, while avoiding
the rest of the root support. -/
theorem restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    restorationFanForcedExcludedSubsetSlice r q j =
      booleanConstraintFace
        (reducedCollisionRestorationFanSupport r q ∪ {j})
        ((reducedCollisionSupport r).erase j) := by
  classical
  have hcommon := restorationFanCommonBlockedSupport_eq_rootSupport_erase
    r q hcard hdrop j k hAcard hB hjq hkq hAq
  rw [restorationFanForcedExcludedSubsetSlice,
    booleanConstraintFace, hcommon]
  ext S
  simp only [Finset.mem_inter,
    mem_blockedSignatureUpperSubsetLayer_iff]
  constructor
  · rintro ⟨⟨hjS, hLower⟩, hHS⟩
    exact ⟨Finset.union_subset hHS hjS, hLower⟩
  · rintro ⟨hHjS, hLower⟩
    exact ⟨⟨hHjS.trans' Finset.subset_union_right,
      hLower⟩, hHjS.trans' Finset.subset_union_left⟩

omit [DecidableEq G] in
/-- The intrinsic transported face is already in Boolean-constraint normal
form. -/
theorem restorationFanExcludedTransportSubsetSlice_eq_booleanConstraintFace
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m) :
    restorationFanExcludedTransportSubsetSlice q j =
      booleanConstraintFace (q.val.2 ∪ {j}) q.val.1 := rfl

omit [DecidableEq G] in
/-- The required and forbidden constraints of a transported face are
consistent whenever the dropped coordinate is outside the target support. -/
theorem restorationFanExcludedTransport_constraints_disjoint
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q) :
    Disjoint (q.val.2 ∪ {j}) q.val.1 := by
  rw [Finset.disjoint_union_left]
  constructor
  · exact q.property.1.symm
  · rw [Finset.disjoint_left]
    intro x hxj hxA
    have hx : x = j := by simpa using hxj
    subst x
    exact hjq (Finset.mem_union_left _ hxA)

omit [DecidableEq G] in
/-- The required and forbidden constraints of a live excluded source face are
consistent. -/
theorem restorationFanForcedExcluded_constraints_disjoint
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) :
    Disjoint
      (reducedCollisionRestorationFanSupport r q ∪ {j})
      ((reducedCollisionSupport r).erase j) := by
  rw [Finset.disjoint_union_left]
  constructor
  · rw [Finset.disjoint_left]
    intro x hxH hxR
    have hxExt := restorationFanSupport_subset_external r q hcard hdrop hxH
    exact (Finset.mem_sdiff.mp hxExt).2 (Finset.mem_of_mem_erase hxR)
  · simp

omit [DecidableEq G] in
/-- The transported face fixes exactly the target support plus its dropped
coordinate. -/
theorem card_restorationFanExcludedTransport_constraints
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q) :
    ((q.val.2 ∪ {j}) ∪ q.val.1).card =
      (reducedCollisionSupport q).card + 1 := by
  have hunion : (q.val.2 ∪ {j}) ∪ q.val.1 =
      reducedCollisionSupport q ∪ {j} := by
    ext x
    simp only [reducedCollisionSupport, Finset.mem_union,
      Finset.mem_singleton]
    tauto
  rw [hunion]
  simpa [Finset.union_comm] using
    Finset.card_insert_of_notMem hjq

omit [DecidableEq G] in
/-- A live excluded source face fixes exactly the next target support plus
the next dropped coordinate. -/
theorem card_restorationFanForcedExcluded_constraints
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    ((reducedCollisionRestorationFanSupport r q ∪ {j}) ∪
        (reducedCollisionSupport r).erase j).card =
      (reducedCollisionSupport q).card + 1 := by
  let H := reducedCollisionRestorationFanSupport r q
  have hHq : H ⊆ reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  have hcommon := restorationFanCommonBlockedSupport_eq_rootSupport_erase
    r q hcard hdrop j k hAcard hB hjq hkq hAq
  have hqDecomp : reducedCollisionSupport q =
      H ∪ (reducedCollisionSupport r).erase j := by
    calc
      reducedCollisionSupport q =
          H ∪ (reducedCollisionSupport q \ H) :=
        (Finset.union_sdiff_of_subset hHq).symm
      _ = H ∪ (reducedCollisionSupport r).erase j := by rw [hcommon]
  have hunion : (H ∪ {j}) ∪ (reducedCollisionSupport r).erase j =
      reducedCollisionSupport q ∪ {j} := by
    rw [hqDecomp]
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton]
    tauto
  change ((H ∪ {j}) ∪
      (reducedCollisionSupport r).erase j).card = _
  rw [hunion]
  simpa [Finset.union_comm] using
    Finset.card_insert_of_notMem hjq

omit [DecidableEq G] in
/-- Exact face matching with a next live restoration source is equivalent to
two concrete equalities of coordinate constraints. -/
theorem restorationFanTransportFace_eq_nextExcluded_iff
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m) (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty) :
    restorationFanExcludedTransportSubsetSlice q j =
        restorationFanForcedExcludedSubsetSlice r' q' j' ↔
      q.val.2 ∪ {j} =
          reducedCollisionRestorationFanSupport r' q' ∪ {j'} ∧
        q.val.1 = (reducedCollisionSupport r').erase j' := by
  rw [restorationFanExcludedTransportSubsetSlice_eq_booleanConstraintFace,
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq']
  exact booleanConstraintFace_eq_iff
    (restorationFanExcludedTransport_constraints_disjoint q j hjq)
    (restorationFanForcedExcluded_constraints_disjoint
      r' q' hcard' hdrop' j')

omit [DecidableEq G] in
/-- In particular, an exact next-source match forces the current target to
have exactly two positive coordinates. -/
theorem targetPositive_card_eq_two_of_restorationFace_match
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m) (hj'k' : j' ≠ k')
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty)
    (hmatch : restorationFanExcludedTransportSubsetSlice q j =
      restorationFanForcedExcludedSubsetSlice r' q' j') :
    q.val.1.card = 2 := by
  have hconstraints :=
    (restorationFanTransportFace_eq_nextExcluded_iff
      q j hjq r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq').mp
        hmatch
  have hBcard : r'.val.2.card = 2 := by
    rw [hB']
    simp [hj'k']
  have hrootCard : (reducedCollisionSupport r').card = 3 := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint r'.property.1,
      hAcard', hBcard]
  have hj'Root : j' ∈ reducedCollisionSupport r' := by
    apply Finset.mem_union_right
    rw [hB']
    simp
  rw [hconstraints.2, Finset.card_erase_of_mem hj'Root, hrootCard]

omit [DecidableEq G] in
/-- Therefore a target with positive-tail cardinality different from two
cannot be an exact live restoration source at the next root. -/
theorem restorationFanTransportFace_ne_nextExcluded_of_positive_card_ne_two
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (hpositive : q.val.1.card ≠ 2)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m) (hj'k' : j' ≠ k')
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty) :
    restorationFanExcludedTransportSubsetSlice q j ≠
      restorationFanForcedExcludedSubsetSlice r' q' j' := by
  intro hmatch
  exact hpositive
    (targetPositive_card_eq_two_of_restorationFace_match
      q j hjq r' q' hcard' hdrop' j' k' hj'k' hAcard' hB'
        hjq' hkq' hAq' hmatch)

omit [DecidableEq G] in
/-- If an equal-support-rank next source is not in the two-positive matching
profile, it captures at most half of the transported face. -/
theorem two_mul_card_restorationFanTransportFace_inter_nextExcluded_le
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (hpositive : q.val.1.card ≠ 2)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m) (hj'k' : j' ≠ k')
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty)
    (hsupportCard : (reducedCollisionSupport q).card =
      (reducedCollisionSupport q').card) :
    2 * (restorationFanExcludedTransportSubsetSlice q j ∩
        restorationFanForcedExcludedSubsetSlice r' q' j').card ≤
      (restorationFanExcludedTransportSubsetSlice q j).card := by
  rw [restorationFanExcludedTransportSubsetSlice_eq_booleanConstraintFace,
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq']
  apply
    two_mul_card_booleanConstraintFaces_inter_le_of_constraintCard_eq_of_ne
  · exact restorationFanExcludedTransport_constraints_disjoint q j hjq
  · rw [card_restorationFanExcludedTransport_constraints q j hjq,
      card_restorationFanForcedExcluded_constraints
        r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq',
      hsupportCard]
  · intro heq
    apply restorationFanTransportFace_ne_nextExcluded_of_positive_card_ne_two
      q j hjq hpositive r' q' hcard' hdrop' j' k' hj'k' hAcard' hB'
        hjq' hkq' hAq'
    rw [restorationFanExcludedTransportSubsetSlice_eq_booleanConstraintFace,
      restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
        r' q' hcard' hdrop' j' k' hAcard' hB' hjq' hkq' hAq']
    exact heq

/-- Under subset-sum injectivity, the same half-overlap estimate holds for
the actual value faces used by the global lower-bound count. -/
theorem two_mul_card_restorationFanTransportValueFace_inter_nextExcluded_le
    {g : Fin (m + 1) → G} {h : G}
    (hg : ValidTuple g)
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q)
    (hpositive : q.val.1.card ≠ 2)
    (r' q' : ReducedSubsetSumCollision g h)
    (hcard' : (reducedCollisionSupport r').card ≤
      (reducedCollisionSupport q').card)
    (hdrop' : (reducedCollisionDroppedSupport r' q').Nonempty)
    (j' k' : Fin m) (hj'k' : j' ≠ k')
    (hAcard' : r'.val.1.card = 1)
    (hB' : r'.val.2 = {j', k'})
    (hjq' : j' ∉ reducedCollisionSupport q')
    (hkq' : k' ∈ q'.val.2)
    (hAq' : (r'.val.1 ∩ q'.val.2).Nonempty)
    (hsupportCard : (reducedCollisionSupport q).card =
      (reducedCollisionSupport q').card) :
    2 * (restorationFanExcludedTransportValueSlice q j ∩
        restorationFanForcedExcludedValueSlice r' q' j').card ≤
      (restorationFanExcludedTransportValueSlice q j).card := by
  rw [restorationFanExcludedTransportValueSlice,
    restorationFanForcedExcludedValueSlice,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  exact two_mul_card_restorationFanTransportFace_inter_nextExcluded_le
    q j hjq hpositive r' q' hcard' hdrop' j' k' hj'k' hAcard' hB'
      hjq' hkq' hAq' hsupportCard

omit [DecidableEq G] in
/-- For the two selected targets at one root, the transported face of one is
disjoint from the opposite excluded source face.  Thus no same-root edge can
continue the affine path. -/
theorem restorationFanTransportFace_disjoint_oppositeExcludedSource
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2)
    (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    Disjoint (restorationFanExcludedTransportSubsetSlice v j)
      (restorationFanForcedExcludedSubsetSlice r u k) := by
  classical
  have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
  have hsource :=
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      r u hcardu hdropu k j hAcard hBswap hku hju hAu
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hjRoot : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hjErase : j ∈ (reducedCollisionSupport r).erase k :=
    Finset.mem_erase.mpr ⟨hjk, hjRoot⟩
  rw [Finset.disjoint_left]
  intro S hSv hSu
  have hSRoot :=
    restorationFanExcludedTransportSubsetSlice_subset_rootUpper
      r v j k hAcard hB hkv hAv hSv
  have hjS :=
    (mem_blockedSignatureUpperSubsetLayer_iff.mp hSRoot) hjRoot
  rw [hsource] at hSu
  have hSAvoid := (mem_booleanConstraintFace_iff.mp hSu).2
  exact Finset.disjoint_left.mp hSAvoid hjS hjErase

end RestorationFaces

end MinModulus
