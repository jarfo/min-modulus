/-
# Positive-upper occupancy inside the paired restoration packing

A singleton-positive/two-negative root divides the Boolean cube into eight
coarse root-pattern cells.  The root layer and its two upper faces occupy six
of them.  Every positive upper face consequently places at least three
quarters of its incidence mass inside the paired restoration packing.

Restricting the parity-split second moment to that packing and cancelling the
incidence factor gives the family-level internal-occupancy bound

  `9 W <= (|F|+2) |U intersect P|`.

Together with the exact complement identity, this isolates the remaining G1
problem as a multiplicity bound within the disjoint components of `P`.
-/
import MinModulus.G1PositiveUpperPairedComplement

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A directional root-pattern cell has at least two new fixed coordinates
relative to any positive upper face, and three when its live coordinate is not
already forced. -/
theorem directionalRootPattern_positiveUpper_inter_scale
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m)) (j : Fin m)
    (hRcard : (reducedCollisionSupport r).card = 3)
    (hjR : j ∈ reducedCollisionSupport r) :
    if j ∈ T then
      4 * (blockedSignatureUpperSubsetLayer T ∩
        directionalRootPatternSubsetCell r j).card ≤
          (blockedSignatureUpperSubsetLayer T).card
    else
      8 * (blockedSignatureUpperSubsetLayer T ∩
        directionalRootPatternSubsetCell r j).card ≤
          (blockedSignatureUpperSubsetLayer T).card := by
  classical
  let R := reducedCollisionSupport r
  let C := R.erase j
  have hCcard : C.card = 2 := by
    dsimp only [C]
    rw [Finset.card_erase_of_mem hjR, hRcard]
  have hjC : j ∉ C := by simp [C]
  have hEq :
      blockedSignatureUpperSubsetLayer T ∩
          directionalRootPatternSubsetCell r j =
        blockedSignatureUpperSubsetLayer (T ∪ {j}) ∩
          blockedSignatureSubsetLayer C := by
    ext S
    simp only [directionalRootPatternSubsetCell, C,
      Finset.mem_inter, mem_blockedSignatureUpperSubsetLayer_iff]
    constructor
    · rintro ⟨hTS, hjS, hLower⟩
      exact ⟨Finset.union_subset hTS (by simpa using hjS), hLower⟩
    · rintro ⟨hTjS, hLower⟩
      have hjUnion : j ∈ T ∪ {j} := by simp
      exact ⟨(fun x hx ↦ hTjS (Finset.mem_union_left _ hx)),
        (by simpa using hTjS hjUnion), hLower⟩
  by_cases hTC : (T ∩ C).Nonempty
  · have hdisj : Disjoint (blockedSignatureUpperSubsetLayer (T ∪ {j}))
        (blockedSignatureSubsetLayer C) := by
      apply blockedSignatureUpperSubsetLayer_disjoint
      rcases hTC with ⟨x, hx⟩
      exact ⟨x, Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp hx).2⟩⟩
    have hempty : blockedSignatureUpperSubsetLayer T ∩
        directionalRootPatternSubsetCell r j = ∅ := by
      rw [hEq]
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
  · have hTCdisj : Disjoint T C := by
      rw [Finset.disjoint_left]
      intro x hxT hxC
      exact hTC ⟨x, Finset.mem_inter.mpr ⟨hxT, hxC⟩⟩
    have hTjC : Disjoint (T ∪ {j}) C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      rcases Finset.mem_union.mp hx with hxT | hxj
      · exact Finset.disjoint_left.mp hTCdisj hxT hxC
      · have hxj' : x = j := by simpa using hxj
        exact hjC (hxj' ▸ hxC)
    rw [hEq,
      card_upperSubsetLayer_inter_blockedSubsetLayer _ _ hTjC,
      card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
    split_ifs with hjT
    · have hTj : T ∪ {j} = T := Finset.union_eq_left.mpr (by simpa using hjT)
      have hsumle : T.card + 2 ≤ m := by
        have hle := Finset.card_le_univ (T ∪ C)
        rw [Finset.card_union_of_disjoint hTCdisj, hCcard] at hle
        simpa using hle
      rw [hTj, Finset.card_union_of_disjoint hTCdisj, hCcard]
      have he : m - T.card = (m - (T.card + 2)) + 2 := by omega
      rw [he, pow_add]
      simp [Nat.mul_comm]
    · have hTjcard : (T ∪ {j}).card = T.card + 1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · simpa [Finset.disjoint_singleton] using hjT
      have hsumle : T.card + 3 ≤ m := by
        have hle := Finset.card_le_univ ((T ∪ {j}) ∪ C)
        rw [Finset.card_union_of_disjoint hTjC, hTjcard, hCcard] at hle
        simpa [Nat.add_assoc] using hle
      rw [Finset.card_union_of_disjoint hTjC, hTjcard, hCcard]
      have he : m - T.card = (m - (T.card + 1 + 2)) + 3 := by omega
      rw [he, pow_add]
      simp [Nat.mul_comm]

noncomputable def rootCoarsePairedSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) :=
  (blockedSignatureSubsetLayer (reducedCollisionSupport r) ∪
      blockedSignatureUpperSubsetLayer r.val.2) ∪
    blockedSignatureUpperSubsetLayer r.val.1

omit [DecidableEq G] in
theorem univ_sdiff_rootCoarsePairedSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k}) :
    (Finset.univ : Finset (Finset (Fin m))) \ rootCoarsePairedSubsetUnion r =
      directionalRootPatternSubsetCell r j ∪
        directionalRootPatternSubsetCell r k := by
  classical
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAcard
  have haR : a ∈ reducedCollisionSupport r :=
    Finset.mem_union_left _ (by rw [hA]; simp)
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ (by rw [hB]; simp)
  have hkR : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ (by rw [hB]; simp)
  have haj : a ≠ j := by
    intro haj
    have haB : a ∈ r.val.2 := by rw [hB]; simp [haj]
    exact Finset.disjoint_left.mp r.property.1
      (by rw [hA]; simp) haB
  have hak : a ≠ k := by
    intro hak
    have haB : a ∈ r.val.2 := by rw [hB]; simp [hak]
    exact Finset.disjoint_left.mp r.property.1
      (by rw [hA]; simp) haB
  ext S
  constructor
  · intro hS
    have hnot := (Finset.mem_sdiff.mp hS).2
    have hnotLower : S ∉ blockedSignatureSubsetLayer
        (reducedCollisionSupport r) := by
      intro hLower
      exact hnot (Finset.mem_union_left _ (Finset.mem_union_left _ hLower))
    have hnotB : S ∉ blockedSignatureUpperSubsetLayer r.val.2 := by
      intro hUpper
      exact hnot (Finset.mem_union_left _ (Finset.mem_union_right _ hUpper))
    have hnotA : S ∉ blockedSignatureUpperSubsetLayer r.val.1 := by
      intro hUpper
      exact hnot (Finset.mem_union_right _ hUpper)
    have haS : a ∉ S := by
      intro ha
      apply hnotA
      rw [mem_blockedSignatureUpperSubsetLayer_iff, hA]
      simpa using ha
    have hroot : ∃ x, x ∈ S ∧ x ∈ reducedCollisionSupport r := by
      by_contra hnone
      apply hnotLower
      rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
      intro x hxS
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxR ↦
        hnone ⟨x, hxS, hxR⟩⟩
    obtain ⟨x, hxS, hxR⟩ := hroot
    rcases Finset.mem_union.mp hxR with hxA | hxB
    · have hxa : x = a := by simpa [hA] using hxA
      exact False.elim (haS (hxa ▸ hxS))
    · rw [hB] at hxB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
      rcases hxB with rfl | rfl
      · have hkS : k ∉ S := by
          intro hk
          apply hnotB
          rw [mem_blockedSignatureUpperSubsetLayer_iff, hB]
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hxS
          · exact hk
        apply Finset.mem_union_left
        apply Finset.mem_inter.mpr
        constructor
        · rw [mem_blockedSignatureUpperSubsetLayer_iff]
          simpa using hxS
        · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
          intro y hyS
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hyErase
          have hyR := Finset.mem_of_mem_erase hyErase
          rcases Finset.mem_union.mp hyR with hyA | hyB
          · have hya : y = a := by simpa [hA] using hyA
            exact haS (hya ▸ hyS)
          · rw [hB] at hyB
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
            rcases hyB with rfl | rfl
            · exact (Finset.mem_erase.mp hyErase).1 rfl
            · exact hkS hyS
      · have hjS : j ∉ S := by
          intro hj
          apply hnotB
          rw [mem_blockedSignatureUpperSubsetLayer_iff, hB]
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hj
          · exact hxS
        apply Finset.mem_union_right
        apply Finset.mem_inter.mpr
        constructor
        · rw [mem_blockedSignatureUpperSubsetLayer_iff]
          simpa using hxS
        · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
          intro y hyS
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hyErase
          have hyR := Finset.mem_of_mem_erase hyErase
          rcases Finset.mem_union.mp hyR with hyA | hyB
          · have hya : y = a := by simpa [hA] using hyA
            exact haS (hya ▸ hyS)
          · rw [hB] at hyB
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
            rcases hyB with rfl | rfl
            · exact hjS hyS
            · exact (Finset.mem_erase.mp hyErase).1 rfl
  · intro hS
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcoarse
    rcases Finset.mem_union.mp hS with hjCell | hkCell
    · have hjS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hjCell).1) (Finset.mem_singleton_self j)
      have hLower := (Finset.mem_inter.mp hjCell).2
      have haNot : a ∉ S := by
        intro haS
        have haErase : a ∈ (reducedCollisionSupport r).erase j :=
          Finset.mem_erase.mpr ⟨haj, haR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower haS)).2 haErase
      have hkNot : k ∉ S := by
        intro hkS
        have hkErase : k ∈ (reducedCollisionSupport r).erase j :=
          Finset.mem_erase.mpr ⟨Ne.symm hjk, hkR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hkS)).2 hkErase
      rcases Finset.mem_union.mp hcoarse with hlowOrB | hupperA
      · rcases Finset.mem_union.mp hlowOrB with hlow | hupperB
        · have hallowed := Finset.mem_powerset.mp hlow hjS
          exact (Finset.mem_sdiff.mp hallowed).2 hjR
        · exact hkNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hupperB)
            (by rw [hB]; simp))
      · exact haNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hupperA)
          (by rw [hA]; simp))
    · have hkS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hkCell).1) (Finset.mem_singleton_self k)
      have hLower := (Finset.mem_inter.mp hkCell).2
      have haNot : a ∉ S := by
        intro haS
        have haErase : a ∈ (reducedCollisionSupport r).erase k :=
          Finset.mem_erase.mpr ⟨hak, haR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower haS)).2 haErase
      have hjNot : j ∉ S := by
        intro hjS
        have hjErase : j ∈ (reducedCollisionSupport r).erase k :=
          Finset.mem_erase.mpr ⟨hjk, hjR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hjS)).2 hjErase
      rcases Finset.mem_union.mp hcoarse with hlowOrB | hupperA
      · rcases Finset.mem_union.mp hlowOrB with hlow | hupperB
        · have hallowed := Finset.mem_powerset.mp hlow hkS
          exact (Finset.mem_sdiff.mp hallowed).2 hkR
        · exact hjNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hupperB)
            (by rw [hB]; simp))
      · exact haNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hupperA)
          (by rw [hA]; simp))

omit [DecidableEq G] in
/-- At most one quarter of a positive upper face lies outside the six coarse
root-pattern cells already contained in the paired packing. -/
theorem four_mul_card_positiveUpper_sdiff_rootCoarse_le
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m))
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k}) :
    4 * (blockedSignatureUpperSubsetLayer T \ rootCoarsePairedSubsetUnion r).card ≤
      (blockedSignatureUpperSubsetLayer T).card := by
  classical
  let UT := blockedSignatureUpperSubsetLayer T
  let Dj := directionalRootPatternSubsetCell r j
  let Dk := directionalRootPatternSubsetCell r k
  have hRcard : (reducedCollisionSupport r).card = 3 := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint r.property.1, hAcard, hB]
    simp [hjk]
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ (by rw [hB]; simp)
  have hkR : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ (by rw [hB]; simp)
  have hmissing : UT \ rootCoarsePairedSubsetUnion r = (UT ∩ Dj) ∪ (UT ∩ Dk) := by
    ext S
    have hcomp := Finset.ext_iff.mp
      (univ_sdiff_rootCoarsePairedSubsetUnion r j k hjk hAcard hB) S
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_inter] at hcomp ⊢
    tauto
  have hDjDk : Disjoint Dj Dk := by
    rw [Finset.disjoint_left]
    intro S hSj hSk
    have hjS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
      (Finset.mem_inter.mp hSj).1) (Finset.mem_singleton_self j)
    have hLowerK := (Finset.mem_inter.mp hSk).2
    have hjErase : j ∈ (reducedCollisionSupport r).erase k :=
      Finset.mem_erase.mpr ⟨hjk, hjR⟩
    exact (Finset.mem_sdiff.mp
      (Finset.mem_powerset.mp hLowerK hjS)).2 hjErase
  have hparts : Disjoint (UT ∩ Dj) (UT ∩ Dk) := by
    exact hDjDk.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
  have hcardMissing : (UT \ rootCoarsePairedSubsetUnion r).card =
      (UT ∩ Dj).card + (UT ∩ Dk).card := by
    rw [hmissing, Finset.card_union_of_disjoint hparts]
  have hjScale := directionalRootPattern_positiveUpper_inter_scale r T j hRcard hjR
  have hkScale := directionalRootPattern_positiveUpper_inter_scale r T k hRcard hkR
  by_cases hjT : j ∈ T
  · have hDkEmpty : UT ∩ Dk = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro S hS
      have hjS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hS).1) hjT
      have hLower := (Finset.mem_inter.mp (Finset.mem_inter.mp hS).2).2
      have hjErase : j ∈ (reducedCollisionSupport r).erase k :=
        Finset.mem_erase.mpr ⟨hjk, hjR⟩
      exact (Finset.mem_sdiff.mp
        (Finset.mem_powerset.mp hLower hjS)).2 hjErase
    simp only [hjT, if_true] at hjScale
    rw [hcardMissing, hDkEmpty]
    simpa [UT] using hjScale
  · by_cases hkT : k ∈ T
    · have hDjEmpty : UT ∩ Dj = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro S hS
        have hkS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
          (Finset.mem_inter.mp hS).1) hkT
        have hLower := (Finset.mem_inter.mp (Finset.mem_inter.mp hS).2).2
        have hkErase : k ∈ (reducedCollisionSupport r).erase j :=
          Finset.mem_erase.mpr ⟨Ne.symm hjk, hkR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hkS)).2 hkErase
      simp only [hkT, if_true] at hkScale
      rw [hcardMissing, hDjEmpty]
      simpa [UT] using hkScale
    · simp only [hjT, hkT, if_false] at hjScale hkScale
      have hjScale' : 8 * (UT ∩ Dj).card ≤ UT.card := by
        simpa [UT, Dj] using hjScale
      have hkScale' : 8 * (UT ∩ Dk).card ≤ UT.card := by
        simpa [UT, Dk] using hkScale
      rw [hcardMissing]
      change 4 * ((UT ∩ Dj).card + (UT ∩ Dk).card) ≤ UT.card
      omega

omit [DecidableEq G] in
/-- Equivalently, at least three quarters of every positive upper face lies
in the coarse root packing. -/
theorem three_mul_card_positiveUpper_le_four_mul_inter_rootCoarse
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m))
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k}) :
    3 * (blockedSignatureUpperSubsetLayer T).card ≤
      4 * (blockedSignatureUpperSubsetLayer T ∩ rootCoarsePairedSubsetUnion r).card := by
  have hcap := four_mul_card_positiveUpper_sdiff_rootCoarse_le r T j k hjk hAcard hB
  have hpartition := Finset.card_sdiff_add_card_inter
    (blockedSignatureUpperSubsetLayer T) (rootCoarsePairedSubsetUnion r)
  omega

noncomputable def rootCoarsePairedValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : Finset G :=
  (rootCoarsePairedSubsetUnion r).image (ssum g)

theorem rootCoarsePairedValueUnion_subset_pairedRestoration
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    rootCoarsePairedValueUnion r ⊆
      pairedRestorationFanValueUnionWithTailUpperFaces r v u j k := by
  classical
  rw [rootCoarsePairedValueUnion,
    ← image_pairedRestorationFanSubsetUnionWithTailUpperFaces]
  apply Finset.image_mono
  intro S hS
  rcases Finset.mem_union.mp hS with hlowOrB | hA
  · rcases Finset.mem_union.mp hlowOrB with hlow | hB
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hlow))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
  · exact Finset.mem_union_right _ hA

theorem three_mul_card_positiveUpperValue_le_four_mul_inter_rootCoarse
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k}) :
    3 * (reducedCollisionPositiveUpperValueLayer q).card ≤
      4 * (reducedCollisionPositiveUpperValueLayer q ∩
        rootCoarsePairedValueUnion r).card := by
  classical
  have hsub := three_mul_card_positiveUpper_le_four_mul_inter_rootCoarse r q.val.1 j k hjk hAcard hB
  rw [reducedCollisionPositiveUpperValueLayer,
    blockedSignatureUpperValueLayer, rootCoarsePairedValueUnion,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  exact hsub

noncomputable def pairedRestorationPositiveUpperOccupancyMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : ℕ :=
  F.sum (fun q ↦ (reducedCollisionPositiveUpperValueLayer q ∩
    pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card)

theorem three_mul_positiveUpperIncidenceMass_le_four_mul_pairedOccupancyMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k}) :
    3 * reducedCollisionPositiveUpperIncidenceMass F ≤
      4 * pairedRestorationPositiveUpperOccupancyMass F r v u j k := by
  classical
  rw [reducedCollisionPositiveUpperIncidenceMass, pairedRestorationPositiveUpperOccupancyMass,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hcoarse := three_mul_card_positiveUpperValue_le_four_mul_inter_rootCoarse hg r q j k hjk hAcard hB
  have hsub := rootCoarsePairedValueUnion_subset_pairedRestoration r v u j k
  have hinter : reducedCollisionPositiveUpperValueLayer q ∩
      rootCoarsePairedValueUnion r ⊆
    reducedCollisionPositiveUpperValueLayer q ∩
      pairedRestorationFanValueUnionWithTailUpperFaces r v u j k :=
    Finset.inter_subset_inter Finset.Subset.rfl hsub
  exact hcoarse.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card hinter))

theorem biUnion_positiveUpper_inter
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (P : Finset G) :
    F.biUnion (fun q ↦ reducedCollisionPositiveUpperValueLayer q ∩ P) =
      reducedCollisionPositiveUpperValueUnionAll F ∩ P := by
  classical
  change F.biUnion (fun q ↦
      reducedCollisionPositiveUpperValueLayer q ∩ P) =
    F.biUnion reducedCollisionPositiveUpperValueLayer ∩ P
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨q, hq, hxq, hxP⟩
    exact ⟨⟨q, hq, hxq⟩, hxP⟩
  · rintro ⟨⟨q, hq, hxq⟩, hxP⟩
    exact ⟨q, hq, hxq, hxP⟩

theorem two_mul_pairedOccupancyMass_sq_le_intersection_mul_adjacentBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    2 * (pairedRestorationPositiveUpperOccupancyMass F r v u j k) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F ∩
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
  classical
  let P := pairedRestorationFanValueUnionWithTailUpperFaces r v u j k
  let L : ReducedSubsetSumCollision g h → Finset G := fun q ↦
    reducedCollisionPositiveUpperValueLayer q ∩ P
  have hcs := square_sum_card_le_union_card_mul_sum_pair_inter F L
  have hpairRestrict :
      (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) ≤
        (F ×ˢ F).sum (fun p ↦
          (reducedCollisionPositiveUpperValueLayer p.1 ∩
            reducedCollisionPositiveUpperValueLayer p.2).card) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.card_le_card
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx'.1).1,
        (Finset.mem_inter.mp hx'.2).1⟩
  have hpairs :=
    two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent
      hg F
  have hpairs' :
      2 * (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) ≤
        F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F :=
    (Nat.mul_le_mul_left 2 hpairRestrict).trans hpairs
  have hUnion : F.biUnion L =
      reducedCollisionPositiveUpperValueUnionAll F ∩ P := by
    simpa [L] using biUnion_positiveUpper_inter F P
  have hMass : F.sum (fun q ↦ (L q).card) =
      pairedRestorationPositiveUpperOccupancyMass F r v u j k := by
    rfl
  change (F.sum fun q ↦ (L q).card) ^ 2 ≤
      (F.biUnion L).card *
        (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) at hcs
  rw [hMass, hUnion] at hcs
  change 2 * (pairedRestorationPositiveUpperOccupancyMass F r v u j k) ^ 2 ≤ _
  calc
    2 * (pairedRestorationPositiveUpperOccupancyMass F r v u j k) ^ 2 ≤
        2 * ((reducedCollisionPositiveUpperValueUnionAll F ∩ P).card *
          (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card)) :=
      Nat.mul_le_mul_left 2 hcs
    _ = (reducedCollisionPositiveUpperValueUnionAll F ∩ P).card *
        (2 * (F ×ˢ F).sum (fun p ↦
          (L p.1 ∩ L p.2).card)) := by ring
    _ ≤ (reducedCollisionPositiveUpperValueUnionAll F ∩ P).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) :=
      Nat.mul_le_mul_left _ hpairs'

theorem nine_mul_sum_weight_le_card_succ_mul_positiveUpperInterPaired
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card)
    (hadjZero : reducedCollisionAdjacentPositiveNestingFaceMass F = 0) :
    9 * F.sum (reducedCollisionWeight (m := m)) ≤
      (F.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll F ∩
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card := by
  classical
  let W := F.sum (reducedCollisionWeight (m := m))
  let S := reducedCollisionPositiveUpperIncidenceMass F
  let T := pairedRestorationPositiveUpperOccupancyMass F r v u j k
  let I := (reducedCollisionPositiveUpperValueUnionAll F ∩
    pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card
  let K := F.card + 1
  have hsupply := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg F hcanonicalCard hsix
  have hthree := three_mul_positiveUpperIncidenceMass_le_four_mul_pairedOccupancyMass hg F r v u j k hjk hAcard hB
  have hsecond := two_mul_pairedOccupancyMass_sq_le_intersection_mul_adjacentBudget hg F r v u j k
  change 8 * W ≤ S at hsupply
  change 3 * S ≤ 4 * T at hthree
  change 2 * T ^ 2 ≤ I *
    (F.card * S + S +
      reducedCollisionAdjacentPositiveNestingFaceMass F) at hsecond
  rw [hadjZero] at hsecond
  change 9 * W ≤ K * I
  by_cases hS : S = 0
  · have hW : W = 0 := by omega
    simp [hW]
  · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
    have hnine : 9 * S ^ 2 ≤ 16 * T ^ 2 := by
      calc
        9 * S ^ 2 = (3 * S) ^ 2 := by ring
        _ ≤ (4 * T) ^ 2 := Nat.pow_le_pow_left hthree 2
        _ = 16 * T ^ 2 := by ring
    have hsixteen : 16 * T ^ 2 ≤ 8 * K * I * S := by
      calc
        16 * T ^ 2 = 8 * (2 * T ^ 2) := by ring
        _ ≤ 8 * (I * (F.card * S + S + 0)) :=
          Nat.mul_le_mul_left 8 hsecond
        _ = 8 * K * I * S := by
          dsimp only [K]
          ring
    have hmul : (9 * S) * S ≤ (8 * K * I) * S := by
      calc
        (9 * S) * S = 9 * S ^ 2 := by ring
        _ ≤ 16 * T ^ 2 := hnine
        _ ≤ 8 * K * I * S := hsixteen
        _ = (8 * K * I) * S := by ring
    have hcancel : 9 * S ≤ 8 * K * I :=
      Nat.le_of_mul_le_mul_right hmul hSpos
    have hscaled : 8 * (9 * W) ≤ 8 * (K * I) := by
      calc
        8 * (9 * W) = 9 * (8 * W) := by ring
        _ ≤ 9 * S := Nat.mul_le_mul_left 9 hsupply
        _ ≤ 8 * K * I := hcancel
        _ = 8 * (K * I) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)

theorem nine_mul_sum_weight_le_card_add_two_mul_positiveUpperInterPaired
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    9 * F.sum (reducedCollisionWeight (m := m)) ≤
      (F.card + 2) *
        (reducedCollisionPositiveUpperValueUnionAll F ∩
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card := by
  classical
  let E := reducedCollisionEvenPositiveCardSubfamily F
  let O := reducedCollisionOddPositiveCardSubfamily F
  let P := pairedRestorationFanValueUnionWithTailUpperFaces r v u j k
  let I := (reducedCollisionPositiveUpperValueUnionAll F ∩ P).card
  have hcardE : ∀ q ∈ E, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hcardO : ∀ q ∈ O, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hsixE : ∀ q ∈ E, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hsixO : ∀ q ∈ O, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hE := nine_mul_sum_weight_le_card_succ_mul_positiveUpperInterPaired hg E r v u j k hjk hAcard hB
    hcardE hsixE (adjacentPositiveNestingFaceMass_evenPositiveCard_eq_zero F)
  have hO := nine_mul_sum_weight_le_card_succ_mul_positiveUpperInterPaired hg O r v u j k hjk hAcard hB
    hcardO hsixO (adjacentPositiveNestingFaceMass_oddPositiveCard_eq_zero F)
  have hEsub : reducedCollisionPositiveUpperValueUnionAll E ∩ P ⊆
      reducedCollisionPositiveUpperValueUnionAll F ∩ P :=
    Finset.inter_subset_inter (evenPositiveCardUpperUnion_subset_all F)
      Finset.Subset.rfl
  have hOsub : reducedCollisionPositiveUpperValueUnionAll O ∩ P ⊆
      reducedCollisionPositiveUpperValueUnionAll F ∩ P :=
    Finset.inter_subset_inter (oddPositiveCardUpperUnion_subset_all F)
      Finset.Subset.rfl
  have hEcard : (reducedCollisionPositiveUpperValueUnionAll E ∩ P).card ≤ I :=
    Finset.card_le_card hEsub
  have hOcard : (reducedCollisionPositiveUpperValueUnionAll O ∩ P).card ≤ I :=
    Finset.card_le_card hOsub
  have hweights := sum_evenPositiveCard_add_sum_oddPositiveCard F
    (reducedCollisionWeight (m := m))
  have hcards := card_evenPositiveCard_add_card_oddPositiveCard F
  change 9 * F.sum (reducedCollisionWeight (m := m)) ≤
    (F.card + 2) * I
  calc
    9 * F.sum (reducedCollisionWeight (m := m)) =
        9 * E.sum (reducedCollisionWeight (m := m)) +
          9 * O.sum (reducedCollisionWeight (m := m)) := by
      rw [← hweights]
      ring
    _ ≤ (E.card + 1) *
          (reducedCollisionPositiveUpperValueUnionAll E ∩ P).card +
        (O.card + 1) *
          (reducedCollisionPositiveUpperValueUnionAll O ∩ P).card :=
      Nat.add_le_add hE hO
    _ ≤ (E.card + 1) * I + (O.card + 1) * I :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (E.card + 1) hEcard)
        (Nat.mul_le_mul_left (O.card + 1) hOcard)
    _ = (F.card + 2) * I := by
      rw [← hcards]
      ring

theorem genuineDominant_two_tail_exists_positiveUpper_pairedOccupancy
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    ∃ j k : Fin n,
    ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ F ∧ u ∈ F ∧ j ≠ k ∧
      9 * F.sum (reducedCollisionWeight (m := n)) ≤
        (F.card + 2) *
          (reducedCollisionPositiveUpperValueUnionAll F ∩
            pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card ∧
      reducedCollisionPositiveUpperValueUnionAll F \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k =
        subsetSumRange g \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k ∧
      2 * (reducedCollisionPositiveUpperValueUnionAll F \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card =
        reducedCollisionWeight (m := n) v +
          reducedCollisionWeight (m := n) u := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let F := criticalCanonicalNonrootCollisions g r
  obtain ⟨j, k, v, u, hselected⟩ :=
    genuineDominant_two_tail_exists_positiveUpper_pairedComplement
      hqodd g hg r hr hres hAcard hBcard
  have hvF := hselected.1
  have huF := hselected.2.1
  have hjk := hselected.2.2.1
  have hB := hselected.2.2.2.1
  have hEq := hselected.2.2.2.2.1
  have hcard := hselected.2.2.2.2.2
  have hmem : ∀ x ∈ F,
      x ∈ criticalCanonicalReducedCollisions g ∧ x ≠ r := by
    intro x hx
    have hx' : x ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hx
    have hx'' := Finset.mem_erase.mp hx'
    exact ⟨hx''.2, hx''.1⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hcanonicalCard : ∀ x ∈ F,
      x.val.1.card ≤ x.val.2.card := by
    intro x hx
    have hxcanonical : x ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using (hmem x hx).1
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hxcanonical)
  have hsix : ∀ x ∈ F, 6 ≤ (reducedCollisionSupport x).card := by
    intro x hx
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard x
        (hmem x hx).1 (hmem x hx).2
  have hinside := nine_mul_sum_weight_le_card_add_two_mul_positiveUpperInterPaired hg F r v u j k hjk
    hAcard hB hcanonicalCard hsix
  exact ⟨j, k, v, u, hvF, huF, hjk, hinside, hEq, hcard⟩

end MinModulus
