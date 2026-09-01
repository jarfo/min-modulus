/-
# Exact coarse root-cell occupancy

Root-trace rigidity puts the singleton positive root coordinate in every
non-root negative tail.  Canonical negative tails also intersect pairwise, so
the non-root negative tail contains at least one of the two root-negative
coordinates.  Collision disjointness therefore prevents a non-root positive
tail from containing both root-negative coordinates.

These two trace restrictions make the coarse estimate from
`G1PositiveUpperPairedOccupancy` exact: every non-root positive upper face has
one quarter of its subsets in the two directional root cells and three
quarters in the root lower/two-upper union.  Any occupancy beyond that exact
three-quarter baseline must lie in the directional restoration-fan slices.
-/
import MinModulus.G1PositiveUpperRootTrace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- If the negative tails meet, collision disjointness prevents the whole
first negative tail from lying in the second positive tail. -/
theorem not_negativeTail_subset_positiveTail_of_negativeTails_inter
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hinter : (r.val.2 ∩ q.val.2).Nonempty) :
    ¬r.val.2 ⊆ q.val.1 := by
  intro hsub
  rcases hinter with ⟨x, hx⟩
  exact Finset.disjoint_left.mp q.property.1
    (hsub (Finset.mem_inter.mp hx).1) (Finset.mem_inter.mp hx).2

omit [DecidableEq G] in
/-- If `T` already forces the live coordinate of a directional root cell and
avoids the other two root coordinates, that cell is exactly one quarter of
the upper face. -/
theorem four_mul_card_positiveUpper_inter_directional_eq_of_mem
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m)) (j : Fin m)
    (hRcard : (reducedCollisionSupport r).card = 3)
    (hjR : j ∈ reducedCollisionSupport r)
    (hjT : j ∈ T)
    (hdisj : Disjoint T ((reducedCollisionSupport r).erase j)) :
    4 * (blockedSignatureUpperSubsetLayer T ∩
        directionalRootPatternSubsetCell r j).card =
      (blockedSignatureUpperSubsetLayer T).card := by
  classical
  let C := (reducedCollisionSupport r).erase j
  have hCcard : C.card = 2 := by
    dsimp only [C]
    rw [Finset.card_erase_of_mem hjR, hRcard]
  have hEq : blockedSignatureUpperSubsetLayer T ∩
      directionalRootPatternSubsetCell r j =
        blockedSignatureUpperSubsetLayer T ∩
          blockedSignatureSubsetLayer C := by
    ext S
    simp only [directionalRootPatternSubsetCell, C,
      Finset.mem_inter, mem_blockedSignatureUpperSubsetLayer_iff]
    constructor
    · rintro ⟨hTS, _hjS, hLower⟩
      exact ⟨hTS, hLower⟩
    · rintro ⟨hTS, hLower⟩
      exact ⟨hTS, (by simpa using hTS hjT), hLower⟩
  have hcardUnion : (T ∪ C).card = T.card + 2 := by
    rw [Finset.card_union_of_disjoint hdisj, hCcard]
  have hle : T.card + 2 ≤ m := by
    rw [← hcardUnion]
    simpa using Finset.card_le_univ (T ∪ C)
  rw [hEq, card_upperSubsetLayer_inter_blockedSubsetLayer T C hdisj,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer, hcardUnion]
  have hexp : m - T.card = (m - (T.card + 2)) + 2 := by omega
  rw [hexp, pow_add]
  ring

omit [DecidableEq G] in
/-- If `T` does not force the live coordinate and avoids the other two root
coordinates, the directional root cell is exactly one eighth of the upper
face. -/
theorem eight_mul_card_positiveUpper_inter_directional_eq_of_not_mem
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m)) (j : Fin m)
    (hRcard : (reducedCollisionSupport r).card = 3)
    (hjR : j ∈ reducedCollisionSupport r)
    (hjT : j ∉ T)
    (hdisj : Disjoint T ((reducedCollisionSupport r).erase j)) :
    8 * (blockedSignatureUpperSubsetLayer T ∩
        directionalRootPatternSubsetCell r j).card =
      (blockedSignatureUpperSubsetLayer T).card := by
  classical
  let C := (reducedCollisionSupport r).erase j
  have hCcard : C.card = 2 := by
    dsimp only [C]
    rw [Finset.card_erase_of_mem hjR, hRcard]
  have hjC : j ∉ C := by simp [C]
  have hTjC : Disjoint (T ∪ {j}) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj, by simpa [Finset.disjoint_singleton] using hjC⟩
  have hTjcard : (T ∪ {j}).card = T.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · simpa [Finset.disjoint_singleton] using hjT
  have hEq : blockedSignatureUpperSubsetLayer T ∩
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
      exact ⟨(fun x hx ↦ hTjS (Finset.mem_union_left _ hx)),
        (by simpa using hTjS (by simp)), hLower⟩
  have hcardUnion : ((T ∪ {j}) ∪ C).card = T.card + 3 := by
    rw [Finset.card_union_of_disjoint hTjC, hTjcard, hCcard]
  have hle : T.card + 3 ≤ m := by
    rw [← hcardUnion]
    simpa using Finset.card_le_univ ((T ∪ {j}) ∪ C)
  rw [hEq,
    card_upperSubsetLayer_inter_blockedSubsetLayer (T ∪ {j}) C hTjC,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer, hcardUnion]
  have hexp : m - T.card = (m - (T.card + 3)) + 3 := by omega
  rw [hexp, pow_add]
  ring

omit [DecidableEq G] in
/-- Under the exact canonical root traces, precisely one quarter of a
positive upper face lies outside the coarse root union. -/
theorem four_mul_card_positiveUpper_sdiff_rootCoarse_eq
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m))
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hTA : Disjoint T r.val.1)
    (hnotB : ¬r.val.2 ⊆ T) :
    4 * (blockedSignatureUpperSubsetLayer T \
        rootCoarsePairedSubsetUnion r).card =
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
  have hmissing : UT \ rootCoarsePairedSubsetUnion r =
      (UT ∩ Dj) ∪ (UT ∩ Dk) := by
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
  have hparts : Disjoint (UT ∩ Dj) (UT ∩ Dk) :=
    hDjDk.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcardMissing : (UT \ rootCoarsePairedSubsetUnion r).card =
      (UT ∩ Dj).card + (UT ∩ Dk).card := by
    rw [hmissing, Finset.card_union_of_disjoint hparts]
  have hjDisj : k ∉ T →
      Disjoint T ((reducedCollisionSupport r).erase j) := by
    intro hkT
    rw [Finset.disjoint_left]
    intro y hyT hyErase
    have hyR := Finset.mem_of_mem_erase hyErase
    rcases Finset.mem_union.mp hyR with hyA | hyB
    · exact Finset.disjoint_left.mp hTA hyT hyA
    · rw [hB] at hyB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
      rcases hyB with rfl | rfl
      · exact (Finset.mem_erase.mp hyErase).1 rfl
      · exact hkT hyT
  have hkDisj : j ∉ T →
      Disjoint T ((reducedCollisionSupport r).erase k) := by
    intro hjT
    rw [Finset.disjoint_left]
    intro y hyT hyErase
    have hyR := Finset.mem_of_mem_erase hyErase
    rcases Finset.mem_union.mp hyR with hyA | hyB
    · exact Finset.disjoint_left.mp hTA hyT hyA
    · rw [hB] at hyB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
      rcases hyB with rfl | rfl
      · exact hjT hyT
      · exact (Finset.mem_erase.mp hyErase).1 rfl
  by_cases hjT : j ∈ T
  · have hkT : k ∉ T := by
      intro hkT
      apply hnotB
      rw [hB]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hjT
      · exact hkT
    have hDj := four_mul_card_positiveUpper_inter_directional_eq_of_mem
      r T j hRcard hjR hjT (hjDisj hkT)
    have hDkEmpty : UT ∩ Dk = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro S hS
      have hjS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hS).1) hjT
      have hLower := (Finset.mem_inter.mp (Finset.mem_inter.mp hS).2).2
      have hjErase : j ∈ (reducedCollisionSupport r).erase k :=
        Finset.mem_erase.mpr ⟨hjk, hjR⟩
      exact (Finset.mem_sdiff.mp
        (Finset.mem_powerset.mp hLower hjS)).2 hjErase
    rw [hcardMissing, hDkEmpty]
    simpa [UT, Dj] using hDj
  · by_cases hkT : k ∈ T
    · have hDk := four_mul_card_positiveUpper_inter_directional_eq_of_mem
        r T k hRcard hkR hkT (hkDisj hjT)
      have hDjEmpty : UT ∩ Dj = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro S hS
        have hkS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
          (Finset.mem_inter.mp hS).1) hkT
        have hLower := (Finset.mem_inter.mp (Finset.mem_inter.mp hS).2).2
        have hkErase : k ∈ (reducedCollisionSupport r).erase j :=
          Finset.mem_erase.mpr ⟨Ne.symm hjk, hkR⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hkS)).2 hkErase
      rw [hcardMissing, hDjEmpty]
      simpa [UT, Dk] using hDk
    · have hDj := eight_mul_card_positiveUpper_inter_directional_eq_of_not_mem
        r T j hRcard hjR hjT (hjDisj hkT)
      have hDk := eight_mul_card_positiveUpper_inter_directional_eq_of_not_mem
        r T k hRcard hkR hkT (hkDisj hjT)
      rw [hcardMissing]
      change 4 * ((UT ∩ Dj).card + (UT ∩ Dk).card) = UT.card
      change 8 * (UT ∩ Dj).card = UT.card at hDj
      change 8 * (UT ∩ Dk).card = UT.card at hDk
      omega

omit [DecidableEq G] in
/-- Equivalently, the coarse root union owns exactly three quarters of the
face. -/
theorem four_mul_card_positiveUpper_inter_rootCoarse_eq_three_mul
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (T : Finset (Fin m))
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hTA : Disjoint T r.val.1)
    (hnotB : ¬r.val.2 ⊆ T) :
    4 * (blockedSignatureUpperSubsetLayer T ∩
        rootCoarsePairedSubsetUnion r).card =
      3 * (blockedSignatureUpperSubsetLayer T).card := by
  have hout := four_mul_card_positiveUpper_sdiff_rootCoarse_eq
    r T j k hjk hAcard hB hTA hnotB
  have hpartition := Finset.card_sdiff_add_card_inter
    (blockedSignatureUpperSubsetLayer T) (rootCoarsePairedSubsetUnion r)
  omega

theorem four_mul_card_positiveUpperValue_inter_rootCoarse_eq_three_mul
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hTA : Disjoint q.val.1 r.val.1)
    (hnotB : ¬r.val.2 ⊆ q.val.1) :
    4 * (reducedCollisionPositiveUpperValueLayer q ∩
        rootCoarsePairedValueUnion r).card =
      3 * (reducedCollisionPositiveUpperValueLayer q).card := by
  classical
  have hsub := four_mul_card_positiveUpper_inter_rootCoarse_eq_three_mul
    r q.val.1 j k hjk hAcard hB hTA hnotB
  rw [reducedCollisionPositiveUpperValueLayer,
    blockedSignatureUpperValueLayer, rootCoarsePairedValueUnion,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  exact hsub

noncomputable def rootCoarsePositiveUpperOccupancyMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r : ReducedSubsetSumCollision g h) : ℕ :=
  F.sum (fun q ↦ (reducedCollisionPositiveUpperValueLayer q ∩
    rootCoarsePairedValueUnion r).card)

theorem four_mul_rootCoarsePositiveUpperOccupancyMass_eq_three_mul_incidence
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (htrace : ∀ q ∈ F,
      Disjoint q.val.1 r.val.1 ∧ ¬r.val.2 ⊆ q.val.1) :
    4 * rootCoarsePositiveUpperOccupancyMass F r =
      3 * reducedCollisionPositiveUpperIncidenceMass F := by
  classical
  rw [rootCoarsePositiveUpperOccupancyMass,
    reducedCollisionPositiveUpperIncidenceMass,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact four_mul_card_positiveUpperValue_inter_rootCoarse_eq_three_mul
    hg r q j k hjk hAcard hB (htrace q hq).1 (htrace q hq).2

/-- Positive-upper incidence in the part of the paired packing beyond the
three coarse root layers.  This is exactly the two directional fan excess. -/
noncomputable def pairedRestorationPositiveUpperDirectionalExcessMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : ℕ :=
  F.sum (fun q ↦ (reducedCollisionPositiveUpperValueLayer q ∩
    (pairedRestorationFanValueUnionWithTailUpperFaces r v u j k \
      rootCoarsePairedValueUnion r)).card)

/-- Paired occupancy is the disjoint sum of its coarse-root baseline and
directional-fan excess. -/
theorem pairedOccupancyMass_eq_rootCoarse_add_directionalExcess
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    pairedRestorationPositiveUpperOccupancyMass F r v u j k =
      rootCoarsePositiveUpperOccupancyMass F r +
        pairedRestorationPositiveUpperDirectionalExcessMass F r v u j k := by
  classical
  rw [pairedRestorationPositiveUpperOccupancyMass,
    rootCoarsePositiveUpperOccupancyMass,
    pairedRestorationPositiveUpperDirectionalExcessMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  let X := reducedCollisionPositiveUpperValueLayer q
  let Q := rootCoarsePairedValueUnion r
  let P := pairedRestorationFanValueUnionWithTailUpperFaces r v u j k
  have hQP : Q ⊆ P := by
    simpa [Q, P] using
      rootCoarsePairedValueUnion_subset_pairedRestoration r v u j k
  have hEq : X ∩ P = (X ∩ Q) ∪ (X ∩ (P \ Q)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxQ : x ∈ Q
      · exact Or.inl ⟨hx.1, hxQ⟩
      · exact Or.inr ⟨hx.1, hx.2, hxQ⟩
    · rintro (⟨hxX, hxQ⟩ | ⟨hxX, hxP, _hxQ⟩)
      · exact ⟨hxX, hQP hxQ⟩
      · exact ⟨hxX, hxP⟩
  have hdisj : Disjoint (X ∩ Q) (X ∩ (P \ Q)) := by
    rw [Finset.disjoint_left]
    intro x hxQ hxE
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxE).2).2
      (Finset.mem_inter.mp hxQ).2
  rw [show (reducedCollisionPositiveUpperValueLayer q ∩ P).card =
      (X ∩ P).card by rfl, hEq, Finset.card_union_of_disjoint hdisj]

/-- Once the canonical root traces hold, paired occupancy differs from the
exact three-quarter baseline only by directional-fan excess. -/
theorem four_mul_pairedOccupancyMass_eq_three_incidence_add_four_directionalExcess
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (htrace : ∀ q ∈ F,
      Disjoint q.val.1 r.val.1 ∧ ¬r.val.2 ⊆ q.val.1) :
    4 * pairedRestorationPositiveUpperOccupancyMass F r v u j k =
      3 * reducedCollisionPositiveUpperIncidenceMass F +
        4 * pairedRestorationPositiveUpperDirectionalExcessMass
          F r v u j k := by
  have hdecomp := pairedOccupancyMass_eq_rootCoarse_add_directionalExcess
    F r v u j k
  have hcoarse :=
    four_mul_rootCoarsePositiveUpperOccupancyMass_eq_three_mul_incidence
      hg F r j k hjk hAcard hB htrace
  omega

section CriticalRootCells

/-- The complete critical non-root family has the exact root traces and exact
three-quarter coarse occupancy. -/
theorem critical_two_tail_nonroot_exact_rootCell_occupancy
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    ∃ j k : Fin n, j ≠ k ∧ r.val.2 = {j, k} ∧
      (∀ u ∈ F, r.val.1 ⊆ u.val.2 ∧
        Disjoint u.val.1 r.val.1 ∧ ¬r.val.2 ⊆ u.val.1) ∧
      4 * rootCoarsePositiveUpperOccupancyMass F r =
        3 * reducedCollisionPositiveUpperIncidenceMass F ∧
      ∀ v u : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        4 * pairedRestorationPositiveUpperOccupancyMass F r v u j k =
          3 * reducedCollisionPositiveUpperIncidenceMass F +
            4 * pairedRestorationPositiveUpperDirectionalExcessMass
              F r v u j k := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  obtain ⟨j, k, hjk, hB⟩ := Finset.card_eq_two.mp hBcard
  have hrootTrace := critical_two_tail_nonroot_rootPositive_trace_and_occupancy
    hqodd g hg r hr hAcard hBcard
  have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have htrace : ∀ u ∈ F, r.val.1 ⊆ u.val.2 ∧
      Disjoint u.val.1 r.val.1 ∧ ¬r.val.2 ⊆ u.val.1 := by
    intro u hu
    have huErase : u ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hu
    have hucritical := (Finset.mem_erase.mp huErase).2
    have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hucritical
    have hinter := canonicalReducedCollision_negative_tails_inter
      g hg hh (half_ne_zero hN hM) r u
        (mem_canonicalReducedCollisions_iff.mp hrcanonical)
        (mem_canonicalReducedCollisions_iff.mp hucanonical)
    exact ⟨(hrootTrace.1 u hu).1, (hrootTrace.1 u hu).2,
      not_negativeTail_subset_positiveTail_of_negativeTails_inter r u hinter⟩
  have htrace' : ∀ u ∈ F,
      Disjoint u.val.1 r.val.1 ∧ ¬r.val.2 ⊆ u.val.1 :=
    fun u hu ↦ ⟨(htrace u hu).2.1, (htrace u hu).2.2⟩
  refine ⟨j, k, hjk, hB, htrace, ?_, ?_⟩
  · exact four_mul_rootCoarsePositiveUpperOccupancyMass_eq_three_mul_incidence
      hg F r j k hjk hAcard hB htrace'
  · intro v u
    exact
      four_mul_pairedOccupancyMass_eq_three_incidence_add_four_directionalExcess
        hg F r v u j k hjk hAcard hB htrace'

end CriticalRootCells

end MinModulus
