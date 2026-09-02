/-
# Extra padding from a zero escape signature

A non-anchor exact omission of the protected quarter witness lies outside the
minimal deletion set.  If a concentrated private class has coefficient zero
there, that additional external coordinate is absent from every associated
reduced collision.  It therefore contributes one more common-padding bit
than the general minimal-support estimate.  This file charges the resulting
factor-two weight gain to overlap and its factor-four pairwise gain to the
canonical crossing mass.
-/
import MinModulus.G1MinimalSupportEscapeSignature

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- An exact omission of the protected quarter witness cannot belong to a
deletion set on which that witness is zero. -/
theorem exactOmission_not_mem_minimalSupportDeletion
    {q : Fin (m + 1) → ℤ} {Q B : Finset (Fin (m + 1))}
    (hQ : ExactOmissions q Q) (hqzero : ∀ b ∈ B, q b = 0)
    {z : Fin (m + 1)} (hzQ : z ∈ Q) : z ∉ B := by
  intro hzB
  have hzneg : q z = -1 := (hQ z).2 hzQ
  have hzero : q z = 0 := hqzero z hzB
  omega

omit [DecidableEq G] in
/-- A `+1` signature at a non-anchor escape is a common positive-tail
coordinate of every raw private reduced collision in the class. -/
theorem minimalSupportPrivateOneSignature_mem_positiveTail
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hz0 : z ≠ 0)
    (b : {b : Fin (m + 1) // b ∈ B})
    (hb : b ∈ minimalSupportPrivateEscapeSignatureFiber
      g hg ht hq B hmin hqzero z 1) :
    ∃ j : Fin m, z = j.succ ∧
      j ∈ (minimalSupportPrivateReducedCollision
        g h hmin hallLight b).val.1 := by
  have hcoeff := (mem_minimalSupportPrivateEscapeSignatureFiber_iff
    g hg ht hq B hmin hqzero z 1 b).1 hb |>.2
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hz0
  refine ⟨j, rfl, ?_⟩
  simpa [minimalSupportPrivateReducedCollision,
    reducedCollisionOfTailLightWitness, witnessPositiveTail] using hcoeff

omit [DecidableEq G] in
/-- A zero signature at a non-anchor exact omission improves the private
collision's padding depth from `B.card-2` to `B.card-1`: all other deleted
coordinates and this additional external omission are absent from its tail
support. -/
theorem minimalSupportPrivateZeroSignature_paddingDepth
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0)
    (b : {b : Fin (m + 1) // b ∈ B})
    (hb : b ∈ minimalSupportPrivateEscapeSignatureFiber
      g hg ht hq B hmin hqzero z 0) :
    B.card - 1 ≤ m -
      ((minimalSupportPrivateReducedCollision
        g h hmin hallLight b).val.1 ∪
       (minimalSupportPrivateReducedCollision
        g h hmin hallLight b).val.2).card := by
  classical
  let c := minimalSupportPrivateWitness g h hmin b
  let r := minimalSupportPrivateReducedCollision g h hmin hallLight b
  let R : Finset (Fin m) := r.val.1 ∪ r.val.2
  have hzB : z ∉ B :=
    exactOmission_not_mem_minimalSupportDeletion hQ hqzero hzQ
  have hczero : c z = 0 :=
    (mem_minimalSupportPrivateEscapeSignatureFiber_iff
      g hg ht hq B hmin hqzero z 0 b).1 hb |>.2
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hz0
  have hjR : j ∉ R := by
    intro hj
    change j ∈ witnessPositiveTail c ∪ witnessNegativeTail c at hj
    rcases Finset.mem_union.mp hj with hj | hj
    · have hjone : c j.succ = 1 := by
        simpa [witnessPositiveTail] using hj
      omega
    · have hjneg : c j.succ = -1 := by
        simpa [witnessNegativeTail] using hj
      omega
  let D : Finset (Fin (m + 1)) := insert j.succ (B.erase b)
  have hdisj : Disjoint (R.image Fin.succ) D := by
    rw [Finset.disjoint_left]
    intro x hxR hxD
    obtain ⟨k, hkR, rfl⟩ := Finset.mem_image.mp hxR
    rcases Finset.mem_insert.mp hxD with hkz | hkB
    · have hkj : k = j := Fin.succ_injective m hkz
      subst k
      exact hjR hkR
    · have hkB' := Finset.mem_erase.mp hkB
      have hcne : c k.succ ≠ 0 := by
        change k ∈ witnessPositiveTail c ∪ witnessNegativeTail c at hkR
        rcases Finset.mem_union.mp hkR with hk | hk
        · have hkone : c k.succ = 1 := by
            simpa [witnessPositiveTail] using hk
          omega
        · have hkneg : c k.succ = -1 := by
            simpa [witnessNegativeTail] using hk
          omega
      have hzero := minimalSupportPrivateWitness_eq_zero_of_ne
        g h hmin b hkB'.2 hkB'.1
      exact hcne hzero
  have hjErase : j.succ ∉ B.erase b := by
    intro hj
    exact hzB (Finset.mem_of_mem_erase hj)
  have hDcard : D.card = B.card := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem hjErase,
      Finset.card_erase_add_one b.property]
  have himage : (R.image Fin.succ).card = R.card :=
    Finset.card_image_of_injective R (Fin.succ_injective m)
  have hdim : (R.image Fin.succ).card + D.card ≤ m + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hle := Finset.card_le_card
      (Finset.subset_univ (R.image Fin.succ ∪ D))
    simpa using hle
  have hRle : R.card ≤ m := by
    have hle := Finset.card_le_card (Finset.subset_univ R)
    simpa [R] using hle
  change B.card - 1 ≤ m - R.card
  rw [himage, hDcard] at hdim
  omega

omit [DecidableEq G] in
/-- The zero-signature padding-depth gain gives weight at least
`2^(B.card-1)` for every raw private collision in the class. -/
theorem pow_card_sub_one_le_minimalSupportPrivateZeroSignature_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0)
    (b : {b : Fin (m + 1) // b ∈ B})
    (hb : b ∈ minimalSupportPrivateEscapeSignatureFiber
      g hg ht hq B hmin hqzero z 0) :
    2 ^ (B.card - 1) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateReducedCollision g h hmin hallLight b) := by
  unfold reducedCollisionWeight
  exact Nat.pow_le_pow_right (by norm_num)
    (minimalSupportPrivateZeroSignature_paddingDepth
      g hg ht hq hQ hmin hqzero hallLight z hzQ hz0 b hb)

/-- The zero-signature class alone contributes its enhanced exponential
weight to the translated subset-sum overlap. -/
theorem minimalSupportPrivateZeroSignature_charge_le_overlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0) :
    (minimalSupportPrivateEscapeSignatureFiber
        g hg ht hq B hmin hqzero z 0).card * 2 ^ (B.card - 1) ≤
      ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  classical
  let S := minimalSupportPrivateEscapeSignatureFiber
    g hg ht hq B hmin hqzero z 0
  let f := minimalSupportPrivateReducedCollision g h hmin hallLight
  have hfinj : Function.Injective f :=
    minimalSupportPrivateReducedCollision_injective g h hmin hallLight
  calc
    S.card * 2 ^ (B.card - 1) =
        ∑ _b ∈ S, 2 ^ (B.card - 1) := by simp
    _ ≤ ∑ b ∈ S, reducedCollisionWeight (m := m) (f b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_card_sub_one_le_minimalSupportPrivateZeroSignature_weight
        g hg ht hq hQ hmin hqzero hallLight z hzQ hz0 b hb
    _ = (S.image f).sum (reducedCollisionWeight (m := m)) := by
      symm
      apply Finset.sum_image
      intro b₁ _hb₁ b₂ _hb₂ heq
      exact hfinj heq
    _ ≤ ∑ r : ReducedSubsetSumCollision g h,
        reducedCollisionWeight (m := m) r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
      rw [card_subsetSumOverlap_eq_sum_reduced_weights g hg h]
      rfl

/-- Canonical orientation preserves the enhanced zero-signature weight. -/
theorem pow_card_sub_one_le_minimalSupportPrivateZeroSignatureCanonical_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} (hh : h + h = 0)
    {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0)
    (b : {b : Fin (m + 1) // b ∈ B})
    (hb : b ∈ minimalSupportPrivateEscapeSignatureFiber
      g hg ht hq B hmin hqzero z 0) :
    2 ^ (B.card - 1) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateCanonicalCollision
        g h hh hmin hallLight b) := by
  rw [minimalSupportPrivateCanonicalCollision_weight]
  exact pow_card_sub_one_le_minimalSupportPrivateZeroSignature_weight
    g hg ht hq hQ hmin hqzero hallLight z hzQ hz0 b hb

/-- Pairwise crossing density upgrades the extra zero-signature padding bit
to a factor-four improvement in the class's quadratic crossing charge. -/
theorem minimalSupportPrivateZeroSignature_crossingCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0) :
    let k := (minimalSupportPrivateEscapeSignatureFiber
      g hg ht hq B hmin hqzero z 0).card
    k * (k - 1) *
        (2 ^ (B.card - 1) * 2 ^ (B.card - 1)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let S := minimalSupportPrivateEscapeSignatureFiber
    g hg ht hq B hmin hqzero z 0
  let f := minimalSupportPrivateCanonicalCollision
    g h hh hmin hallLight
  let F := S.image f
  let w := 2 ^ (B.card - 1)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hfinj : Function.Injective f :=
    minimalSupportPrivateCanonicalCollision_injective
      g h hh hmin hallLight
  have hFcard : F.card = S.card := by
    exact Finset.card_image_of_injective S hfinj
  have hFsub : F ⊆ canonicalReducedCollisions (g := g) hh := by
    intro r hr
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
    exact mem_canonicalReducedCollisions_iff.mpr
      (minimalSupportPrivateCanonicalCollision_isCanonical
        g h hh hh0 hmin hallLight b)
  have hweight : ∀ r ∈ F, w ≤ reducedCollisionWeight (m := m) r := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    exact pow_card_sub_one_le_minimalSupportPrivateZeroSignatureCanonical_weight
      g hg hh ht hq hQ hmin hqzero hallLight z hzQ hz0 b hb
  have hoffsub : F.offDiag ⊆
      canonicalDistinctReducedCollisionPairs (g := g) hh := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    exact mem_canonicalDistinctReducedCollisionPairs_iff.mpr
      ⟨hFsub hp'.1, hFsub hp'.2.1, hp'.2.2⟩
  have hpairs : F.offDiag.card = S.card * (S.card - 1) := by
    rw [Finset.offDiag_card, hFcard, Nat.mul_sub_left_distrib]
    simp
  dsimp only
  calc
    S.card * (S.card - 1) * (w * w) =
        ∑ _p ∈ F.offDiag, w * w := by simp [hpairs]
    _ ≤ F.offDiag.sum pairWeight := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.mul_le_mul (hweight p.1 (Finset.mem_offDiag.mp hp).1)
        (hweight p.2 (Finset.mem_offDiag.mp hp).2.1)
    _ ≤ (canonicalDistinctReducedCollisionPairs (g := g) hh).sum
        pairWeight := Finset.sum_le_sum_of_subset hoffsub
    _ ≤ 2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
        pairWeight :=
      sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights
        g hg hh hh0

end MinModulus
