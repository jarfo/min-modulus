/-
# Padding charge from minimal support private witnesses

In the branch with no tail-heavy half witness, every private witness of a
minimal support transversal is a reduced subset-sum collision.  Different
deleted coordinates give different reduced shapes.  Moreover, the witness
at `b` vanishes on every other deleted coordinate, leaving those coordinates
available as common padding.  This gives an exponential overlap charge for
the deletion cardinality.
-/
import MinModulus.G1MinimalSupportEscapeIncidence
import MinModulus.G1QuarterLayerCount

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The reduced collision encoded by the private witness at one coordinate
of a minimal support transversal, in the all-tail-light branch. -/
noncomputable def minimalSupportPrivateReducedCollision
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    ReducedSubsetSumCollision g h :=
  reducedCollisionOfTailLightWitness g
    (minimalSupportPrivateWitness_isWitness g h hmin b)
    (hallLight _ (minimalSupportPrivateWitness_isWitness g h hmin b))

omit [DecidableEq G] in
/-- The selected reduced shape reconstructs the private coefficient vector. -/
theorem minimalSupportPrivateReducedCollision_coeffs
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    subsetCollisionCoeffs
        (minimalSupportPrivateReducedCollision
          g h hmin hallLight b).val.1
        (minimalSupportPrivateReducedCollision
          g h hmin hallLight b).val.2 =
      minimalSupportPrivateWitness g h hmin b := by
  exact reducedCollisionOfTailLightWitness_coeffs g
    (minimalSupportPrivateWitness_isWitness g h hmin b)
    (hallLight _ (minimalSupportPrivateWitness_isWitness g h hmin b))

omit [DecidableEq G] in
/-- Private reduced collisions are injectively indexed by the deleted
coordinates. -/
theorem minimalSupportPrivateReducedCollision_injective
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    Function.Injective
      (minimalSupportPrivateReducedCollision g h hmin hallLight) := by
  intro b₁ b₂ heq
  apply minimalSupportPrivateWitness_injective g h hmin
  calc
    minimalSupportPrivateWitness g h hmin b₁ =
        subsetCollisionCoeffs
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₁).val.1
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₁).val.2 :=
      (minimalSupportPrivateReducedCollision_coeffs
        g h hmin hallLight b₁).symm
    _ = subsetCollisionCoeffs
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.1
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.2 := by rw [heq]
    _ = minimalSupportPrivateWitness g h hmin b₂ :=
      minimalSupportPrivateReducedCollision_coeffs
        g h hmin hallLight b₂

omit [DecidableEq G] in
/-- Apart from the private coordinate itself and the possible distinguished
anchor, every deleted coordinate is absent from the reduced tail support.
Consequently the padding depth is at least `B.card-2`. -/
theorem minimalSupportPrivateReducedCollision_paddingDepth
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    B.card - 2 ≤ m -
      ((minimalSupportPrivateReducedCollision
        g h hmin hallLight b).val.1 ∪
       (minimalSupportPrivateReducedCollision
        g h hmin hallLight b).val.2).card := by
  classical
  let c := minimalSupportPrivateWitness g h hmin b
  let r := minimalSupportPrivateReducedCollision g h hmin hallLight b
  let R : Finset (Fin m) := r.val.1 ∪ r.val.2
  have hdisj : Disjoint (R.image Fin.succ) (B.erase b) := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    obtain ⟨j, hjR, rfl⟩ := Finset.mem_image.mp hxR
    have hjR' : j ∈ witnessPositiveTail c ∪ witnessNegativeTail c := by
      simpa [R, r, minimalSupportPrivateReducedCollision,
        reducedCollisionOfTailLightWitness, c] using hjR
    have hcne : c j.succ ≠ 0 := by
      rcases Finset.mem_union.mp hjR' with hj | hj
      · have hj' : c j.succ = 1 := by
          simpa [witnessPositiveTail] using hj
        omega
      · have hj' : c j.succ = -1 := by
          simpa [witnessNegativeTail] using hj
        omega
    have hxB' := Finset.mem_erase.mp hxB
    have hczero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b hxB'.2 hxB'.1
    exact hcne hczero
  have himage : (R.image Fin.succ).card = R.card :=
    Finset.card_image_of_injective R (Fin.succ_injective m)
  have hdim : (R.image Fin.succ).card + (B.erase b).card ≤ m + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hle := Finset.card_le_card
      (Finset.subset_univ (R.image Fin.succ ∪ B.erase b))
    simpa using hle
  have herase : (B.erase b).card + 1 = B.card :=
    Finset.card_erase_add_one b.property
  have hRle : R.card ≤ m := by
    have hle := Finset.card_le_card (Finset.subset_univ R)
    simpa [R] using hle
  change B.card - 2 ≤ m - R.card
  rw [himage] at hdim
  omega

omit [DecidableEq G] in
/-- Each private reduced collision carries at least
`2^(B.card-2)` exact padding multiplicity. -/
theorem pow_card_sub_two_le_minimalSupportPrivateReducedCollision_weight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateReducedCollision g h hmin hallLight b) := by
  unfold reducedCollisionWeight
  exact Nat.pow_le_pow_right (by norm_num)
    (minimalSupportPrivateReducedCollision_paddingDepth
      g h hmin hallLight b)

/-- Exponential dimension-loss charge: in the all-tail-light branch, the
private reduced collisions contribute at least
`B.card * 2^(B.card-2)` distinct padded collisions to the half-translate
overlap. -/
theorem minimalSupportPrivateCollision_charge_le_overlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    B.card * 2 ^ (B.card - 2) ≤
      ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  classical
  let f := minimalSupportPrivateReducedCollision g h hmin hallLight
  have hfinj : Function.Injective f :=
    minimalSupportPrivateReducedCollision_injective
      g h hmin hallLight
  calc
    B.card * 2 ^ (B.card - 2) =
        ∑ _b ∈ B.attach, 2 ^ (B.card - 2) := by simp
    _ ≤ ∑ b ∈ B.attach, reducedCollisionWeight (m := m) (f b) := by
      apply Finset.sum_le_sum
      intro b _hb
      exact pow_card_sub_two_le_minimalSupportPrivateReducedCollision_weight
        g h hmin hallLight b
    _ = (B.attach.image f).sum
        (reducedCollisionWeight (m := m)) := by
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

omit [DecidableEq G] in
/-- Under global tail-lightness, every coefficient-floor escape occurs at
the distinguished anchor or at an exact omission of the protected quarter
witness. -/
theorem minimalSupportPrivateEscape_eq_anchor_or_mem_exactOmissions
    (g : Fin (m + 1) → G) {h t : G}
    {q : Fin (m + 1) → ℤ} (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) (i : Fin (m + 1))
    (hi : (b, i) ∈ minimalSupportPrivateEscapePairs g h q hmin) :
    i = 0 ∨ i ∈ Q := by
  cases i using Fin.cases with
  | zero => exact Or.inl rfl
  | succ j =>
      right
      have hescape := (mem_minimalSupportPrivateEscapePairs_iff
        g h q hmin b j.succ).1 hi
      have hceil := hallLight
        (minimalSupportPrivateWitness g h hmin b)
        (minimalSupportPrivateWitness_isWitness g h hmin b) j
      have hfloor := hq.2.1 j.succ
      have hqneg : q j.succ = -1 := by omega
      exact (hQ j.succ).1 hqneg

end MinModulus
