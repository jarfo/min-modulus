/-
# Crossing-mass charge from minimal support private collisions

Tail-light private witnesses give distinct reduced half-collisions with large
padding weights.  Canonically orient those shapes.  Private support prevents
two selected vectors from being negatives, so canonical orientation preserves
injectivity.  The dense canonical crossing theorem then charges every ordered
off-diagonal private pair, up to the universal factor two, to the existing
positive/negative crossing mass.
-/
import MinModulus.G1MinimalSupportCollisionCharge
import MinModulus.G1CrossingMass

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Choose the canonical member of the swap pair containing `r`. -/
noncomputable def canonicalizeReducedCollision
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    ReducedSubsetSumCollision g h := by
  classical
  exact if IsCanonicalReducedCollision hh r then r
    else reducedSubsetSumCollisionSwapEquiv hh r

theorem canonicalizeReducedCollision_isCanonical
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h) :
    IsCanonicalReducedCollision hh (canonicalizeReducedCollision hh r) := by
  classical
  by_cases hr : IsCanonicalReducedCollision hh r
  · simp only [canonicalizeReducedCollision, hr, if_true]
  · simpa [canonicalizeReducedCollision, hr] using
      (canonicalReducedCollision_swap_iff_not hh hh0 r).mpr hr

theorem canonicalizeReducedCollision_weight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    reducedCollisionWeight (m := m) (canonicalizeReducedCollision hh r) =
      reducedCollisionWeight (m := m) r := by
  classical
  by_cases hr : IsCanonicalReducedCollision hh r
  · simp [canonicalizeReducedCollision, hr]
  · simp [canonicalizeReducedCollision, hr, reducedCollisionWeight_swap]

/-- Canonicalization separates two shapes provided they are neither equal nor
swaps of one another. -/
theorem canonicalizeReducedCollision_ne_of_ne_of_ne_swap
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrq : r ≠ q)
    (hrswap : r ≠ reducedSubsetSumCollisionSwapEquiv hh q) :
    canonicalizeReducedCollision hh r ≠ canonicalizeReducedCollision hh q := by
  classical
  by_cases hr : IsCanonicalReducedCollision hh r
  · by_cases hq : IsCanonicalReducedCollision hh q
    · simpa [canonicalizeReducedCollision, hr, hq] using hrq
    · simpa [canonicalizeReducedCollision, hr, hq] using hrswap
  · by_cases hq : IsCanonicalReducedCollision hh q
    · simp only [canonicalizeReducedCollision, hr, hq, if_false, if_true]
      intro hswap
      apply hrswap
      calc
        r = reducedSubsetSumCollisionSwapEquiv hh
            (reducedSubsetSumCollisionSwapEquiv hh r) := by rfl
        _ = reducedSubsetSumCollisionSwapEquiv hh q :=
          congrArg (reducedSubsetSumCollisionSwapEquiv hh) hswap
    · simp only [canonicalizeReducedCollision, hr, hq, if_false]
      exact fun heq ↦
        hrq ((reducedSubsetSumCollisionSwapEquiv hh).injective heq)

omit [DecidableEq G] in
/-- No two private witnesses, including the same one twice, are negatives of
one another. -/
theorem minimalSupportPrivateWitness_ne_neg
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b₁ b₂ : {b : Fin (m + 1) // b ∈ B}) :
    minimalSupportPrivateWitness g h hmin b₁ ≠
      -minimalSupportPrivateWitness g h hmin b₂ := by
  intro heq
  have hb := congrFun heq b₁
  have hnz := minimalSupportPrivateWitness_ne_zero g h hmin b₁
  by_cases hval : (b₁ : Fin (m + 1)) = b₂
  · have hbsub : b₁ = b₂ := Subtype.ext hval
    subst b₂
    simp only [Pi.neg_apply] at hb
    omega
  · have hz := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b₂ b₁.property hval
    simp only [Pi.neg_apply, hz, neg_zero] at hb
    exact hnz hb

omit [DecidableEq G] in
/-- Private reduced shapes are never swaps, because swapping negates their
reconstructed coefficient vectors. -/
theorem minimalSupportPrivateReducedCollision_ne_swap
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b₁ b₂ : {b : Fin (m + 1) // b ∈ B}) :
    minimalSupportPrivateReducedCollision g h hmin hallLight b₁ ≠
      reducedSubsetSumCollisionSwapEquiv hh
        (minimalSupportPrivateReducedCollision g h hmin hallLight b₂) := by
  intro heq
  apply minimalSupportPrivateWitness_ne_neg g h hmin b₁ b₂
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
          (reducedSubsetSumCollisionSwapEquiv hh
            (minimalSupportPrivateReducedCollision
              g h hmin hallLight b₂)).val.1
          (reducedSubsetSumCollisionSwapEquiv hh
            (minimalSupportPrivateReducedCollision
              g h hmin hallLight b₂)).val.2 := by rw [heq]
    _ = subsetCollisionCoeffs
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.2
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.1 := by rfl
    _ = -subsetCollisionCoeffs
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.1
          (minimalSupportPrivateReducedCollision
            g h hmin hallLight b₂).val.2 :=
      subsetCollisionCoeffs_swap _ _
    _ = -minimalSupportPrivateWitness g h hmin b₂ := by
      rw [minimalSupportPrivateReducedCollision_coeffs
        g h hmin hallLight b₂]

/-- The canonically oriented private collision at `b`. -/
noncomputable def minimalSupportPrivateCanonicalCollision
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (minimalSupportPrivateReducedCollision g h hmin hallLight b)

theorem minimalSupportPrivateCanonicalCollision_isCanonical
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    IsCanonicalReducedCollision hh
      (minimalSupportPrivateCanonicalCollision
        g h hh hmin hallLight b) :=
  canonicalizeReducedCollision_isCanonical hh hh0 _

theorem minimalSupportPrivateCanonicalCollision_weight
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    reducedCollisionWeight (m := m)
        (minimalSupportPrivateCanonicalCollision
          g h hh hmin hallLight b) =
      reducedCollisionWeight (m := m)
        (minimalSupportPrivateReducedCollision
          g h hmin hallLight b) :=
  canonicalizeReducedCollision_weight hh _

theorem minimalSupportPrivateCanonicalCollision_injective
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    Function.Injective
      (minimalSupportPrivateCanonicalCollision
        g h hh hmin hallLight) := by
  intro b₁ b₂ heq
  by_contra hb
  have hredne : minimalSupportPrivateReducedCollision
      g h hmin hallLight b₁ ≠
      minimalSupportPrivateReducedCollision g h hmin hallLight b₂ :=
    fun hred ↦ hb (minimalSupportPrivateReducedCollision_injective
      g h hmin hallLight hred)
  have hswap := minimalSupportPrivateReducedCollision_ne_swap
    g h hh hmin hallLight b₁ b₂
  exact (canonicalizeReducedCollision_ne_of_ne_of_ne_swap
    hh _ _ hredne hswap) heq

/-- The finite family of canonically oriented private collisions. -/
noncomputable def minimalSupportPrivateCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact B.attach.image
    (minimalSupportPrivateCanonicalCollision g h hh hmin hallLight)

theorem card_minimalSupportPrivateCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    (minimalSupportPrivateCanonicalCollisions
      g h hh B hmin hallLight).card = B.card := by
  classical
  rw [minimalSupportPrivateCanonicalCollisions,
    Finset.card_image_of_injective _
      (minimalSupportPrivateCanonicalCollision_injective
        g h hh hmin hallLight)]
  simp

theorem minimalSupportPrivateCanonicalCollisions_subset
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    minimalSupportPrivateCanonicalCollisions g h hh B hmin hallLight ⊆
      canonicalReducedCollisions (g := g) hh := by
  classical
  intro r hr
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
  exact mem_canonicalReducedCollisions_iff.mpr
    (minimalSupportPrivateCanonicalCollision_isCanonical
      g h hh hh0 hmin hallLight b)

/-- Each canonically oriented private shape retains the same exponential
padding-weight lower bound. -/
theorem pow_card_sub_two_le_minimalSupportPrivateCanonicalCollision_weight
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateCanonicalCollision
        g h hh hmin hallLight b) := by
  rw [minimalSupportPrivateCanonicalCollision_weight]
  exact pow_card_sub_two_le_minimalSupportPrivateReducedCollision_weight
    g h hmin hallLight b

/-- Quadratic-exponential crossing charge from the minimal deletion family.
Every ordered distinct private pair contributes at least
`2^(B.card-2)^2`; crossing density captures at least half of their total
product weight. -/
theorem minimalSupportPrivate_crossingCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    B.card * (B.card - 1) *
        (2 ^ (B.card - 2) * 2 ^ (B.card - 2)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let F := minimalSupportPrivateCanonicalCollisions
    g h hh B hmin hallLight
  let w := 2 ^ (B.card - 2)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hFcard : F.card = B.card :=
    card_minimalSupportPrivateCanonicalCollisions
      g h hh B hmin hallLight
  have hFsub : F ⊆ canonicalReducedCollisions (g := g) hh :=
    minimalSupportPrivateCanonicalCollisions_subset
      g h hh hh0 B hmin hallLight
  have hweight : ∀ r ∈ F, w ≤ reducedCollisionWeight (m := m) r := by
    intro r hr
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
    exact pow_card_sub_two_le_minimalSupportPrivateCanonicalCollision_weight
      g h hh hmin hallLight b
  have hoffsub : F.offDiag ⊆
      canonicalDistinctReducedCollisionPairs (g := g) hh := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    exact mem_canonicalDistinctReducedCollisionPairs_iff.mpr
      ⟨hFsub hp'.1, hFsub hp'.2.1, hp'.2.2⟩
  have hpairs : F.offDiag.card = B.card * (B.card - 1) := by
    rw [Finset.offDiag_card, hFcard, Nat.mul_sub_left_distrib]
    simp
  calc
    B.card * (B.card - 1) * (w * w) =
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
