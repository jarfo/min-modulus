/-
# Crossing charge for selected tail-light private owners

The private padding mechanism is local not only to one omission fiber, but to
an arbitrary selected set of deletion owners.  If the selected private
witnesses are tail-light, they give distinct canonical collisions of weight
at least `2^(|B|-2)`.  Thus any two selected owners force critical large
crossing at the usual depth.

Selecting precisely the tail-light owners gives the structural consequence
needed in the private-heavy branch: under critical small crossing, at most one
private owner is tail-light, so all but at most one deletion vertices carry a
tail-heavy private witness.
-/
import MinModulus.G1PrivateHeavyOmissionVertexCrossingCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Tail-lightness restricted to an arbitrary selected finset of private
owners. -/
def MinimalSupportSelectedPrivateWitnessesTailLight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) : Prop :=
  ∀ b : ↥B, b ∈ S →
    ∀ k : Fin m, minimalSupportPrivateWitness g h hmin b k.succ ≤ 1

/-- Reduced collision supplied by one selected tail-light private owner. -/
noncomputable def minimalSupportSelectedPrivateReducedCollision
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) : ReducedSubsetSumCollision g h :=
  reducedCollisionOfTailLightWitness g
    (minimalSupportPrivateWitness_isWitness g h hmin b.val)
    (hlight b.val b.property)

omit [DecidableEq G] in
theorem minimalSupportSelectedPrivateReducedCollision_coeffs
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) :
    subsetCollisionCoeffs
        (minimalSupportSelectedPrivateReducedCollision
          g h hmin S hlight b).val.1
        (minimalSupportSelectedPrivateReducedCollision
          g h hmin S hlight b).val.2 =
      minimalSupportPrivateWitness g h hmin b.val :=
  reducedCollisionOfTailLightWitness_coeffs g
    (minimalSupportPrivateWitness_isWitness g h hmin b.val)
    (hlight b.val b.property)

/-- Canonical orientation of one selected private collision. -/
noncomputable def minimalSupportSelectedPrivateCanonicalCollision
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) : ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (minimalSupportSelectedPrivateReducedCollision
      g h hmin S hlight b)

theorem minimalSupportSelectedPrivateCanonicalCollision_isCanonical
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) :
    IsCanonicalReducedCollision hh
      (minimalSupportSelectedPrivateCanonicalCollision
        g h hh hmin S hlight b) :=
  canonicalizeReducedCollision_isCanonical hh hh0 _

/-- Distinct selected owners remain distinct after reduction and canonical
orientation. -/
theorem minimalSupportSelectedPrivateCanonicalCollision_injective
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S) :
    Function.Injective
      (minimalSupportSelectedPrivateCanonicalCollision
        g h hh hmin S hlight) := by
  intro b u hcan
  by_contra hbu
  let rb := minimalSupportSelectedPrivateReducedCollision
    g h hmin S hlight b
  let ru := minimalSupportSelectedPrivateReducedCollision
    g h hmin S hlight u
  have hrawNe : rb ≠ ru := by
    intro hraw
    apply hbu
    apply Subtype.ext
    apply minimalSupportPrivateWitness_injective g h hmin
    calc
      minimalSupportPrivateWitness g h hmin b.val =
          subsetCollisionCoeffs rb.val.1 rb.val.2 :=
        (minimalSupportSelectedPrivateReducedCollision_coeffs
          g h hmin S hlight b).symm
      _ = subsetCollisionCoeffs ru.val.1 ru.val.2 := by rw [hraw]
      _ = minimalSupportPrivateWitness g h hmin u.val :=
        minimalSupportSelectedPrivateReducedCollision_coeffs
          g h hmin S hlight u
  have hrawSwap : rb ≠ reducedSubsetSumCollisionSwapEquiv hh ru := by
    intro hswap
    apply minimalSupportPrivateWitness_ne_neg g h hmin b.val u.val
    calc
      minimalSupportPrivateWitness g h hmin b.val =
          subsetCollisionCoeffs rb.val.1 rb.val.2 :=
        (minimalSupportSelectedPrivateReducedCollision_coeffs
          g h hmin S hlight b).symm
      _ = subsetCollisionCoeffs
          (reducedSubsetSumCollisionSwapEquiv hh ru).val.1
          (reducedSubsetSumCollisionSwapEquiv hh ru).val.2 := by rw [hswap]
      _ = subsetCollisionCoeffs ru.val.2 ru.val.1 := by rfl
      _ = -subsetCollisionCoeffs ru.val.1 ru.val.2 :=
        subsetCollisionCoeffs_swap _ _
      _ = -minimalSupportPrivateWitness g h hmin u.val := by
        rw [minimalSupportSelectedPrivateReducedCollision_coeffs
          g h hmin S hlight u]
  exact (canonicalizeReducedCollision_ne_of_ne_of_ne_swap
    hh rb ru hrawNe hrawSwap) hcan

omit [DecidableEq G] in
/-- The padding depth of a selected private collision depends on the whole
deletion set `B`, not on the size of the selected subset. -/
theorem minimalSupportSelectedPrivateReducedCollision_paddingDepth
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) :
    B.card - 2 ≤ m -
      ((minimalSupportSelectedPrivateReducedCollision
          g h hmin S hlight b).val.1 ∪
       (minimalSupportSelectedPrivateReducedCollision
          g h hmin S hlight b).val.2).card := by
  classical
  let c := minimalSupportPrivateWitness g h hmin b.val
  let r := minimalSupportSelectedPrivateReducedCollision
    g h hmin S hlight b
  let R : Finset (Fin m) := r.val.1 ∪ r.val.2
  have hdisj : Disjoint (R.image Fin.succ) (B.erase b.val) := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    obtain ⟨j, hjR, rfl⟩ := Finset.mem_image.mp hxR
    have hjR' : j ∈ witnessPositiveTail c ∪ witnessNegativeTail c := by
      simpa [R, r, minimalSupportSelectedPrivateReducedCollision,
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
      g h hmin b.val hxB'.2 hxB'.1
    exact hcne hczero
  have himage : (R.image Fin.succ).card = R.card :=
    Finset.card_image_of_injective R (Fin.succ_injective m)
  have hdim : (R.image Fin.succ).card + (B.erase b.val).card ≤ m + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hle := Finset.card_le_card
      (Finset.subset_univ (R.image Fin.succ ∪ B.erase b.val))
    simpa using hle
  have herase : (B.erase b.val).card + 1 = B.card :=
    Finset.card_erase_add_one b.val.property
  have hRle : R.card ≤ m := by
    have hle := Finset.card_le_card (Finset.subset_univ R)
    simpa [R] using hle
  change B.card - 2 ≤ m - R.card
  rw [himage] at hdim
  omega

/-- Canonical selected collisions retain weight `2^(|B|-2)`. -/
theorem pow_card_sub_two_le_minimalSupportSelectedPrivateCanonicalCollision_weight
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S)
    (b : ↥S) :
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
      (minimalSupportSelectedPrivateCanonicalCollision
        g h hh hmin S hlight b) := by
  calc
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
        (minimalSupportSelectedPrivateReducedCollision
          g h hmin S hlight b) := by
      unfold reducedCollisionWeight
      exact Nat.pow_le_pow_right (by norm_num)
        (minimalSupportSelectedPrivateReducedCollision_paddingDepth
          g h hmin S hlight b)
    _ = reducedCollisionWeight (m := m)
        (minimalSupportSelectedPrivateCanonicalCollision
          g h hh hmin S hlight b) :=
      (canonicalizeReducedCollision_weight hh _).symm

/-- Canonical collisions selected by `S`. -/
noncomputable def minimalSupportSelectedPrivateCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S) : Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact S.attach.image
    (minimalSupportSelectedPrivateCanonicalCollision
      g h hh hmin S hlight)

theorem card_minimalSupportSelectedPrivateCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S) :
    (minimalSupportSelectedPrivateCanonicalCollisions
      g h hh B hmin S hlight).card = S.card := by
  classical
  rw [minimalSupportSelectedPrivateCanonicalCollisions,
    Finset.card_image_of_injective _
      (minimalSupportSelectedPrivateCanonicalCollision_injective
        g h hh hmin S hlight)]
  simp

theorem minimalSupportSelectedPrivateCanonicalCollisions_subset
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S) :
    minimalSupportSelectedPrivateCanonicalCollisions
        g h hh B hmin S hlight ⊆
      canonicalReducedCollisions (g := g) hh := by
  classical
  intro r hr
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
  exact mem_canonicalReducedCollisions_iff.mpr
    (minimalSupportSelectedPrivateCanonicalCollision_isCanonical
      g h hh hh0 hmin S hlight b)

/-- Crossing charge from an arbitrary selected tail-light private family. -/
theorem minimalSupportSelectedPrivate_crossingCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S) :
    S.card * (S.card - 1) *
        (2 ^ (B.card - 2) * 2 ^ (B.card - 2)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let F := minimalSupportSelectedPrivateCanonicalCollisions
    g h hh B hmin S hlight
  let w := 2 ^ (B.card - 2)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hFcard : F.card = S.card :=
    card_minimalSupportSelectedPrivateCanonicalCollisions
      g h hh B hmin S hlight
  have hFsub : F ⊆ canonicalReducedCollisions (g := g) hh :=
    minimalSupportSelectedPrivateCanonicalCollisions_subset
      g h hh hh0 B hmin S hlight
  have hweight : ∀ r ∈ F, w ≤ reducedCollisionWeight (m := m) r := by
    intro r hr
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
    exact
      pow_card_sub_two_le_minimalSupportSelectedPrivateCanonicalCollision_weight
        g h hh hmin S hlight b
  have hoffsub : F.offDiag ⊆
      canonicalDistinctReducedCollisionPairs (g := g) hh := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    exact mem_canonicalDistinctReducedCollisionPairs_iff.mpr
      ⟨hFsub hp'.1, hFsub hp'.2.1, hp'.2.2⟩
  have hpairs : F.offDiag.card = S.card * (S.card - 1) := by
    rw [Finset.offDiag_card, hFcard, Nat.mul_sub_left_distrib]
    simp
  change S.card * (S.card - 1) * (w * w) ≤
    2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
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

/-- Critical specialization of the selected private charge. -/
theorem critical_minimalSupportSelectedPrivate_crossingCharge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin S) :
    S.card * (S.card - 1) *
        (2 ^ (B.card - 2) * 2 ^ (B.card - 2)) ≤
      2 * criticalCanonicalCrossMass g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  simpa [criticalCanonicalCrossMass,
    criticalCanonicalPositiveNegativeCrossPairs] using
    (minimalSupportSelectedPrivate_crossingCharge
      g hg (half_add_half hN) (half_ne_zero hN hM) hmin S hlight)

/-- Two selected tail-light private owners force critical large crossing at
the standard deletion-depth cutoff. -/
theorem critical_largeCross_of_two_selectedPrivateTailLight
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (S : Finset ↥B)
    (hlight : MinimalSupportSelectedPrivateWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin S)
    (hS : 2 ≤ S.card)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  let d := min (s + 1) (Nat.log 2 (n + 1)) - 1
  let L := S.card * (S.card - 1) *
    (2 ^ (B.card - 2) * 2 ^ (B.card - 2))
  have hnum : criticalHalfGap n s * criticalHalfGap n s ≤ 2 * L := by
    simpa [criticalHalfGap, d, L] using
      (pow_add_one_square_le_two_mul_twoVertexPrivateCrossCharge
        (d := d) (b := B.card) (v := S.card)
        (by simpa [d] using hB) hS)
  have hcharge : L ≤ 2 * criticalCanonicalCrossMass g := by
    simpa [L] using
      (critical_minimalSupportSelectedPrivate_crossingCharge
        hq g hg hmin S hlight)
  have htwice : 2 * L ≤ 4 * criticalCanonicalCrossMass g := by
    have := Nat.mul_le_mul_left 2 hcharge
    omega
  exact hnum.trans htwice

/-- Private owners whose selected witness is tail-light. -/
noncomputable def minimalSupportPrivateTailLightVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    ∀ k : Fin m, minimalSupportPrivateWitness g h hmin b k.succ ≤ 1)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateTailLightVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (b : ↥B) :
    b ∈ minimalSupportPrivateTailLightVertices g h hmin ↔
      ∀ k : Fin m,
        minimalSupportPrivateWitness g h hmin b k.succ ≤ 1 := by
  classical
  simp [minimalSupportPrivateTailLightVertices]

/-- Private owners whose selected witness has a tail coefficient at least
two. -/
noncomputable def minimalSupportPrivateTailHeavyVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    ∃ k : Fin m, 2 ≤ minimalSupportPrivateWitness g h hmin b k.succ)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateTailHeavyVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (b : ↥B) :
    b ∈ minimalSupportPrivateTailHeavyVertices g h hmin ↔
      ∃ k : Fin m,
        2 ≤ minimalSupportPrivateWitness g h hmin b k.succ := by
  classical
  simp [minimalSupportPrivateTailHeavyVertices]

omit [DecidableEq G] in
theorem minimalSupportPrivateTailLightVertices_selectedTailLight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    MinimalSupportSelectedPrivateWitnessesTailLight g h hmin
      (minimalSupportPrivateTailLightVertices g h hmin) := by
  intro b hb
  exact (mem_minimalSupportPrivateTailLightVertices_iff g h hmin b).mp hb

omit [DecidableEq G] in
/-- The tail-light and tail-heavy private owners partition the deletion set. -/
theorem card_minimalSupportPrivateTailLight_add_tailHeavyVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportPrivateTailLightVertices g h hmin).card +
      (minimalSupportPrivateTailHeavyVertices g h hmin).card = B.card := by
  classical
  let L := minimalSupportPrivateTailLightVertices g h hmin
  let H := minimalSupportPrivateTailHeavyVertices g h hmin
  have hdisj : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro b hbL hbH
    have hbLight :=
      (mem_minimalSupportPrivateTailLightVertices_iff g h hmin b).mp hbL
    obtain ⟨k, hk⟩ :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff g h hmin b).mp hbH
    have := hbLight k
    omega
  have hunion : L ∪ H = Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hbLight : ∀ k : Fin m,
        minimalSupportPrivateWitness g h hmin b k.succ ≤ 1
    · exact Or.inl
        ((mem_minimalSupportPrivateTailLightVertices_iff
          g h hmin b).mpr hbLight)
    · right
      push Not at hbLight
      obtain ⟨k, hk⟩ := hbLight
      exact (mem_minimalSupportPrivateTailHeavyVertices_iff
        g h hmin b).mpr ⟨k, by omega⟩
  change L.card + H.card = B.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

/-- In the critical-depth regime, either crossing is already large or there
is at most one tail-light private owner. -/
theorem critical_largeCross_or_privateTailLightVertices_card_le_one
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      (minimalSupportPrivateTailLightVertices g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card ≤ 1 := by
  let S := minimalSupportPrivateTailLightVertices g
    ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
  by_cases hlarge : criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g
  · exact Or.inl hlarge
  · right
    by_contra hcard
    have hS : 2 ≤ S.card := by
      simpa [S] using (show 2 ≤
        (minimalSupportPrivateTailLightVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card by omega)
    exact hlarge (critical_largeCross_of_two_selectedPrivateTailLight
      hq g hg hmin S
        (minimalSupportPrivateTailLightVertices_selectedTailLight
          g _ hmin) hS hB)

/-- Quantitative abundance form: outside large crossing, all but at most one
deletion owner has a tail-heavy private witness. -/
theorem critical_largeCross_or_allButOne_privateTailHeavy
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card ≤
        (minimalSupportPrivateTailHeavyVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card + 1 := by
  rcases critical_largeCross_or_privateTailLightVertices_card_le_one
      hq g hg hmin hB with hlarge | hlight
  · exact Or.inl hlarge
  · right
    have hpartition :=
      card_minimalSupportPrivateTailLight_add_tailHeavyVertices
        g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
    omega

/-- Premise-free critical frontier for the selected private family: crossing
is large, the deletion set lies below the half-gap depth cutoff, or all but
at most one deletion owner carries a tail-heavy private witness. -/
theorem critical_largeCross_or_minimalSupport_card_le_depth_add_one_or_allButOneHeavy
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card ≤ min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 ∨
      B.card ≤
        (minimalSupportPrivateTailHeavyVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card + 1 := by
  by_cases hB :
      min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card
  · rcases critical_largeCross_or_allButOne_privateTailHeavy
      hq g hg hmin hB with hlarge | hheavy
    · exact Or.inl hlarge
    · exact Or.inr (Or.inr hheavy)
  · exact Or.inr (Or.inl (by omega))

end MinModulus
