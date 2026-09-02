/-
# Crossing charge from a locally light private-omission fiber

Global tail-lightness is unnecessary for the private padding argument.  A
single shared-omission vertex fiber carries the same `2^(|B|-2)` weight per
locally light private witness, because privacy still leaves every other
deletion coordinate available for padding.  Canonical injectivity and the
general crossing-density theorem then charge every ordered distinct pair in
the fiber.

At a critical modulus, two vertices in such a light fiber already force the
large-crossing inequality whenever `|B|` clears the usual half-gap depth.
Composing this with the common-omission capacity theorem leaves only ambient
label capacity or an explicit tail-heavy member of the large fiber.
-/
import MinModulus.G1PrivateHeavyOmissionVertexLightSplit
import MinModulus.G1MinimalSupportCriticalCrossing

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Privacy leaves all deletion vertices other than the owner (and possibly
the anchor) outside the reduced support of a locally light fiber member. -/
theorem minimalSupportPrivateOmissionReducedCollision_paddingDepth
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    B.card - 2 ≤ m -
      ((minimalSupportPrivateOmissionReducedCollision
          g h hmin z hlight b).val.1 ∪
       (minimalSupportPrivateOmissionReducedCollision
          g h hmin z hlight b).val.2).card := by
  classical
  let c := minimalSupportPrivateWitness g h hmin b.val
  let r := minimalSupportPrivateOmissionReducedCollision
    g h hmin z hlight b
  let R : Finset (Fin m) := r.val.1 ∪ r.val.2
  have hdisj : Disjoint (R.image Fin.succ) (B.erase b.val) := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    obtain ⟨j, hjR, rfl⟩ := Finset.mem_image.mp hxR
    have hjR' : j ∈ witnessPositiveTail c ∪ witnessNegativeTail c := by
      simpa [R, r, minimalSupportPrivateOmissionReducedCollision,
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

omit [DecidableEq G] in
/-- Every locally light private witness in the fiber retains the full private
padding weight `2^(|B|-2)`. -/
theorem pow_card_sub_two_le_minimalSupportPrivateOmissionReducedCollision_weight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateOmissionReducedCollision
        g h hmin z hlight b) := by
  unfold reducedCollisionWeight
  exact Nat.pow_le_pow_right (by norm_num)
    (minimalSupportPrivateOmissionReducedCollision_paddingDepth
      g h hmin z hlight b)

/-- Canonical orientation preserves the local private padding weight. -/
theorem pow_card_sub_two_le_minimalSupportPrivateOmissionCanonicalCollision_weight
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
      (minimalSupportPrivateOmissionCanonicalCollision
        g h hh hmin z hlight b) := by
  calc
    2 ^ (B.card - 2) ≤ reducedCollisionWeight (m := m)
        (minimalSupportPrivateOmissionReducedCollision
          g h hmin z hlight b) :=
      pow_card_sub_two_le_minimalSupportPrivateOmissionReducedCollision_weight
        g h hmin z hlight b
    _ = reducedCollisionWeight (m := m)
        (minimalSupportPrivateOmissionCanonicalCollision
          g h hh hmin z hlight b) :=
      (canonicalizeReducedCollision_weight hh _).symm

/-- The canonically oriented collisions selected by one locally light
omission vertex fiber. -/
noncomputable def minimalSupportPrivateOmissionCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateOmissionCanonicalCollision
      g h hh hmin z hlight)

theorem card_minimalSupportPrivateOmissionCanonicalCollisions
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z) :
    (minimalSupportPrivateOmissionCanonicalCollisions
      g h hh B hmin z hlight).card =
        (minimalSupportPrivateOmissionVertices g hmin z).card := by
  classical
  rw [minimalSupportPrivateOmissionCanonicalCollisions,
    Finset.card_image_of_injective _
      (minimalSupportPrivateOmissionCanonicalCollision_injective
        g h hh hmin z hlight)]
  simp

theorem minimalSupportPrivateOmissionCanonicalCollisions_subset
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z) :
    minimalSupportPrivateOmissionCanonicalCollisions
        g h hh B hmin z hlight ⊆
      canonicalReducedCollisions (g := g) hh := by
  classical
  intro r hr
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
  exact mem_canonicalReducedCollisions_iff.mpr
    (minimalSupportPrivateOmissionCanonicalCollision_isCanonical
      g h hh hh0 hmin z hlight b)

/-- Quadratic-exponential crossing charge from any one locally light private
omission vertex fiber. -/
theorem minimalSupportPrivateOmission_crossingCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z) :
    let V := minimalSupportPrivateOmissionVertices g hmin z
    V.card * (V.card - 1) *
        (2 ^ (B.card - 2) * 2 ^ (B.card - 2)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let V := minimalSupportPrivateOmissionVertices g hmin z
  let F := minimalSupportPrivateOmissionCanonicalCollisions
    g h hh B hmin z hlight
  let w := 2 ^ (B.card - 2)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hFcard : F.card = V.card :=
    card_minimalSupportPrivateOmissionCanonicalCollisions
      g h hh B hmin z hlight
  have hFsub : F ⊆ canonicalReducedCollisions (g := g) hh :=
    minimalSupportPrivateOmissionCanonicalCollisions_subset
      g h hh hh0 B hmin z hlight
  have hweight : ∀ r ∈ F, w ≤ reducedCollisionWeight (m := m) r := by
    intro r hr
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hr
    exact
      pow_card_sub_two_le_minimalSupportPrivateOmissionCanonicalCollision_weight
        g h hh hmin z hlight b
  have hoffsub : F.offDiag ⊆
      canonicalDistinctReducedCollisionPairs (g := g) hh := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    exact mem_canonicalDistinctReducedCollisionPairs_iff.mpr
      ⟨hFsub hp'.1, hFsub hp'.2.1, hp'.2.2⟩
  have hpairs : F.offDiag.card = V.card * (V.card - 1) := by
    rw [Finset.offDiag_card, hFcard, Nat.mul_sub_left_distrib]
    simp
  change V.card * (V.card - 1) * (w * w) ≤
    2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
  calc
    V.card * (V.card - 1) * (w * w) =
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

/-- Two fiber vertices suffice numerically once the deletion set clears the
usual critical half-gap depth. -/
theorem pow_add_one_square_le_two_mul_twoVertexPrivateCrossCharge
    {d b v : ℕ} (hb : d + 2 ≤ b) (hv : 2 ≤ v) :
    (2 ^ d + 1) * (2 ^ d + 1) ≤
      2 * (v * (v - 1) *
        (2 ^ (b - 2) * 2 ^ (b - 2))) := by
  have hppos : 0 < 2 ^ d := pow_pos (by norm_num) d
  have hpone : 1 ≤ 2 ^ d := by omega
  have hdouble : 2 ^ d + 1 ≤ 2 * 2 ^ d := by omega
  have hdepth : d ≤ b - 2 := by omega
  have hpow : 2 ^ d ≤ 2 ^ (b - 2) :=
    Nat.pow_le_pow_right (by norm_num) hdepth
  have hsquare : 2 ^ d * 2 ^ d ≤
      2 ^ (b - 2) * 2 ^ (b - 2) := Nat.mul_le_mul hpow hpow
  have hvprod : 2 ≤ v * (v - 1) := by
    have hvone : 1 ≤ v - 1 := by omega
    exact Nat.mul_le_mul hv hvone
  calc
    (2 ^ d + 1) * (2 ^ d + 1) ≤
        (2 * 2 ^ d) * (2 * 2 ^ d) :=
      Nat.mul_le_mul hdouble hdouble
    _ = 4 * (2 ^ d * 2 ^ d) := by ring
    _ ≤ 4 * (2 ^ (b - 2) * 2 ^ (b - 2)) :=
      Nat.mul_le_mul_left 4 hsquare
    _ = 2 * (2 * (2 ^ (b - 2) * 2 ^ (b - 2))) := by ring
    _ ≤ 2 * (v * (v - 1) *
        (2 ^ (b - 2) * 2 ^ (b - 2))) := by
      exact Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_right
          (2 ^ (b - 2) * 2 ^ (b - 2)) hvprod)

/-- Critical specialization of the local omission-fiber crossing charge. -/
theorem critical_minimalSupportPrivateOmission_crossingCharge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin z) :
    let V := minimalSupportPrivateOmissionVertices g hmin z
    V.card * (V.card - 1) *
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
    (minimalSupportPrivateOmission_crossingCharge
      g hg (half_add_half hN) (half_ne_zero hN hM) hmin z hlight)

/-- A locally light omission fiber with two vertices forces critical large
crossing as soon as the ambient deletion set has the standard depth. -/
theorem critical_largeCross_of_two_light_privateOmissionVertices
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin z)
    (hV : 2 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  let d := min (s + 1) (Nat.log 2 (n + 1)) - 1
  let V := minimalSupportPrivateOmissionVertices g hmin z
  let L := V.card * (V.card - 1) *
    (2 ^ (B.card - 2) * 2 ^ (B.card - 2))
  have hnum : criticalHalfGap n s * criticalHalfGap n s ≤ 2 * L := by
    simpa [criticalHalfGap, d, L, V] using
      (pow_add_one_square_le_two_mul_twoVertexPrivateCrossCharge
        (d := d) (b := B.card) (v := V.card)
        (by simpa [d] using hB) (by simpa [V] using hV))
  have hcharge : L ≤ 2 * criticalCanonicalCrossMass g := by
    simpa [L, V] using
      (critical_minimalSupportPrivateOmission_crossingCharge
        hq g hg hmin z hlight)
  have htwice : 2 * L ≤ 4 * criticalCanonicalCrossMass g := by
    have := Nat.mul_le_mul_left 2 hcharge
    omega
  exact hnum.trans htwice

/-- Direct composition with the 2ga capacity/fiber dichotomy.  Under the
critical depth condition, pair-label counting yields ambient label capacity,
large crossing, or a tail-heavy private witness inside the selected large
shared-omission fiber. -/
theorem critical_privateOmission_capacity_or_largeCross_or_tailHeavy
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (L r : ℕ) (hr : 1 ≤ r)
    (hcount : L * r < B.card * (B.card - 1))
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ z : Fin (n + 1), z ∉ B ∧
        ∃ b : ↥B,
          b ∈ minimalSupportPrivateOmissionVertices g hmin z ∧
          ∃ k : Fin n,
            2 ≤ minimalSupportPrivateWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin b k.succ := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  rcases minimalSupportPrivateCommonOmission_capacity_or_largeVertexFiber
      g hg (half_add_half hN) hmin L r hcount with hcap | hfiber
  · exact Or.inl hcap
  · obtain ⟨z, hzExternal, hzlarge⟩ := hfiber
    have hV : 2 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card := by
      have hone : 1 <
          (minimalSupportPrivateOmissionVertices g hmin z).card *
            (minimalSupportPrivateOmissionVertices g hmin z).card :=
        lt_of_le_of_lt hr hzlarge
      nlinarith
    rcases minimalSupportPrivateOmissionVertices_tailLight_or_exists_tailHeavy
        g _ hmin z with hlight | hheavy
    · exact Or.inr (Or.inl
        (critical_largeCross_of_two_light_privateOmissionVertices
          hq g hg hmin z hlight hV hB))
    · exact Or.inr (Or.inr ⟨z, hzExternal, hheavy⟩)

end MinModulus
