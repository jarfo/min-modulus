/-
# Local lightness for minimal-support private witnesses

The pure-star argument does not need every half witness to be tail-light.  It
uses lightness only to turn the private witnesses selected by a minimal
support transversal into canonical reduced collisions.  This file isolates
that exact hypothesis.  It is compatible with a different genuine-heavy
source witness, while failure exposes a selected private witness with a tail
coefficient at least two.
-/
import MinModulus.G1HeavyLightnessAudit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Tail-lightness restricted to the private witnesses canonically selected
by one minimal support transversal. -/
def MinimalSupportPrivateWitnessesTailLight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Prop :=
  ∀ b : {b : Fin (m + 1) // b ∈ B}, ∀ k : Fin m,
    minimalSupportPrivateWitness g h hmin b k.succ ≤ 1

omit [DecidableEq G] in
/-- Global tail-lightness implies the localized private-family condition. -/
theorem MinimalSupportPrivateWitnessesTailLight.of_allHalfWitnessesTailLight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hallLight : AllHalfWitnessesTailLight g h) :
    MinimalSupportPrivateWitnessesTailLight g h hmin := by
  intro b k
  exact hallLight _
    (minimalSupportPrivateWitness_isWitness g h hmin b) k

omit [DecidableEq G] in
/-- Failure of local private-family lightness produces a concrete selected
private witness and tail coordinate with coefficient at least two. -/
theorem exists_minimalSupportPrivateWitness_tailHeavy_of_not_localLight
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hnot : ¬ MinimalSupportPrivateWitnessesTailLight g h hmin) :
    ∃ b : {b : Fin (m + 1) // b ∈ B}, ∃ k : Fin m,
      2 ≤ minimalSupportPrivateWitness g h hmin b k.succ := by
  unfold MinimalSupportPrivateWitnessesTailLight at hnot
  push Not at hnot
  obtain ⟨b, k, hk⟩ := hnot
  exact ⟨b, k, by omega⟩

/-- Two locally tail-light private witnesses give two distinct canonical
shapes.  Hence, relative to any prescribed root, at least one is a different
canonical collision. -/
theorem exists_other_canonicalReducedCollision_of_minimalSupportPrivate_localLight
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hlocal : MinimalSupportPrivateWitnessesTailLight g h hmin)
    (hBcard : 2 ≤ B.card) :
    ∃ w : ReducedSubsetSumCollision g h,
      w ∈ canonicalReducedCollisions (g := g) hh ∧ w ≠ r := by
  classical
  let raw : {b : Fin (m + 1) // b ∈ B} →
      ReducedSubsetSumCollision g h := fun b ↦
    reducedCollisionOfTailLightWitness g
      (minimalSupportPrivateWitness_isWitness g h hmin b)
      (hlocal b)
  let can : {b : Fin (m + 1) // b ∈ B} →
      ReducedSubsetSumCollision g h := fun b ↦
    canonicalizeReducedCollision hh (raw b)
  have hcoeff : ∀ b, subsetCollisionCoeffs (raw b).val.1 (raw b).val.2 =
      minimalSupportPrivateWitness g h hmin b := by
    intro b
    exact reducedCollisionOfTailLightWitness_coeffs g
      (minimalSupportPrivateWitness_isWitness g h hmin b)
      (hlocal b)
  have hrawNe : ∀ {b₁ b₂}, b₁ ≠ b₂ → raw b₁ ≠ raw b₂ := by
    intro b₁ b₂ hb hraw
    apply hb
    apply minimalSupportPrivateWitness_injective g h hmin
    calc
      minimalSupportPrivateWitness g h hmin b₁ =
          subsetCollisionCoeffs (raw b₁).val.1 (raw b₁).val.2 :=
        (hcoeff b₁).symm
      _ = subsetCollisionCoeffs (raw b₂).val.1 (raw b₂).val.2 := by
        rw [hraw]
      _ = minimalSupportPrivateWitness g h hmin b₂ := hcoeff b₂
  have hrawNeSwap : ∀ b₁ b₂,
      raw b₁ ≠ reducedSubsetSumCollisionSwapEquiv hh (raw b₂) := by
    intro b₁ b₂ hswap
    apply minimalSupportPrivateWitness_ne_neg g h hmin b₁ b₂
    calc
      minimalSupportPrivateWitness g h hmin b₁ =
          subsetCollisionCoeffs (raw b₁).val.1 (raw b₁).val.2 :=
        (hcoeff b₁).symm
      _ = subsetCollisionCoeffs
          (reducedSubsetSumCollisionSwapEquiv hh (raw b₂)).val.1
          (reducedSubsetSumCollisionSwapEquiv hh (raw b₂)).val.2 := by
        rw [hswap]
      _ = subsetCollisionCoeffs (raw b₂).val.2 (raw b₂).val.1 := by rfl
      _ = -subsetCollisionCoeffs (raw b₂).val.1 (raw b₂).val.2 :=
        subsetCollisionCoeffs_swap _ _
      _ = -minimalSupportPrivateWitness g h hmin b₂ := by rw [hcoeff b₂]
  have hcanNe : ∀ {b₁ b₂}, b₁ ≠ b₂ → can b₁ ≠ can b₂ := by
    intro b₁ b₂ hb
    exact canonicalizeReducedCollision_ne_of_ne_of_ne_swap
      hh (raw b₁) (raw b₂) (hrawNe hb) (hrawNeSwap b₁ b₂)
  have hcanMem : ∀ b, can b ∈ canonicalReducedCollisions (g := g) hh := by
    intro b
    exact mem_canonicalReducedCollisions_iff.mpr
      (canonicalizeReducedCollision_isCanonical hh hh0 (raw b))
  have hattach : 1 < B.attach.card := by
    rw [Finset.card_attach]
    omega
  obtain ⟨u, _hu, v, _hv, huv⟩ := Finset.one_lt_card.mp hattach
  have hcanUV : can u ≠ can v := hcanNe huv
  by_cases hur : can u = r
  · refine ⟨can v, hcanMem v, ?_⟩
    intro hvr
    apply hcanUV
    rw [hur, hvr]
  · exact ⟨can u, hcanMem u, hur⟩

/-- A high-weight canonical root and one different canonical collision force
critical large crossing from dimension seven onward. -/
theorem critical_largeCross_of_highWeightCanonical_and_other_of_seven_le
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r w : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hw : w ∈ criticalCanonicalReducedCollisions g)
    (hwr : w ≠ r)
    (hrweight : 2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hw' : w ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hw
  have hwErase : w ∈ (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hwr, hw'⟩
  have hsingle : reducedCollisionWeight (m := n) w ≤
      canonicalCrossStarWeight hh r := by
    simpa [canonicalCrossStarWeight] using
      (Finset.single_le_sum
        (fun x _hx ↦ Nat.zero_le (reducedCollisionWeight (m := n) x))
        hwErase)
  have hwpos : 1 ≤ reducedCollisionWeight (m := n) w := by
    unfold reducedCollisionWeight
    exact Nat.one_le_two_pow
  have hstarOne : 1 ≤ canonicalCrossStarWeight hh r := hwpos.trans hsingle
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstar' : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstar
  have hcrossLower : 2 ^ (n - 3) ≤ criticalCanonicalCrossMass g := by
    have hmul := Nat.mul_le_mul hrweight hstarOne
    have : 2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r *
        canonicalCrossStarWeight hh r := by simpa using hmul
    exact this.trans hstar'
  have hgap := criticalHalfGap_square_le_two_pow_pred (s := s) hnseven
  have hfour : 2 ^ (n - 1) ≤ 4 * criticalCanonicalCrossMass g := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    norm_num
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hcrossLower
  exact hgap.trans hfour

/-- The pure-star closure with global tail-lightness replaced by exactly the
local lightness of the selected private family. -/
theorem critical_largeCross_of_highWeightCanonical_and_minimalSupportPrivate_localLight
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hrweight : 2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hlocal : MinimalSupportPrivateWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin)
    (hBcard : 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨w, hw, hwr⟩ :=
    exists_other_canonicalReducedCollision_of_minimalSupportPrivate_localLight
      g hh (half_ne_zero hN hM) r hmin hlocal hBcard
  have hw' : w ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hw
  exact critical_largeCross_of_highWeightCanonical_and_other_of_seven_le
    hq hnseven g hg r w hr hw' hwr hrweight

end MinModulus
