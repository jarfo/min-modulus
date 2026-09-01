/-
# Closure of the large-negative-tail genuine residual

The depth-deficit budget gives more than a target count.  If
`d = n - |supp(r)|` and a non-root target has support depth `t`, then its
unused ambient exponent is `e = d - t` and `2e <= 2^e = w_v`.  Summing the
escape-depth tax therefore yields

`2|B_r| <= sum_{v != r} w_v`.

Quarter-star concentration implies `8|B_r| <= 2^d`, hence
`|B_r| <= 2^(d-3)`.  Canonical orientation gives
`|supp(r)| <= 2|B_r|`, so `n <= 2|B_r| + d`.

These inequalities are incompatible with strict small crossing.  The root
star forces `4 * 2^d * |B_r|` below the critical half-gap square, while the
half-gap is at most `n+1`.  A uniform elementary estimate shows

`(2|B_r| + d + 1)^2 < 4 * 2^d * |B_r|`

for `d >= 5` and `|B_r| <= 2^(d-3)`.  Thus the genuine dominant residual is
empty in every dimension; no finite profile enumeration is used.
-/
import MinModulus.G1GlobalDepthDeficit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Twice an exponent is bounded by the corresponding power of two,
including exponent zero. -/
theorem two_mul_le_two_pow (e : ℕ) : 2 * e ≤ 2 ^ e := by
  by_cases he : e = 0
  · subst e
    norm_num
  · exact two_mul_le_two_pow_of_pos e (Nat.pos_of_ne_zero he)

omit [DecidableEq G] in
/-- Exact padding normalization pays twice the unused ambient depth of every
support-growing collision. -/
theorem two_mul_ambientDepth_sub_supportDepth_le_weight
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card) :
    2 * ((m - (reducedCollisionSupport r).card) -
        reducedCollisionSupportDepth r v) ≤
      reducedCollisionWeight (m := m) v := by
  have hvle : (reducedCollisionSupport v).card ≤ m := by
    have := Finset.card_le_univ (reducedCollisionSupport v)
    simpa using this
  have hremainder :
      m - (reducedCollisionSupport v).card =
        (m - (reducedCollisionSupport r).card) -
          reducedCollisionSupportDepth r v := by
    simp only [reducedCollisionSupportDepth]
    omega
  change 2 * ((m - (reducedCollisionSupport r).card) -
      reducedCollisionSupportDepth r v) ≤
    2 ^ (m - (reducedCollisionSupport v).card)
  rw [hremainder]
  exact two_mul_le_two_pow _

/-- Four times `d+1` fits in `2^d` from depth five onward. -/
theorem four_mul_succ_le_two_pow_of_five_le (d : ℕ) (hd : 5 ≤ d) :
    4 * (d + 1) ≤ 2 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd' : 5 ≤ d
      · have hprev := ih hd'
        have hfour : 4 ≤ 2 ^ d := by
          have : 2 ^ 2 ≤ 2 ^ d :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at this ⊢
          exact this
        rw [pow_succ]
        omega
      · have hd4 : d = 4 := by omega
        subst d
        norm_num

/-- The square of `d+1` has the required exponential bound from depth five
onward. -/
theorem succ_square_le_two_pow_succ_of_five_le (d : ℕ) (hd : 5 ≤ d) :
    (d + 1) ^ 2 ≤ 2 ^ (d + 1) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd' : 5 ≤ d
      · have hprev := ih hd'
        have hsquare : (d + 2) ^ 2 ≤ 2 * (d + 1) ^ 2 := by
          nlinarith
        calc
          (d + 2) ^ 2 ≤ 2 * (d + 1) ^ 2 := hsquare
          _ ≤ 2 * 2 ^ (d + 1) := Nat.mul_le_mul_left 2 hprev
          _ = 2 ^ (d + 2) := by
            rw [show d + 2 = (d + 1) + 1 by omega, pow_succ,
              pow_succ]
            ring
      · have hd4 : d = 4 := by omega
        subst d
        norm_num

/-- Numerical incompatibility at the heart of the large-tail closure. -/
theorem square_two_mul_add_depth_lt_four_mul_pow_mul
    (d B : ℕ) (hd : 5 ≤ d) (hBpos : 0 < B)
    (hBupper : B ≤ 2 ^ (d - 3)) :
    (2 * B + d + 1) ^ 2 < 4 * 2 ^ d * B := by
  have hBsqRaw := Nat.mul_le_mul_left (4 * B) hBupper
  have hpowShift : 4 * B * 2 ^ (d - 3) = B * 2 ^ (d - 1) := by
    rw [show d - 1 = (d - 3) + 2 by omega, pow_add]
    norm_num
    ring
  have hBsqLe : 4 * B * B ≤ B * 2 ^ (d - 1) := by
    rw [← hpowShift]
    simpa [Nat.mul_assoc] using hBsqRaw
  have hpowLt : 2 ^ (d - 1) < 2 ^ d :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hBsq : 4 * B * B < B * 2 ^ d :=
    hBsqLe.trans_lt (Nat.mul_lt_mul_of_pos_left hpowLt hBpos)
  have hlinearRaw := four_mul_succ_le_two_pow_of_five_le d hd
  have hlinear : 4 * B * (d + 1) ≤ B * 2 ^ d := by
    have := Nat.mul_le_mul_left B hlinearRaw
    nlinarith
  have hsquareRaw := succ_square_le_two_pow_succ_of_five_le d hd
  have hpowSucc : 2 ^ (d + 1) = 2 * 2 ^ d := by
    rw [pow_succ]
    ring
  have hBone : 1 ≤ B := by omega
  have hsquare : (d + 1) ^ 2 ≤ B * (2 * 2 ^ d) := by
    calc
      (d + 1) ^ 2 ≤ 2 ^ (d + 1) := hsquareRaw
      _ = 2 * 2 ^ d := hpowSucc
      _ ≤ B * (2 * 2 ^ d) := by
        simpa using Nat.mul_le_mul_right (2 * 2 ^ d) hBone
  nlinarith

/-- The certified critical half-gap is at most the ambient tail cube size
`n+1`. -/
theorem criticalHalfGap_le_succ (n s : ℕ) (hn : 1 ≤ n) :
    criticalHalfGap n s ≤ n + 1 := by
  let a := min (s + 1) (Nat.log 2 (n + 1))
  have hlog : 0 < Nat.log 2 (n + 1) :=
    Nat.log_pos (by norm_num) (by omega)
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min (by omega) hlog
  have hgap : criticalHalfGap n s ≤ 2 ^ a := by
    change 2 ^ (a - 1) + 1 ≤ 2 ^ a
    calc
      2 ^ (a - 1) + 1 ≤ 2 ^ (a - 1) + 2 ^ (a - 1) :=
        Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ a := Nat.two_pow_pred_add_two_pow_pred ha
  have hale : a ≤ Nat.log 2 (n + 1) := min_le_right _ _
  exact hgap.trans ((Nat.pow_le_pow_right (by norm_num) hale).trans
    (Nat.pow_log_le_self 2 (by omega)))

section CriticalLargeNegativeClosure

/-- The escape-depth tax pays twice the whole negative root tail from the
non-root crossing-star weight. -/
theorem genuineDominant_two_mul_negativeTailCard_le_crossStarWeight
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    2 * r.val.2.card ≤ canonicalCrossStarWeight hh r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  change 2 * r.val.2.card ≤ canonicalCrossStarWeight hh r
  let C := canonicalReducedCollisions (g := g) hh
  let E := canonicalOtherReducedCollisions hh r
  let depth := reducedCollisionSupportDepth r
  let weight : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) → ℕ :=
    reducedCollisionWeight (m := n)
  let d := n - (reducedCollisionSupport r).card
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ v ∈ C, (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by
    simpa [C, hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hbudget :=
    genuineDominant_negativeTail_add_sumDepth_le_ambientDepth_mul_nonrootCard
      hqodd g hg r hr hres
  change r.val.2.card + E.sum depth ≤ d * E.card at hbudget
  have hpoint : ∀ v ∈ E, 2 * d ≤ 2 * depth v + weight v := by
    intro v hv
    have hvC : v ∈ C := by
      apply Finset.mem_of_mem_erase
      simpa [E, C, canonicalOtherReducedCollisions] using hv
    have hcard := hrmin v hvC
    have hdepthle : depth v ≤ d := by
      have hvle : (reducedCollisionSupport v).card ≤ n := by
        have := Finset.card_le_univ (reducedCollisionSupport v)
        simpa using this
      simp only [depth, d, reducedCollisionSupportDepth]
      omega
    have hunused := two_mul_ambientDepth_sub_supportDepth_le_weight
      r v hcard
    change 2 * (d - depth v) ≤ weight v at hunused
    omega
  have hpointSum : 2 * d * E.card ≤
      2 * E.sum depth + E.sum weight := by
    calc
      2 * d * E.card = E.sum (fun _ ↦ 2 * d) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ E.sum (fun v ↦ 2 * depth v + weight v) :=
        Finset.sum_le_sum hpoint
      _ = 2 * E.sum depth + E.sum weight := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hweightSum : E.sum weight = canonicalCrossStarWeight hh r := by
    simp [E, weight, canonicalOtherReducedCollisions,
      canonicalCrossStarWeight]
  have hbudgetTwo : 2 * r.val.2.card + 2 * E.sum depth ≤
      2 * d * E.card := by
    have := Nat.mul_le_mul_left 2 hbudget
    simpa [Nat.mul_add, Nat.mul_assoc] using this
  rw [← hweightSum]
  omega

/-- No large-negative-tail genuine dominant residual exists. -/
theorem not_isCriticalGenuineDominantEscapeCollision_of_three_le_negativeTail
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hBthree : 3 ≤ r.val.2.card) :
    ¬ IsCriticalGenuineDominantEscapeCollision g r := by
  classical
  intro hres
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let d := n - (reducedCollisionSupport r).card
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hcanonical := mem_canonicalReducedCollisions_iff.mp hr'
  have hAleB := canonicalReducedCollision_card_le hcanonical
  have hsupportCard : (reducedCollisionSupport r).card =
      r.val.1.card + r.val.2.card := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint r.property.1]
  have hsupportLe : (reducedCollisionSupport r).card ≤
      2 * r.val.2.card := by omega
  have hsupportUniv : (reducedCollisionSupport r).card ≤ n := by
    have := Finset.card_le_univ (reducedCollisionSupport r)
    simpa using this
  have hdepthFive := genuineDominant_rootSupport_add_five_le
    hn hqodd g hg r hr hres
  have hd : 5 ≤ d := by
    dsimp only [d]
    omega
  have hnUpper : n ≤ 2 * r.val.2.card + d := by
    dsimp only [d]
    omega
  have htwoB := genuineDominant_two_mul_negativeTailCard_le_crossStarWeight
    hqodd g hg r hr hres
  have hquarter :=
    genuineDominant_four_mul_crossStarWeight_le_rootWeight_global
      hn hqodd g hg r hr hres
  have hweight : reducedCollisionWeight (m := n) r = 2 ^ d := by rfl
  have heightB : 8 * r.val.2.card ≤ 2 ^ d := by
    change 2 * r.val.2.card ≤ canonicalCrossStarWeight hh r at htwoB
    change 4 * canonicalCrossStarWeight hh r ≤
      reducedCollisionWeight (m := n) r at hquarter
    rw [hweight] at hquarter
    omega
  have hpowSplit : 2 ^ d = 8 * 2 ^ (d - 3) := by
    rw [show d = (d - 3) + 3 by omega, pow_add]
    norm_num
    ring
  have hBupper : r.val.2.card ≤ 2 ^ (d - 3) := by
    rw [hpowSplit] at heightB
    omega
  have hnumeric := square_two_mul_add_depth_lt_four_mul_pow_mul
    d r.val.2.card hd (by omega) hBupper
  have hgap := criticalHalfGap_le_succ n s hn
  have hgapSquare : criticalHalfGap n s * criticalHalfGap n s ≤
      (n + 1) ^ 2 := by nlinarith
  have hnSquare : (n + 1) ^ 2 ≤
      (2 * r.val.2.card + d + 1) ^ 2 := by
    nlinarith
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstar' : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstar
  have htailStar :=
    genuineDominant_negativeTail_add_nonrootCard_le_crossStarWeight
      hqodd g hg r hr hres
  have hBstar : r.val.2.card ≤ canonicalCrossStarWeight hh r := by
    change r.val.2.card + canonicalCrossStarCard hh r ≤
      canonicalCrossStarWeight hh r at htailStar
    omega
  have hcrossLower : 4 * 2 ^ d * r.val.2.card ≤
      4 * criticalCanonicalCrossMass g := by
    rw [← hweight]
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4
      ((Nat.mul_le_mul_left (reducedCollisionWeight (m := n) r) hBstar).trans
        hstar')
  have hsmall := hres.1.2
  nlinarith

/-- The genuine dominant branch is empty after combining the two-two and
large-negative-tail closures. -/
theorem not_isCriticalGenuineDominantEscapeCollision
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g) :
    ¬ IsCriticalGenuineDominantEscapeCollision g r := by
  intro hres
  exact not_isCriticalGenuineDominantEscapeCollision_of_three_le_negativeTail
    hn hqodd g hg r hr
      (genuineDominant_three_le_negativeTailCard
        hn hqodd g hg r hr hres) hres

/-- The final dominant residual is eliminated: critical G1 is reduced to the
three explicit large-crossing, common-touch, and heavy-witness alternatives. -/
theorem critical_largeCross_or_commonTouched_or_heavy
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g := by
  rcases critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant
      hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr hheavy)
  · exact False.elim
      (not_isCriticalGenuineDominantEscapeCollision
        hn hqodd g hg r hr hres)

end CriticalLargeNegativeClosure

end MinModulus
