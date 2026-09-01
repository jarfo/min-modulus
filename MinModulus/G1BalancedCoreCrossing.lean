/-
# Two-sided incidence and depth-two growth of the balanced core

A balanced canonical collision points forward to every other canonical
collision in the positive-to-negative crossing relation.  Indeed, applying
the reverse-cross alternative toward imbalance zero leaves an impossible
imbalance gap.  Canonical negative tails also intersect, so every other
negative tail meets both disjoint sides of the balanced core and contains at
least two of its support coordinates.

In a genuine critical residual, a balanced core distinct from the dominant
root cannot occupy the generic tiny depth-one exception: the exception has
root weight two, whereas the dominant fiber bound and the post-singleton root
profiles force root weight greater than four.  Hence a growing balanced core
has support depth at least two and at most one quarter of the root weight.
-/
import MinModulus.G1BalancedCore
import MinModulus.G1SupportGrowthAmortization

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A balanced canonical collision has a forward positive-to-negative
crossing to every distinct canonical collision. -/
theorem balancedCanonical_positive_inter_other_negative
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvbalance : reducedCollisionImbalance v = 0)
    (huv : u ≠ v) :
    (v.val.1 ∩ u.val.2).Nonempty := by
  rcases reducedCollision_reverse_cross_or_imbalance_gap
      g hg hh0 u v
        (canonicalReducedCollision_card_le hu)
        (canonicalReducedCollision_card_le hv) (Ne.symm huv) with
    hinter | hgap
  · simpa [Finset.inter_comm] using hinter
  · rw [hvbalance] at hgap
    omega

/-- Every other canonical negative tail meets both disjoint tails of a
balanced core, hence contains at least two core-support coordinates. -/
theorem balancedCanonical_otherNegative_two_sided_incidence
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvbalance : reducedCollisionImbalance v = 0)
    (huv : u ≠ v) :
    (v.val.1 ∩ u.val.2).Nonempty ∧
      (v.val.2 ∩ u.val.2).Nonempty ∧
      2 ≤ (u.val.2 ∩ reducedCollisionSupport v).card := by
  have hpositive := balancedCanonical_positive_inter_other_negative
    g hg hh hh0 v u hv hu hvbalance huv
  have hnegative := canonicalReducedCollision_negative_tails_inter
    g hg hh hh0 v u hv hu
  obtain ⟨a, ha⟩ := hpositive
  obtain ⟨b, hb⟩ := hnegative
  have ha' := Finset.mem_inter.mp ha
  have hb' := Finset.mem_inter.mp hb
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp v.property.1 ha'.1 hb'.1
  have haSupport : a ∈ reducedCollisionSupport v := by
    exact Finset.mem_union_left _ ha'.1
  have hbSupport : b ∈ reducedCollisionSupport v := by
    exact Finset.mem_union_right _ hb'.1
  have haInter : a ∈ u.val.2 ∩ reducedCollisionSupport v :=
    Finset.mem_inter.mpr ⟨ha'.2, haSupport⟩
  have hbInter : b ∈ u.val.2 ∩ reducedCollisionSupport v :=
    Finset.mem_inter.mpr ⟨hb'.2, hbSupport⟩
  have htwo : 1 < (u.val.2 ∩ reducedCollisionSupport v).card :=
    Finset.one_lt_card.mpr ⟨a, haInter, b, hbInter, hab⟩
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by omega⟩

section CriticalBalancedCoreCrossing

/-- Every genuine residual has a balanced core with two-sided incidence to
the whole canonical family.  The core is either the dominant root or lies at
support depth at least two and has at most one quarter of the root weight. -/
theorem genuineDominant_exists_balancedCore_twoSided_depthTwo
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    ∃ v ∈ criticalCanonicalReducedCollisions g,
      reducedCollisionImbalance v = 0 ∧
      v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card ∧
      (v = r ∨
        (2 ≤ reducedCollisionSupportDepth r v ∧
          (reducedCollisionSupport r).card + 2 ≤
            (reducedCollisionSupport v).card ∧
          4 * reducedCollisionWeight (m := n) v ≤
            reducedCollisionWeight (m := n) r)) ∧
      ∀ u ∈ criticalCanonicalReducedCollisions g, u ≠ v →
        (v.val.1 ∩ u.val.2).Nonempty ∧
        (v.val.2 ∩ u.val.2).Nonempty ∧
        2 ≤ (u.val.2 ∩ reducedCollisionSupport v).card := by
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
  obtain ⟨v, hv, hvbalance, hvcards, hvBcard⟩ :=
    genuineDominant_exists_balanced_criticalCore hqodd g hg r hres
  have hvcanonical : IsCanonicalReducedCollision hh v :=
    mem_canonicalReducedCollisions_iff.mp (by
      simpa [hh, criticalCanonicalReducedCollisions] using hv)
  have hincidence : ∀ u ∈ criticalCanonicalReducedCollisions g, u ≠ v →
      (v.val.1 ∩ u.val.2).Nonempty ∧
      (v.val.2 ∩ u.val.2).Nonempty ∧
      2 ≤ (u.val.2 ∩ reducedCollisionSupport v).card := by
    intro u hu huv
    have hucanonical : IsCanonicalReducedCollision hh u :=
      mem_canonicalReducedCollisions_iff.mp (by
        simpa [hh, criticalCanonicalReducedCollisions] using hu)
    exact balancedCanonical_otherNegative_two_sided_incidence
      g hg hh (half_ne_zero hN hM) v u hvcanonical hucanonical
        hvbalance huv
  refine ⟨v, hv, hvbalance, hvcards, hvBcard, ?_, hincidence⟩
  by_cases hvr : v = r
  · exact Or.inl hvr
  · right
    have hdepthOr := genuineDominant_other_supportDepth_two_or_tiny
      hqodd g hg r v hr hres hv hvr
    have hrootProfile :=
      genuineDominant_two_two_or_three_le_negativeCard
        hn hqodd g hg r hr hres
    have hBtwo : 2 ≤ r.val.2.card := by
      rcases hrootProfile with htwo | hthree
      · omega
      · omega
    have hrootWeight := two_mul_negativeTailCard_lt_weight_of_genuineDominant
      hqodd g hg r hr hres
    have hdepth : 2 ≤ reducedCollisionSupportDepth r v := by
      rcases hdepthOr with hdepth | htiny
      · exact hdepth
      · omega
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hcard : (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
      simpa [reducedCollisionSupport] using hdominant.2.1 v hv
    have hsupport : (reducedCollisionSupport r).card + 2 ≤
        (reducedCollisionSupport v).card := by
      rw [reducedCollisionSupportDepth] at hdepth
      omega
    have hquarter :=
      four_mul_reducedCollisionWeight_le_of_two_le_supportDepth
        r v hcard hdepth
    exact ⟨hdepth, hsupport, hquarter⟩

/-- Global critical localization retaining the exact root profiles and the
depth-two two-sided balanced core. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_balancedCoreDepthTwo
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
        ((r.val.1.card = 2 ∧ r.val.2.card = 2) ∨
          3 ≤ r.val.2.card) ∧
        ∃ v ∈ criticalCanonicalReducedCollisions g,
          reducedCollisionImbalance v = 0 ∧
          v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card ∧
          (v = r ∨
            (2 ≤ reducedCollisionSupportDepth r v ∧
              (reducedCollisionSupport r).card + 2 ≤
                (reducedCollisionSupport v).card ∧
              4 * reducedCollisionWeight (m := n) v ≤
                reducedCollisionWeight (m := n) r)) ∧
          ∀ u ∈ criticalCanonicalReducedCollisions g, u ≠ v →
            (v.val.1 ∩ u.val.2).Nonempty ∧
            (v.val.2 ∩ u.val.2).Nonempty ∧
            2 ≤ (u.val.2 ∩ reducedCollisionSupport v).card := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_largeTail
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, _hlarge⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres,
      genuineDominant_two_two_or_three_le_negativeCard
        hn hqodd g hg r hr hres,
      genuineDominant_exists_balancedCore_twoSided_depthTwo
        hn hqodd g hg r hr hres⟩))

end CriticalBalancedCoreCrossing

end MinModulus
