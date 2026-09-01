/-
# A third blocked signature from the anchor exchange

For a two-coordinate dominant negative tail, the two selected escape targets
omit opposite source-tail coordinates.  The anchor-exchange collision instead
contains both source-tail coordinates.  Membership in a restored blocked
signature agrees with target-support membership on the root support, so these
three targets yield three pairwise-distinct restored signatures.
-/
import MinModulus.G1AnchorHeavyExchange

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Two no-smaller-support targets have distinct blocked signatures whenever
one avoids a root-support coordinate and the other contains it. -/
theorem restoredCollisionBlockedSupport_ne_of_root_mem_avoid_mem
    {g : Fin (m + 1) → G} {h : G}
    (r q v : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hvcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    {j : Fin m} (hjr : j ∈ reducedCollisionSupport r)
    (hjq : j ∉ reducedCollisionSupport q)
    (hjv : j ∈ reducedCollisionSupport v) :
    restoredCollisionBlockedSupport r q ≠
      restoredCollisionBlockedSupport r v := by
  intro heq
  have hjqBlocked : j ∉ restoredCollisionBlockedSupport r q := by
    intro hj
    exact hjq
      ((mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r q hqcard hjr).mp hj)
  have hjvBlocked : j ∈ restoredCollisionBlockedSupport r v :=
    (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r v hvcard hjr).mpr hjv
  exact hjqBlocked (by rw [heq]; exact hjvBlocked)

/-- Unless a selected escape target already has a larger negative tail, the
two singleton-fiber targets and the anchor-exchange collision produce three
distinct blocked signatures.  All three restored layers have full root weight
and are quantitatively root-separated. -/
theorem genuineDominant_two_tail_escape_growth_or_three_blocked_signatures
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    (∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card) ∨
    ∃ v u w : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧
      u ∈ canonicalSupportEscapeTargets hh r ∧ v ≠ u ∧
      w ∈ canonicalReducedCollisions (g := g) hh ∧ w ≠ r ∧
      3 ≤ w.val.2.card ∧ 2 ≤ reducedCollisionImbalance w ∧
      ({restoredCollisionBlockedSupport r v,
          restoredCollisionBlockedSupport r u,
          restoredCollisionBlockedSupport r w} :
        Finset (Finset (Fin n))).card = 3 ∧
      IsFullRestoredCollisionLayer r v ∧
      IsFullRestoredCollisionLayer r u ∧
      IsFullRestoredCollisionLayer r w ∧
      IsRootSeparatedRestoredLayer r v ∧
      IsRootSeparatedRestoredLayer r u ∧
      IsRootSeparatedRestoredLayer r w := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ a ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport a).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  obtain ⟨j, k, v, u, _z, hjk, hrB, hvtarget, hutarget, hvu,
      hjvAvoid, hkuAvoid, hkv, hju, _hzv, _hzu, _hzr, _hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases genuineDominant_two_tail_escape_growth_or_anchor_exchange
      hqodd g hg r hr hres hBcard with hgrow | hexchange
  · exact Or.inl hgrow
  · obtain ⟨w, hwcanonical, hwr, hwBcard, hwimbalance,
      hrBw, hdrop⟩ := hexchange
    have hvincidence := (mem_canonicalSupportEscapeTargets_iff.mp hvtarget)
    obtain ⟨jv, hjvInc⟩ := hvincidence
    have huincidence := (mem_canonicalSupportEscapeTargets_iff.mp hutarget)
    obtain ⟨ju, hjuInc⟩ := huincidence
    have hvcanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjvInc).2.1
    have hucanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjuInc).2.1
    have hjr : j ∈ reducedCollisionSupport r := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _ (by rw [hrB]; simp)
    have hkr : k ∈ reducedCollisionSupport r := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _ (by rw [hrB]; simp)
    have hkw : k ∈ reducedCollisionSupport w := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _
        (hrBw (by rw [hrB]; simp))
    have hjw : j ∈ reducedCollisionSupport w := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _
        (hrBw (by rw [hrB]; simp))
    have hku : k ∉ reducedCollisionSupport u := hkuAvoid
    have hjv : j ∉ reducedCollisionSupport v := hjvAvoid
    have hju : j ∈ reducedCollisionSupport u := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _ hju
    have hkv' : k ∈ reducedCollisionSupport v := by
      rw [reducedCollisionSupport]
      exact Finset.mem_union_right _ hkv
    have hvcard := hrmin v hvcanonical
    have hucard := hrmin u hucanonical
    have hwcard := hrmin w hwcanonical
    have hvuBlocked : restoredCollisionBlockedSupport r v ≠
        restoredCollisionBlockedSupport r u :=
      restoredCollisionBlockedSupport_ne_of_root_mem_avoid_mem
        r v u hvcard hucard hjr hjv hju
    have hvwBlocked : restoredCollisionBlockedSupport r v ≠
        restoredCollisionBlockedSupport r w :=
      restoredCollisionBlockedSupport_ne_of_root_mem_avoid_mem
        r v w hvcard hwcard hjr hjv hjw
    have huwBlocked : restoredCollisionBlockedSupport r u ≠
        restoredCollisionBlockedSupport r w :=
      restoredCollisionBlockedSupport_ne_of_root_mem_avoid_mem
        r u w hucard hwcard hkr hku hkw
    have hsignatureCard :
        ({restoredCollisionBlockedSupport r v,
            restoredCollisionBlockedSupport r u,
            restoredCollisionBlockedSupport r w} :
          Finset (Finset (Fin n))).card = 3 := by
      simp [hvuBlocked, hvwBlocked, huwBlocked]
    have hdrop' : (reducedCollisionDroppedSupport r w).Nonempty := by
      rcases hdrop with ⟨a, ha⟩
      have ha' := Finset.mem_sdiff.mp ha
      exact ⟨a, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ ha'.1, ha'.2⟩⟩
    exact Or.inr ⟨v, u, w, hvtarget, hutarget, hvu,
      hwcanonical, hwr, hwBcard, hwimbalance, hsignatureCard,
      isFullRestoredCollisionLayer_of_support_card_le hg r v hvcard,
      isFullRestoredCollisionLayer_of_support_card_le hg r u hucard,
      isFullRestoredCollisionLayer_of_support_card_le hg r w hwcard,
      canonicalSupportEscapeTarget_isRootSeparatedRestoredLayer
        hg hh r hrcanonical hmajor hjvInc,
      canonicalSupportEscapeTarget_isRootSeparatedRestoredLayer
        hg hh r hrcanonical hmajor hjuInc,
      isRootSeparatedRestoredLayer_of_support_card_le_of_dropped_nonempty
        hg r w hwcard hdrop'⟩

end MinModulus
