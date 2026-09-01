/-
# Retaining the root-support exchange in the anchor-heavy branch

The three omissions produced by the exact two-singleton fan are not arbitrary:
two are the source negative tail, while the constructed witness vanishes on a
source positive-tail coordinate.  After tail-light reconstruction, the new
canonical collision therefore contains the entire source negative tail and
drops a source positive coordinate.  This makes its restored padding layer
quantitatively separated from the dominant root layer.
-/
import MinModulus.G1AnchorHeavyGrowth

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Any restored target which drops a source-support coordinate is separated
from the root padding layer by at least half of their common full weight. -/
theorem isRootSeparatedRestoredLayer_of_support_card_le_of_dropped_nonempty
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hdrop : (reducedCollisionDroppedSupport r v).Nonempty) :
    IsRootSeparatedRestoredLayer r v := by
  have hinter := two_mul_card_restoredValueLayer_inter_root_le
    hg r v hcard hdrop
  refine ⟨hinter, ?_⟩
  have hunion := Finset.card_union_add_card_inter
    (collisionPaddingValueLayer r) (restoredCollisionValueLayer r v)
  rw [card_collisionPaddingValueLayer hg r,
    card_restoredCollisionValueLayer hg r v hcard] at hunion
  have hinter' : 2 * (collisionPaddingValueLayer r ∩
      restoredCollisionValueLayer r v).card ≤
      reducedCollisionWeight (m := m) r := by
    simpa [Finset.inter_comm] using hinter
  omega

/-- The genuine two-singleton residual has a geometry-preserving dichotomy.
Either one selected escape target already has negative tail at least three,
or the anchor-heavy reconstruction contains all of the root negative tail and
drops a root positive-tail coordinate. -/
theorem genuineDominant_two_tail_escape_growth_or_anchor_exchange
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
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalReducedCollisions (g := g) hh ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧ 2 ≤ reducedCollisionImbalance v ∧
      r.val.2 ⊆ v.val.2 ∧
      (r.val.1 \ reducedCollisionSupport v).Nonempty := by
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
  obtain ⟨j, k, v, u, z, hjk, hrB, hv, hu, _hvu,
      hjvAvoid, hkuAvoid, _hkv, _hju, _hzv, _hzu, hzr, hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases hshape with hexact | hvgrow | hugrow
  · have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      rcases mem_canonicalSupportEscapeTargets_iff.mp hv with ⟨x, hx⟩
      exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
    have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
      rcases mem_canonicalSupportEscapeTargets_iff.mp hu with ⟨x, hx⟩
      exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
    have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hr
    have hzj : z ≠ j := by
      intro hzj
      subst z
      exact hzr (by rw [hrB]; simp)
    have hzk : z ≠ k := by
      intro hzk
      subst z
      exact hzr (by rw [hrB]; simp)
    have hvjzero : subsetCollisionCoeffs v.val.1 v.val.2 j.succ = 0 := by
      have hjA : j ∉ v.val.1 := fun hjA ↦
        hjvAvoid (Finset.mem_union_left _ hjA)
      have hjB : j ∉ v.val.2 := fun hjB ↦
        hjvAvoid (Finset.mem_union_right _ hjB)
      simp [subsetCollisionCoeffs, hjA, hjB]
    have hukzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0 := by
      have hkA : k ∉ u.val.1 := fun hkA ↦
        hkuAvoid (Finset.mem_union_left _ hkA)
      have hkB : k ∉ u.val.2 := fun hkB ↦
        hkuAvoid (Finset.mem_union_right _ hkB)
      simp [subsetCollisionCoeffs, hkA, hkB]
    have hrzNe : subsetCollisionCoeffs r.val.1 r.val.2 z.succ ≠ 0 := by
      intro hrzero
      exact canonical_exactTriangle_two_zero_not_allZero_zmod
        hN hM g hg r v u hrcanonical hvcanonical hucanonical
          hjk hzj hzk hrB hexact.1
          (by simpa [pair_comm] using hexact.2)
          hrzero hvjzero hukzero
    have hrzNotNeg :
        subsetCollisionCoeffs r.val.1 r.val.2 z.succ ≠ -1 := by
      intro hrneg
      have hzB := (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 z).mp hrneg
      exact hzr (Finset.mem_sdiff.mp hzB).1
    have hrzone : subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 1 := by
      have hb := subsetCollisionCoeffs_tail_bounds r.val.1 r.val.2 z
      omega
    let cr := subsetCollisionCoeffs r.val.1 r.val.2
    let cv := subsetCollisionCoeffs v.val.1 v.val.2
    let cu := subsetCollisionCoeffs u.val.1 u.val.2
    have hrcard := canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hrcanonical)
    have hvcard := canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
    have hucard := canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hucanonical)
    have hcr : Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) cr :=
      witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
        hrcard r.property.2
    have hcv : Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) cv :=
      witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
        hvcard v.property.2
    have hcu : Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) cu :=
      witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
        hucard u.property.2
    have hR := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) r hrcanonical hrB
    have hV := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) v hvcanonical hexact.1
    have hU := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) u hucanonical
        (by simpa [pair_comm] using hexact.2)
    have hdetail :=
      common_touched_or_exists_three_omissions_of_light_triangle
        g hg (half_add_half hN) hcv hcu hcr
          k.succ z.succ j.succ
          ((Fin.succ_injective _).ne (Ne.symm hzk))
          ((Fin.succ_injective _).ne hzj)
          ((Fin.succ_injective _).ne hjk)
          (by simpa [cv] using hV)
          (by
            intro i
            simpa [cu, or_comm] using hU i)
          (by simpa [cr] using hR)
          (by simpa [cr] using hrzone)
    rcases hdetail with htouch | ⟨x, c, hxj, hxk, hxz, _hcrx,
        hc, hczero, hck, hcj, hcx⟩
    · have htouch' : CriticalCommonTouched g := by
        refine ⟨z.succ, ?_⟩
        intro c' hc'
        apply htouch c'
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc'
      exact False.elim (hres.2.1 htouch')
    · obtain ⟨e, hce⟩ :=
        exists_coeff_ge_two_of_omit_other_and_zero_at_exact_pair
          g hg (half_add_half hN) hcv hc k.succ z.succ
            (by simpa [cv] using hV) hck hczero
      have he0 := heavy_coordinate_eq_anchor_of_not_criticalHeavy
        g hres.2.2 c hc e hce
      subst e
      have hceil : ∀ y : Fin n, c y.succ ≤ 1 := by
        intro y
        by_contra hy
        have hy2 : 2 ≤ c y.succ := by omega
        exact hres.2.2 ⟨c, hc, y, hy2⟩
      obtain ⟨w, hwcanonical, hwcoeff, hwimbalance, hwcard⟩ :=
        exists_canonicalReducedCollision_of_anchorHeavy_three_omissions
          g (half_add_half hN) hc hceil k.succ j.succ x
            ((Fin.succ_injective _).ne (Ne.symm hjk))
            (Ne.symm hxj) hxk hck hcj hcx hce
      have hwne : w ≠ r := by
        intro hwr
        subst w
        omega
      have hkW : k ∈ w.val.2 := by
        have hkcoeff : subsetCollisionCoeffs w.val.1 w.val.2 k.succ = -1 := by
          rw [hwcoeff]
          exact hck
        exact (Finset.mem_sdiff.mp
          ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
            w.val.1 w.val.2 k).mp hkcoeff)).1
      have hjW : j ∈ w.val.2 := by
        have hjcoeff : subsetCollisionCoeffs w.val.1 w.val.2 j.succ = -1 := by
          rw [hwcoeff]
          exact hcj
        exact (Finset.mem_sdiff.mp
          ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
            w.val.1 w.val.2 j).mp hjcoeff)).1
      have hrBW : r.val.2 ⊆ w.val.2 := by
        intro y hy
        rw [hrB] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hjW
        · exact hkW
      have hzA : z ∈ r.val.1 := by
        by_contra hzA
        have : subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 0 := by
          simp [subsetCollisionCoeffs, hzA, hzr]
        exact hrzNe this
      have hwzero : subsetCollisionCoeffs w.val.1 w.val.2 z.succ = 0 := by
        rw [hwcoeff]
        exact hczero
      have hzW : z ∉ reducedCollisionSupport w := by
        intro hzW
        rcases Finset.mem_union.mp hzW with hzWA | hzWB
        · have hznotB : z ∉ w.val.2 := by
            intro hzWB
            exact Finset.disjoint_left.mp w.property.1 hzWA hzWB
          have hwone : subsetCollisionCoeffs w.val.1 w.val.2 z.succ = 1 := by
            simp [subsetCollisionCoeffs, hzWA, hznotB]
          omega
        · have hznotA : z ∉ w.val.1 := by
            intro hzWA
            exact Finset.disjoint_left.mp w.property.1 hzWA hzWB
          have hwneg : subsetCollisionCoeffs w.val.1 w.val.2 z.succ = -1 := by
            simp [subsetCollisionCoeffs, hznotA, hzWB]
          omega
      exact Or.inr ⟨w, by simpa [hh] using hwcanonical, hwne, hwcard,
        hwimbalance, hrBW,
        ⟨z, Finset.mem_sdiff.mpr ⟨hzA, hzW⟩⟩⟩
  · exact Or.inl ⟨v, hv, hvgrow⟩
  · exact Or.inl ⟨u, hu, hugrow⟩

/-- In either branch, the larger-tail collision carries a full restored layer
of dominant weight which is quantitatively separated from the root layer.
The target also grows support strictly and loses at least one binary padding
dimension. -/
theorem genuineDominant_two_tail_exists_rootSeparated_tail_growth
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
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalReducedCollisions (g := g) hh ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      (reducedCollisionSupport r).card <
        (reducedCollisionSupport v).card ∧
      2 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      IsFullRestoredCollisionLayer r v ∧
      IsRootSeparatedRestoredLayer r v := by
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
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  rcases genuineDominant_two_tail_escape_growth_or_anchor_exchange
      hqodd g hg r hr hres hBcard with hgrow | hexchange
  · obtain ⟨v, hvtarget, hvcard⟩ := hgrow
    rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨j, hjv⟩
    have hvcanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjv).2.1
    have hvr := reducedCollision_ne_of_right_mem_of_avoids
      r v (mem_canonicalSupportEscapeIncidences_iff.mp hjv).1
        (mem_canonicalSupportEscapeIncidences_iff.mp hjv).2.2.1
    have hgrowth := canonical_other_support_growth_of_strictMajority
      hh r hrcanonical hmajor v hvcanonical hvr
    exact ⟨v, hvcanonical, hvr, hvcard, by
      simpa [reducedCollisionSupport] using hgrowth.1,
      hgrowth.2,
      isFullRestoredCollisionLayer_of_support_card_le hg r v (by
        simpa [reducedCollisionSupport] using hgrowth.1.le),
      canonicalSupportEscapeTarget_isRootSeparatedRestoredLayer
        hg hh r hrcanonical hmajor hjv⟩
  · obtain ⟨v, hvcanonical, hvr, hvcard, _hvimbalance,
      _hrBv, hdrop⟩ := hexchange
    have hgrowth := canonical_other_support_growth_of_strictMajority
      hh r hrcanonical hmajor v hvcanonical hvr
    have hsupportLe : (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
      simpa [reducedCollisionSupport] using hgrowth.1.le
    have hdropped : (reducedCollisionDroppedSupport r v).Nonempty := by
      rcases hdrop with ⟨z, hz⟩
      have hz' := Finset.mem_sdiff.mp hz
      exact ⟨z, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ hz'.1, hz'.2⟩⟩
    exact ⟨v, hvcanonical, hvr, hvcard, by
      simpa [reducedCollisionSupport] using hgrowth.1,
      hgrowth.2,
      isFullRestoredCollisionLayer_of_support_card_le hg r v hsupportLe,
      isRootSeparatedRestoredLayer_of_support_card_le_of_dropped_nonempty
        hg r v hsupportLe hdropped⟩

end MinModulus
