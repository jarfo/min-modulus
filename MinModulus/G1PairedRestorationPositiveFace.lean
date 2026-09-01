/-
# Positive face for paired directional restoration fans

For a root with negative tail `{j,k}`, a canonical target that drops `j` and
contains `k` in its own negative tail cannot realize the reverse canonical
crossing: its positive tail contains neither `j` nor `k`.  It must therefore
cross forward, so its negative tail meets the root positive tail.  The full
positive upper face is consequently disjoint from that target's entire
restoration fan.  The same holds for the target dropping `k`.

The paired lower packing can thus be enlarged by both root-tail upper faces
without any crossing-mass contamination.  Their only overlap is the upper
face of the complete root support, of size `w_r`.  In the singleton-positive
profile this produces an exact near-tiling: the complement has doubled
cardinality `w_v+w_u`, precisely the two directional fan deficits.
-/
import MinModulus.G1PairedRestorationFans
import MinModulus.G1SignaturePositiveFace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A canonical target dropping `j` and containing the other root-tail
coordinate `k` must cross the root from its positive tail into the target's
negative tail. -/
theorem positiveTail_inter_targetNegativeTail_of_drops_one_contains_other
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (j k : Fin m) (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q) (hkq : k ∈ q.val.2) :
    (r.val.1 ∩ q.val.2).Nonempty := by
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hqr : q ≠ r := by
    exact reducedCollision_ne_of_right_mem_of_avoids r q hjB hjq
  have hcross := distinct_canonicalReducedCollisions_positive_negative_cross
    g hg hh hh0 r q
      (mem_canonicalReducedCollisions_iff.mp hr)
      (mem_canonicalReducedCollisions_iff.mp hq) hqr
  rcases hcross with hforward | hreverse
  · exact hforward
  · exfalso
    rcases hreverse with ⟨x, hx⟩
    have hxqA := (Finset.mem_inter.mp hx).1
    have hxrB := (Finset.mem_inter.mp hx).2
    rw [hB] at hxrB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxrB
    rcases hxrB with rfl | rfl
    · exact hjq (Finset.mem_union_left _ hxqA)
    · exact Finset.disjoint_left.mp q.property.1 hxqA hkq

/-- Both selected targets meet the root positive tail, so its upper face is
disjoint from the root layer and both complete directional fan slices. -/
theorem positiveUpper_disjoint_pairedRestorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hA : r.val.1.Nonempty)
    (hAv : (r.val.1 ∩ reducedCollisionSupport v).Nonempty)
    (hAu : (r.val.1 ∩ reducedCollisionSupport u).Nonempty) :
    Disjoint (blockedSignatureUpperValueLayer g r.val.1)
      (pairedRestorationFanValueUnion r v u j k) := by
  have hAsub : r.val.1 ⊆ reducedCollisionSupport r := by
    intro x hx
    exact Finset.mem_union_left _ hx
  have hrootHit : (r.val.1 ∩ reducedCollisionSupport r).Nonempty := by
    rcases hA with ⟨a, ha⟩
    exact ⟨a, Finset.mem_inter.mpr ⟨ha, hAsub ha⟩⟩
  have hRoot :=
    blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
      hg r.val.1 (reducedCollisionSupport r) hrootHit
  have hV :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r v hcardv hdropv r.val.1 hAsub hAv
  have hU :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r u hcardu hdropu r.val.1 hAsub hAu
  rw [pairedRestorationFanValueUnion, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  exact ⟨hRoot.mono Finset.Subset.rfl (by
      rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]),
    hV.mono Finset.Subset.rfl
      (restorationFanForcedValueSlice_subset_fan r v j),
    hU.mono Finset.Subset.rfl
      (restorationFanForcedValueSlice_subset_fan r u k)⟩

/-- The value-level intersection of the two root upper faces is exactly the
upper face of the full root support, hence has cardinality `w_r`. -/
theorem card_positiveUpper_inter_negativeUpper_eq_weight
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r : ReducedSubsetSumCollision g h) :
    (blockedSignatureUpperValueLayer g r.val.1 ∩
        blockedSignatureUpperValueLayer g r.val.2).card =
      reducedCollisionWeight (m := m) r := by
  rw [blockedSignatureUpperValueLayer,
    blockedSignatureUpperValueLayer,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    blockedSignatureUpperSubsetLayers_inter,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer]
  rfl

/-- Paired lower packing enlarged by both root-tail upper faces. -/
noncomputable def pairedRestorationFanValueUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  (pairedRestorationFanValueUnion r v u j k ∪
      blockedSignatureUpperValueLayer g r.val.2) ∪
    blockedSignatureUpperValueLayer g r.val.1

/-- Exact inclusion-exclusion after adding the contamination-free positive
upper face. -/
theorem card_pairedRestorationFanValueUnionWithTailUpperFaces_add_weight
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hA : r.val.1.Nonempty)
    (hB : r.val.2.Nonempty)
    (hAv : (r.val.1 ∩ reducedCollisionSupport v).Nonempty)
    (hAu : (r.val.1 ∩ reducedCollisionSupport u).Nonempty)
    (hBv : (r.val.2 ∩ reducedCollisionSupport v).Nonempty)
    (hBu : (r.val.2 ∩ reducedCollisionSupport u).Nonempty) :
    (pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card +
        reducedCollisionWeight (m := m) r =
      (pairedRestorationFanValueUnion r v u j k).card +
        (blockedSignatureUpperValueLayer g r.val.2).card +
        (blockedSignatureUpperValueLayer g r.val.1).card := by
  let L := pairedRestorationFanValueUnion r v u j k
  let UB := blockedSignatureUpperValueLayer g r.val.2
  let UA := blockedSignatureUpperValueLayer g r.val.1
  let Tail := L ∪ UB
  let Total := Tail ∪ UA
  have hAL : Disjoint UA L := by
    simpa [UA, L] using
      positiveUpper_disjoint_pairedRestorationFanValueUnion
        hg r v u hcardv hcardu hdropv hdropu j k hA hAv hAu
  have hInter : Tail ∩ UA = UB ∩ UA := by
    ext x
    simp only [Tail, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxL | hxUB, hxUA⟩
      · exact False.elim (Finset.disjoint_left.mp hAL hxUA hxL)
      · exact ⟨hxUB, hxUA⟩
    · rintro ⟨hxUB, hxUA⟩
      exact ⟨Or.inr hxUB, hxUA⟩
  have hTailCard : Tail.card = L.card + UB.card := by
    have hBsub : r.val.2 ⊆ reducedCollisionSupport r := by
      intro b hb
      exact Finset.mem_union_right _ hb
    have hBroot : (r.val.2 ∩ reducedCollisionSupport r).Nonempty := by
      rcases hB with ⟨b, hb⟩
      exact ⟨b, Finset.mem_inter.mpr ⟨hb, hBsub hb⟩⟩
    have hRoot :=
      blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
        hg r.val.2 (reducedCollisionSupport r) hBroot
    have hV :=
      blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
        hg r v hcardv hdropv r.val.2 hBsub hBv
    have hU :=
      blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
        hg r u hcardu hdropu r.val.2 hBsub hBu
    have hdisj : Disjoint UB L := by
      dsimp only [UB, L]
      rw [pairedRestorationFanValueUnion,
        Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨hRoot.mono Finset.Subset.rfl (by
          rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]),
        hV.mono Finset.Subset.rfl
          (restorationFanForcedValueSlice_subset_fan r v j),
        hU.mono Finset.Subset.rfl
          (restorationFanForcedValueSlice_subset_fan r u k)⟩
    exact Finset.card_union_of_disjoint hdisj.symm
  have hdecomp := Finset.card_union_add_card_inter Tail UA
  change Total.card + (Tail ∩ UA).card = Tail.card + UA.card at hdecomp
  have hinterCard : (Tail ∩ UA).card =
      reducedCollisionWeight (m := m) r := by
    rw [hInter, Finset.inter_comm]
    exact card_positiveUpper_inter_negativeUpper_eq_weight hg r
  simpa [pairedRestorationFanValueUnionWithTailUpperFaces,
    Total, Tail, L, UB, UA,
    hTailCard, hinterCard] using hdecomp

/-- Exact doubled cardinality of the paired packing after adjoining both
root-tail upper faces. -/
theorem two_mul_card_pairedRestorationFanValueUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hjR : j ∈ reducedCollisionSupport r)
    (hkR : k ∈ reducedCollisionSupport r)
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hju : j ∈ reducedCollisionSupport u)
    (hA : r.val.1.Nonempty) (hB : r.val.2.Nonempty)
    (hAv : (r.val.1 ∩ reducedCollisionSupport v).Nonempty)
    (hAu : (r.val.1 ∩ reducedCollisionSupport u).Nonempty)
    (hBv : (r.val.2 ∩ reducedCollisionSupport v).Nonempty)
    (hBu : (r.val.2 ∩ reducedCollisionSupport u).Nonempty) :
    2 * (pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card =
      4 * reducedCollisionWeight (m := m) r -
          reducedCollisionWeight (m := m) v -
          reducedCollisionWeight (m := m) u +
        2 * 2 ^ (m - r.val.1.card) +
        2 * 2 ^ (m - r.val.2.card) := by
  have hfaces :=
    card_pairedRestorationFanValueUnionWithTailUpperFaces_add_weight
      hg r v u hcardv hcardu hdropv hdropu j k
        hA hB hAv hAu hBv hBu
  have hlower := two_mul_card_pairedRestorationFanValueUnion
    hg r v u hcardv hcardu hdropv hdropu j k
      hjR hkR hjv hku hju
  have hUpperA := card_blockedSignatureUpperValueLayer hg r.val.1
  have hUpperB := card_blockedSignatureUpperValueLayer hg r.val.2
  have hvle : reducedCollisionWeight (m := m) v ≤
      reducedCollisionWeight (m := m) r :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hcardv m)
  have hule : reducedCollisionWeight (m := m) u ≤
      reducedCollisionWeight (m := m) r :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hcardu m)
  rw [hUpperA, hUpperB] at hfaces
  omega

/-- Both-face packing remains inside the anchored subset-sum cube. -/
theorem pairedRestorationFanValueUnionWithTailUpperFaces_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    pairedRestorationFanValueUnionWithTailUpperFaces r v u j k ⊆
      subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxTail | hxA
  · rcases Finset.mem_union.mp hxTail with hxLower | hxB
    · exact pairedRestorationFanValueUnion_subset_subsetSumRange
        r v u j k hxLower
    · rw [blockedSignatureUpperValueLayer] at hxB
      rcases Finset.mem_image.mp hxB with ⟨S, hS, rfl⟩
      rw [subsetSumRange]
      exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩
  · rw [blockedSignatureUpperValueLayer] at hxA
    rcases Finset.mem_image.mp hxA with ⟨S, hS, rfl⟩
    rw [subsetSumRange]
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

section CriticalPairedPositiveFace

/-- In the live two-tail residual, canonical crossing forces both selected
targets to meet the root positive tail.  Consequently both upper faces can
be adjoined with no fan contamination.  If the positive tail is a singleton,
the construction is an exact near-tiling whose complement has doubled size
`w_v+w_u`. -/
theorem genuineDominant_two_tail_exists_pairedRestorationFan_twoFace_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ j k : Fin n,
    ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      j ≠ k ∧ r.val.2 = {j, k} ∧
      v ∈ criticalCanonicalReducedCollisions g ∧
      u ∈ criticalCanonicalReducedCollisions g ∧ v ≠ u ∧
      j ∉ reducedCollisionSupport v ∧
      k ∉ reducedCollisionSupport u ∧
      k ∈ v.val.2 ∧ j ∈ u.val.2 ∧
      (r.val.1 ∩ v.val.2).Nonempty ∧
      (r.val.1 ∩ u.val.2).Nonempty ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      8 * reducedCollisionWeight (m := n) u ≤
        reducedCollisionWeight (m := n) r ∧
      2 * (pairedRestorationFanValueUnionWithTailUpperFaces
          r v u j k).card =
        4 * reducedCollisionWeight (m := n) r -
            reducedCollisionWeight (m := n) v -
            reducedCollisionWeight (m := n) u +
          2 * 2 ^ (n - r.val.1.card) + 2 * 2 ^ (n - 2) ∧
      pairedRestorationFanValueUnionWithTailUpperFaces r v u j k ⊆
        subsetSumRange g ∧
      4 * reducedCollisionWeight (m := n) r -
            reducedCollisionWeight (m := n) v -
            reducedCollisionWeight (m := n) u +
          2 * 2 ^ (n - r.val.1.card) + 2 * 2 ^ (n - 2) ≤
        2 * 2 ^ n ∧
      (r.val.1.card = 1 →
        2 * (pairedRestorationFanValueUnionWithTailUpperFaces
            r v u j k).card +
              reducedCollisionWeight (m := n) v +
              reducedCollisionWeight (m := n) u = 2 * 2 ^ n ∧
        2 * (subsetSumRange g \
            pairedRestorationFanValueUnionWithTailUpperFaces
              r v u j k).card =
          reducedCollisionWeight (m := n) v +
            reducedCollisionWeight (m := n) u) := by
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
  obtain ⟨j, k, v, u, _z, hjk, hBset, hvtarget, hutarget, hvu,
      hjv, hku, hkvB, hjuB, _hzv, _hzu, _hzr, _hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with
    ⟨jv, hjvInc⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with
    ⟨ku, hkuInc⟩
  have hjvInc' := mem_canonicalSupportEscapeIncidences_iff.mp hjvInc
  have hkuInc' := mem_canonicalSupportEscapeIncidences_iff.mp hkuInc
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh :=
    hjvInc'.2.1
  have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh :=
    hkuInc'.2.1
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hvcanonical
  have hucritical : u ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hucanonical
  have hjB : j ∈ r.val.2 := by rw [hBset]; simp
  have hkB : k ∈ r.val.2 := by rw [hBset]; simp
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hkR : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hkB
  have hvr : v ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r v hjvInc'.1 hjvInc'.2.2.1
  have hur : u ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r u hkuInc'.1 hkuInc'.2.2.1
  have hvall := genuineDominant_two_tail_all_other_eighthWeight_growth
    hqodd g hg r hr hres hBcard v hvcritical hvr
  have huall := genuineDominant_two_tail_all_other_eighthWeight_growth
    hqodd g hg r hr hres hBcard u hucritical hur
  have hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by omega
  have hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card := by omega
  have hdropv : (reducedCollisionDroppedSupport r v).Nonempty :=
    ⟨j, Finset.mem_sdiff.mpr ⟨hjR, hjv⟩⟩
  have hdropu : (reducedCollisionDroppedSupport r u).Nonempty :=
    ⟨k, Finset.mem_sdiff.mpr ⟨hkR, hku⟩⟩
  have hju : j ∈ reducedCollisionSupport u :=
    Finset.mem_union_right _ hjuB
  have hAvNeg :=
    positiveTail_inter_targetNegativeTail_of_drops_one_contains_other
      hg hh (half_ne_zero hN hM) r v hr' hvcanonical
        j k hBset hjv hkvB
  have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hBset
  have hAuNeg :=
    positiveTail_inter_targetNegativeTail_of_drops_one_contains_other
      hg hh (half_ne_zero hN hM) r u hr' hucanonical
        k j hBswap hku hjuB
  have hAv : (r.val.1 ∩ reducedCollisionSupport v).Nonempty := by
    rcases hAvNeg with ⟨a, ha⟩
    exact ⟨a, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp ha).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp ha).2⟩⟩
  have hAu : (r.val.1 ∩ reducedCollisionSupport u).Nonempty := by
    rcases hAuNeg with ⟨a, ha⟩
    exact ⟨a, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp ha).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp ha).2⟩⟩
  have hBv : (r.val.2 ∩ reducedCollisionSupport v).Nonempty :=
    ⟨k, Finset.mem_inter.mpr
      ⟨hkB, Finset.mem_union_right _ hkvB⟩⟩
  have hBu : (r.val.2 ∩ reducedCollisionSupport u).Nonempty :=
    ⟨j, Finset.mem_inter.mpr
      ⟨hjB, Finset.mem_union_right _ hjuB⟩⟩
  have hB : r.val.2.Nonempty := Finset.card_pos.mp (by omega)
  have hn : 1 ≤ n := by
    have hcardle : r.val.2.card ≤ n := by
      simpa using Finset.card_le_univ r.val.2
    omega
  have hA := genuineDominant_positiveTail_nonempty
    hn hqodd g hg r hr hres
  have hexact :=
    two_mul_card_pairedRestorationFanValueUnionWithTailUpperFaces
      hg r v u hcardv hcardu hdropv hdropu j k
        hjR hkR hjv hku hju hA hB hAv hAu hBv hBu
  rw [hBcard] at hexact
  have hsubset :=
    pairedRestorationFanValueUnionWithTailUpperFaces_subset_subsetSumRange
      r v u j k
  have hUle :
      (pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card ≤
        2 ^ n := by
    calc
      (pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card ≤
          (subsetSumRange g).card := Finset.card_le_card hsubset
      _ = 2 ^ n := card_subsetSumRange g hg
  have hambient :
      4 * reducedCollisionWeight (m := n) r -
            reducedCollisionWeight (m := n) v -
            reducedCollisionWeight (m := n) u +
          2 * 2 ^ (n - r.val.1.card) + 2 * 2 ^ (n - 2) ≤
        2 * 2 ^ n := by
    rw [← hexact]
    exact Nat.mul_le_mul_left 2 hUle
  have hsingleton : r.val.1.card = 1 →
      2 * (pairedRestorationFanValueUnionWithTailUpperFaces
          r v u j k).card +
            reducedCollisionWeight (m := n) v +
            reducedCollisionWeight (m := n) u = 2 * 2 ^ n ∧
      2 * (subsetSumRange g \
          pairedRestorationFanValueUnionWithTailUpperFaces
            r v u j k).card =
        reducedCollisionWeight (m := n) v +
          reducedCollisionWeight (m := n) u := by
    intro hAcard
    have hsupp : (reducedCollisionSupport r).card = 3 := by
      rw [reducedCollisionSupport,
        Finset.card_union_of_disjoint r.property.1, hAcard, hBcard]
    have hn3 : 3 ≤ n := by
      have hle := Finset.card_le_univ (reducedCollisionSupport r)
      simpa [hsupp] using hle
    have hrWeight : reducedCollisionWeight (m := n) r = 2 ^ (n - 3) := by
      change 2 ^ (n - (reducedCollisionSupport r).card) = _
      rw [hsupp]
    have hp1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
      norm_num
      ring
    have hp2 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
      rw [show n - 2 = (n - 3) + 1 by omega, pow_add]
      norm_num
      ring
    have hpn : 2 ^ n = 8 * 2 ^ (n - 3) := by
      rw [show n = (n - 3) + 3 by omega, pow_add]
      norm_num
      ring
    have hnear :
        2 * (pairedRestorationFanValueUnionWithTailUpperFaces
            r v u j k).card +
              reducedCollisionWeight (m := n) v +
              reducedCollisionWeight (m := n) u = 2 * 2 ^ n := by
      rw [hAcard, hrWeight, hp1, hp2] at hexact
      rw [hpn]
      omega
    have hcompCard :
        (subsetSumRange g \
          pairedRestorationFanValueUnionWithTailUpperFaces
            r v u j k).card =
          2 ^ n -
            (pairedRestorationFanValueUnionWithTailUpperFaces
              r v u j k).card := by
      rw [Finset.card_sdiff_of_subset hsubset, card_subsetSumRange g hg]
    constructor
    · exact hnear
    · rw [hcompCard]
      omega
  exact ⟨j, k, v, u, hjk, hBset, hvcritical, hucritical, hvu,
    hjv, hku, hkvB, hjuB, hAvNeg, hAuNeg,
    hvall.2.2, huall.2.2, hexact, hsubset, hambient, hsingleton⟩

end CriticalPairedPositiveFace

end MinModulus
