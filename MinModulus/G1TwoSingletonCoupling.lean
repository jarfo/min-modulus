/-
# Coupling the two singleton-fiber escape targets

The minimum-fiber parameter package still permits a root with two negative
tail coordinates and one selected singleton fiber for each.  This file uses
structure that the one-root count cannot see.  The two signatures have
distinct realizing targets.  Canonical negative tails are pairwise
intersecting, while one target omits the first root-tail coordinate and the
other omits the second.  Their common negative-tail coordinate must therefore
lie outside the root negative tail.

This is the first multi-root constraint on the surviving symbolic
`(|A_r|,|B_r|)=(1,2)` profile.
-/
import MinModulus.G1MinimumFiberBudget

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Two distinct target signatures whose root-tail fibers are the two
singletons have distinct realizing targets, and those targets share a
negative-tail coordinate outside the root negative tail. -/
theorem two_singleton_escapeTargets_common_negative_outside
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q u : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ v ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card)
    {j k : Fin m} (hjk : j ≠ k) (hB : r.val.2 = {j, k})
    (hq : q ∈ canonicalSupportEscapeTargets hh r)
    (hu : u ∈ canonicalSupportEscapeTargets hh r)
    (hqfiber : r.val.2 \ restoredCollisionBlockedSupport r q = {j})
    (hufiber : r.val.2 \ restoredCollisionBlockedSupport r u = {k}) :
    q ≠ u ∧ k ∈ q.val.2 ∧ j ∈ u.val.2 ∧ ∃ z : Fin m,
      z ∈ q.val.2 ∧ z ∈ u.val.2 ∧ z ∉ r.val.2 := by
  classical
  rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨jq, hjq⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hu with ⟨ju, hju⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hju' := mem_canonicalSupportEscapeIncidences_iff.mp hju
  have hqu : q ≠ u := by
    intro heq
    have hsingle : ({j} : Finset (Fin m)) = {k} := by
      calc
        {j} = r.val.2 \ restoredCollisionBlockedSupport r q :=
          hqfiber.symm
        _ = r.val.2 \ restoredCollisionBlockedSupport r u := by rw [heq]
        _ = {k} := hufiber
    exact hjk (Finset.singleton_inj.mp hsingle)
  have hkq : k ∈ q.val.2 := by
    have hinter := canonicalReducedCollision_negative_tails_inter
      g hg hh hh0 r q
        (mem_canonicalReducedCollisions_iff.mp hr)
        (mem_canonicalReducedCollisions_iff.mp hjq'.2.1)
    obtain ⟨x, hx⟩ := hinter
    have hxB := (Finset.mem_inter.mp hx).1
    have hxq := (Finset.mem_inter.mp hx).2
    have hxroot : x ∈ reducedCollisionSupport r :=
      Finset.mem_union_right _ hxB
    have hxqSupport : x ∈ reducedCollisionSupport q :=
      Finset.mem_union_right _ hxq
    have hxBlocked : x ∈ restoredCollisionBlockedSupport r q :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r q (hrmin q hjq'.2.1) hxroot).2 hxqSupport
    have hxjk : x = j ∨ x = k := by
      rw [hB] at hxB
      simpa using hxB
    rcases hxjk with hxj | hxk
    · have hxdiff : x ∈ r.val.2 \
          restoredCollisionBlockedSupport r q := by
        rw [hqfiber]
        simp [hxj]
      exact False.elim ((Finset.mem_sdiff.mp hxdiff).2 hxBlocked)
    · simpa [hxk] using hxq
  have hjuTail : j ∈ u.val.2 := by
    have hinter := canonicalReducedCollision_negative_tails_inter
      g hg hh hh0 r u
        (mem_canonicalReducedCollisions_iff.mp hr)
        (mem_canonicalReducedCollisions_iff.mp hju'.2.1)
    obtain ⟨x, hx⟩ := hinter
    have hxB := (Finset.mem_inter.mp hx).1
    have hxu := (Finset.mem_inter.mp hx).2
    have hxroot : x ∈ reducedCollisionSupport r :=
      Finset.mem_union_right _ hxB
    have hxuSupport : x ∈ reducedCollisionSupport u :=
      Finset.mem_union_right _ hxu
    have hxBlocked : x ∈ restoredCollisionBlockedSupport r u :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r u (hrmin u hju'.2.1) hxroot).2 hxuSupport
    have hxjk : x = j ∨ x = k := by
      rw [hB] at hxB
      simpa using hxB
    rcases hxjk with hxj | hxk
    · simpa [hxj] using hxu
    · have hxdiff : x ∈ r.val.2 \
          restoredCollisionBlockedSupport r u := by
        rw [hufiber]
        simp [hxk]
      exact False.elim ((Finset.mem_sdiff.mp hxdiff).2 hxBlocked)
  have hinter := canonicalReducedCollision_negative_tails_inter
    g hg hh hh0 q u
      (mem_canonicalReducedCollisions_iff.mp hjq'.2.1)
      (mem_canonicalReducedCollisions_iff.mp hju'.2.1)
  obtain ⟨z, hz⟩ := hinter
  have hzq := (Finset.mem_inter.mp hz).1
  have hzu := (Finset.mem_inter.mp hz).2
  refine ⟨hqu, hkq, hjuTail, z, hzq, hzu, ?_⟩
  intro hzB
  have hzroot : z ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hzB
  have hzqSupport : z ∈ reducedCollisionSupport q :=
    Finset.mem_union_right _ hzq
  have hzuSupport : z ∈ reducedCollisionSupport u :=
    Finset.mem_union_right _ hzu
  have hzqBlocked : z ∈ restoredCollisionBlockedSupport r q :=
    (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r q (hrmin q hjq'.2.1) hzroot).2 hzqSupport
  have hzuBlocked : z ∈ restoredCollisionBlockedSupport r u :=
    (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r u (hrmin u hju'.2.1) hzroot).2 hzuSupport
  have hzjk : z = j ∨ z = k := by
    rw [hB] at hzB
    simpa using hzB
  rcases hzjk with hzj | hzk
  · have hzdiff : z ∈ r.val.2 \ restoredCollisionBlockedSupport r q := by
      rw [hqfiber]
      simp [hzj]
    exact (Finset.mem_sdiff.mp hzdiff).2 hzqBlocked
  · have hzdiff : z ∈ r.val.2 \ restoredCollisionBlockedSupport r u := by
      rw [hufiber]
      simp [hzk]
    exact (Finset.mem_sdiff.mp hzdiff).2 hzuBlocked

/-- A three-edge omission fan is either the exact triangle or one of its two
new target tails has at least three coordinates. -/
theorem two_singleton_omissionFan_exact_triangle_or_tail_growth
    (Q U B : Finset (Fin m)) {j k z : Fin m}
    (hjB : j ∈ B) (hkB : k ∈ B) (hzB : z ∉ B)
    (hkQ : k ∈ Q) (hzQ : z ∈ Q)
    (hjU : j ∈ U) (hzU : z ∈ U) :
    (Q = {k, z} ∧ U = {j, z}) ∨ 3 ≤ Q.card ∨ 3 ≤ U.card := by
  classical
  have hzk : z ≠ k := by
    intro hzk
    subst z
    exact hzB hkB
  have hzj : z ≠ j := by
    intro hzj
    subst z
    exact hzB hjB
  by_cases hQ : Q = {k, z}
  · by_cases hU : U = {j, z}
    · exact Or.inl ⟨hQ, hU⟩
    · apply Or.inr (Or.inr ?_)
      have hsub : {j, z} ⊆ U := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hjU
        · exact hzU
      have hlt := Finset.card_lt_card
        (hsub.ssubset_of_ne (Ne.symm hU))
      have hpair : ({j, z} : Finset (Fin m)).card = 2 := by
        simp [Ne.symm hzj]
      omega
  · apply Or.inr (Or.inl ?_)
    have hsub : {k, z} ⊆ Q := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hkQ
      · exact hzQ
    have hlt := Finset.card_lt_card
      (hsub.ssubset_of_ne (Ne.symm hQ))
    have hpair : ({k, z} : Finset (Fin m)).card = 2 := by
      simp [Ne.symm hzk]
    omega

/-- In any support-minimal escape-covered collision with a two-coordinate
negative tail, the two minimum-fiber selected signatures yield distinct
actual targets sharing a negative coordinate outside that tail. -/
theorem exists_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ v ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hBcard : r.val.2.card = 2) :
    ∃ j k : Fin m, ∃ q u : ReducedSubsetSumCollision g h, ∃ z : Fin m,
      j ≠ k ∧ r.val.2 = {j, k} ∧
      q ∈ canonicalSupportEscapeTargets hh r ∧
      u ∈ canonicalSupportEscapeTargets hh r ∧ q ≠ u ∧
      k ∈ q.val.2 ∧ j ∈ u.val.2 ∧
      z ∈ q.val.2 ∧ z ∈ u.val.2 ∧ z ∉ r.val.2 ∧
      ((q.val.2 = {k, z} ∧ u.val.2 = {j, z}) ∨
        3 ≤ q.val.2.card ∨ 3 ≤ u.val.2.card) := by
  classical
  obtain ⟨j, k, hjk, hB⟩ := Finset.card_eq_two.mp hBcard
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let Cj := selectedCoveringSignature S r.val.2 j
  let Ck := selectedCoveringSignature S r.val.2 k
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hkB : k ∈ r.val.2 := by rw [hB]; simp
  have hjC := selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S r.val.2 hcover' hjB
  have hkC := selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S r.val.2 hcover' hkB
  have hkCj : k ∈ Cj := by
    have hmeet := sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hjC.1
    obtain ⟨x, hx⟩ := hmeet
    have hxB := (Finset.mem_inter.mp hx).1
    have hxCj := (Finset.mem_inter.mp hx).2
    have hx : x = j ∨ x = k := by
      rw [hB] at hxB
      simpa using hxB
    rcases hx with rfl | rfl
    · exact False.elim ((Finset.mem_sdiff.mp hjC.2).2 hxCj)
    · exact hxCj
  have hjCk : j ∈ Ck := by
    have hmeet := sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hkC.1
    obtain ⟨x, hx⟩ := hmeet
    have hxB := (Finset.mem_inter.mp hx).1
    have hxCk := (Finset.mem_inter.mp hx).2
    have hx : x = j ∨ x = k := by
      rw [hB] at hxB
      simpa using hxB
    rcases hx with rfl | rfl
    · exact hxCk
    · exact False.elim ((Finset.mem_sdiff.mp hkC.2).2 hxCk)
  have hCjfiber : r.val.2 \ Cj = {j} := by
    rw [hB]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxj | hxk, hxnot⟩
      · exact hxj
      · exact False.elim (hxnot (hxk ▸ hkCj))
    · intro hxj
      subst x
      exact ⟨Or.inl rfl, (Finset.mem_sdiff.mp hjC.2).2⟩
  have hCkfiber : r.val.2 \ Ck = {k} := by
    rw [hB]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxj | hxk, hxnot⟩
      · exact False.elim (hxnot (hxj ▸ hjCk))
      · exact hxk
    · intro hxk
      subst x
      exact ⟨Or.inr rfl, (Finset.mem_sdiff.mp hkC.2).2⟩
  let q := realizingEscapeTargetForSignature hh r Cj
  let u := realizingEscapeTargetForSignature hh r Ck
  have hqspec := realizingEscapeTargetForSignature_mem_and_blockedSupport
    hh r hjC.1
  have huspec := realizingEscapeTargetForSignature_mem_and_blockedSupport
    hh r hkC.1
  have hqfiber : r.val.2 \ restoredCollisionBlockedSupport r q = {j} := by
    rw [hqspec.2]
    exact hCjfiber
  have hufiber : r.val.2 \ restoredCollisionBlockedSupport r u = {k} := by
    rw [huspec.2]
    exact hCkfiber
  obtain ⟨hqu, hkq, hju, z, hzq, hzu, hzB⟩ :=
    two_singleton_escapeTargets_common_negative_outside
      hg hh hh0 r q u hr hrmin hjk hB hqspec.1 huspec.1 hqfiber hufiber
  have hsplit := two_singleton_omissionFan_exact_triangle_or_tail_growth
    q.val.2 u.val.2 r.val.2 hjB hkB hzB hkq hzq hju hzu
  exact ⟨j, k, q, u, z, hjk, hB, hqspec.1, huspec.1,
    hqu, hkq, hju, hzq, hzu, hzB, hsplit⟩

section CriticalTwoSingletonCoupling

/-- Critical specialization: every genuine dominant residual with
`|B_r|=2` contains two distinct selected escape targets with a common
negative-tail coordinate outside `B_r`. -/
theorem genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
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
    ∃ j k : Fin n,
      ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      ∃ z : Fin n,
        j ≠ k ∧ r.val.2 = {j, k} ∧
        v ∈ canonicalSupportEscapeTargets hh r ∧
        u ∈ canonicalSupportEscapeTargets hh r ∧ v ≠ u ∧
        k ∈ v.val.2 ∧ j ∈ u.val.2 ∧
        z ∈ v.val.2 ∧ z ∈ u.val.2 ∧ z ∉ r.val.2 ∧
        ((v.val.2 = {k, z} ∧ u.val.2 = {j, z}) ∨
          3 ≤ v.val.2.card ∨ 3 ≤ u.val.2.card) := by
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
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ v ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2 := by
    simpa [hh] using hdominant.2.2.2.2.2.2.2.2.2.1
  simpa [hh] using
    exists_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hg hh (half_ne_zero hN hM) r hr' hrmin hcover hBcard

end CriticalTwoSingletonCoupling

end MinModulus
