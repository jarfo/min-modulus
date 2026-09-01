/-
# Root-trace rigidity for positive upper faces

For a canonical root with singleton positive tail and unit imbalance, every
other canonical collision contains that singleton in its negative tail.  This
is forced directly by validity: applying the oriented collision-subtraction
lemma in the non-root-to-root direction leaves only an impossible imbalance
drop as the alternative.

Consequently every non-root positive tail is disjoint from the root positive
tail, and its positive upper face occupies exactly one half of the root
positive upper face.  Summed over the complete non-root family, the root-
positive component therefore owns exactly half of the total positive-upper
incidence mass, rather than an uncontrolled amount between one half and all.
-/
import MinModulus.G1PositiveUpperPairedOccupancy

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A singleton positive tail of unit imbalance is contained in the negative
tail of every distinct cardinality-oriented collision. -/
theorem singletonPositive_subset_negativeTail_of_unitImbalance
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hAcard : r.val.1.card = 1)
    (hunit : reducedCollisionImbalance r = 1)
    (hqr : q ≠ r) :
    r.val.1 ⊆ q.val.2 := by
  rcases reducedCollision_reverse_cross_or_imbalance_gap
      g hg hh0 q r hqcard hrcard (Ne.symm hqr) with hinter | hgap
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAcard
    have haB : a ∈ q.val.2 := by
      rcases hinter with ⟨x, hx⟩
      have hxa : x = a := by simpa [ha] using (Finset.mem_inter.mp hx).2
      exact hxa ▸ (Finset.mem_inter.mp hx).1
    intro x hx
    have hxa : x = a := by simpa [ha] using hx
    exact hxa ▸ haB
  · rw [hunit] at hgap
    omega

omit [DecidableEq G] in
/-- Hence the positive tails of the root and every distinct oriented
collision are disjoint. -/
theorem positiveTails_disjoint_of_singleton_unitImbalance
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hAcard : r.val.1.card = 1)
    (hunit : reducedCollisionImbalance r = 1)
    (hqr : q ≠ r) :
    Disjoint q.val.1 r.val.1 := by
  have hsub := singletonPositive_subset_negativeTail_of_unitImbalance
    g hg hh0 r q hrcard hqcard hAcard hunit hqr
  exact q.property.1.mono_right hsub

/-- Intersecting an upper face with a disjoint singleton upper face removes
exactly one free Boolean coordinate. -/
theorem two_mul_card_positiveUpper_inter_singletonUpper
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (C A : Finset (Fin m)) (hdisj : Disjoint C A)
    (hAcard : A.card = 1) :
    2 * (blockedSignatureUpperValueLayer g C ∩
        blockedSignatureUpperValueLayer g A).card =
      (blockedSignatureUpperValueLayer g C).card := by
  have hcardUnion : (C ∪ A).card = C.card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard]
  have hle : C.card + 1 ≤ m := by
    rw [← hcardUnion]
    simpa using Finset.card_le_univ (C ∪ A)
  rw [blockedSignatureUpperValueLayer,
    blockedSignatureUpperValueLayer,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    blockedSignatureUpperSubsetLayers_inter,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer,
    card_blockedSignatureSubsetLayer,
    hcardUnion]
  have hexp : m - C.card = (m - (C.card + 1)) + 1 := by omega
  rw [hexp, pow_succ]
  omega

/-- Positive-upper incidence mass falling in the root-positive upper face. -/
noncomputable def rootPositiveUpperOccupancyMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r : ReducedSubsetSumCollision g h) : ℕ :=
  F.sum (fun q ↦ (reducedCollisionPositiveUpperValueLayer q ∩
    blockedSignatureUpperValueLayer g r.val.1).card)

/-- If every family member has positive tail disjoint from the singleton
root tail, the root-positive component owns exactly half of the full
positive-upper incidence mass. -/
theorem two_mul_rootPositiveUpperOccupancyMass_eq_incidenceMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (r : ReducedSubsetSumCollision g h)
    (hAcard : r.val.1.card = 1)
    (hdisj : ∀ q ∈ F, Disjoint q.val.1 r.val.1) :
    2 * rootPositiveUpperOccupancyMass F r =
      reducedCollisionPositiveUpperIncidenceMass F := by
  classical
  rw [rootPositiveUpperOccupancyMass,
    reducedCollisionPositiveUpperIncidenceMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simpa [reducedCollisionPositiveUpperValueLayer] using
    two_mul_card_positiveUpper_inter_singletonUpper
      g hg q.val.1 r.val.1 (hdisj q hq) hAcard

section CriticalRootTrace

/-- In the critical singleton-positive/two-negative profile, every non-root
canonical collision contains the root positive singleton in its negative
tail.  The family-level root-positive incidence is therefore exactly one
half of all positive-upper incidence. -/
theorem critical_two_tail_nonroot_rootPositive_trace_and_occupancy
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    (∀ u ∈ F, r.val.1 ⊆ u.val.2 ∧ Disjoint u.val.1 r.val.1) ∧
      2 * rootPositiveUpperOccupancyMass F r =
        reducedCollisionPositiveUpperIncidenceMass F := by
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
  let F := criticalCanonicalNonrootCollisions g r
  have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hrcard : r.val.1.card ≤ r.val.2.card :=
    canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hrcanonical)
  have hunit : reducedCollisionImbalance r = 1 := by
    simp [reducedCollisionImbalance, hAcard, hBcard]
  have htrace : ∀ u ∈ F,
      r.val.1 ⊆ u.val.2 ∧ Disjoint u.val.1 r.val.1 := by
    intro u hu
    have huErase : u ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hu
    have hur := (Finset.mem_erase.mp huErase).1
    have hucritical := (Finset.mem_erase.mp huErase).2
    have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hucritical
    have hucard : u.val.1.card ≤ u.val.2.card :=
      canonicalReducedCollision_card_le
        (mem_canonicalReducedCollisions_iff.mp hucanonical)
    have hsub := singletonPositive_subset_negativeTail_of_unitImbalance
      g hg (half_ne_zero hN hM) r u hrcard hucard hAcard hunit hur
    exact ⟨hsub, u.property.1.mono_right hsub⟩
  exact ⟨htrace,
    two_mul_rootPositiveUpperOccupancyMass_eq_incidenceMass
      g hg F r hAcard (fun u hu ↦ (htrace u hu).2)⟩

end CriticalRootTrace

end MinModulus
