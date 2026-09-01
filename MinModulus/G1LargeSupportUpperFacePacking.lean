/-
# Global positive-upper packing for the large-support residual

After the live-profile obstruction, every non-root canonical collision has
support at least six.  Canonical orientation gives `|A_q| ≤ |B_q|`, hence
`|B_q| ≥ 3`.  The positive upper face forcing `A_q` has cardinality

  `2^(m-|A_q|) = 2^|B_q| * w_q`,

so it carries at least eight times the native padding weight `w_q`.

This file makes that expansion simultaneous over the whole non-root family.
Positive tails of distinct reduced collisions are distinct under validity.
After stratifying by `|A_q|`, all upper faces have equal size and distinct
members overlap in at most half a face.  The finite-family second-moment
bound therefore gives, in every stratum,

  `16 * (stratum padding weight) ≤
      (stratum cardinality + 1) * (upper-face union cardinality)`.

The strata partition the complete non-root family exactly.  Thus the next
global step no longer needs to discover the factor-eight supply; it must
control duplication between different positive-cardinality strata and the
contamination of their union with the existing paired restoration packing.
-/
import MinModulus.G1TransportLiveProfileObstruction

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Members of a reduced-collision family with a fixed positive-tail
cardinality. -/
noncomputable def reducedCollisionPositiveCardStratum
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact F.filter (fun q ↦ q.val.1.card = a)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionPositiveCardStratum_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)} {a : ℕ}
    {q : ReducedSubsetSumCollision g h} :
    q ∈ reducedCollisionPositiveCardStratum F a ↔
      q ∈ F ∧ q.val.1.card = a := by
  classical
  simp [reducedCollisionPositiveCardStratum]

/-- Union of all positive upper value faces in one positive-cardinality
stratum. -/
noncomputable def reducedCollisionPositiveUpperValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ) : Finset G := by
  classical
  exact (reducedCollisionPositiveCardStratum F a).biUnion
    (fun q ↦ blockedSignatureUpperValueLayer g q.val.1)

/-- Every stratum upper-face union lies in the anchored subset-sum cube. -/
theorem reducedCollisionPositiveUpperValueUnion_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ) :
    reducedCollisionPositiveUpperValueUnion F a ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨q, hq, hxq⟩
  rw [blockedSignatureUpperValueLayer] at hxq
  rcases Finset.mem_image.mp hxq with ⟨S, hS, rfl⟩
  rw [subsetSumRange]
  exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

/-- Total positive-upper incidence mass, retaining multiplicity between
different faces. -/
noncomputable def reducedCollisionPositiveUpperIncidenceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ :=
  F.sum (fun q ↦ (blockedSignatureUpperValueLayer g q.val.1).card)

omit [DecidableEq G] in
/-- Under validity, a reduced collision is determined by its positive tail.
The negative tail then follows from injectivity of anchored subset sums. -/
theorem reducedSubsetSumCollision_eq_of_left_eq
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hleft : q.val.1 = u.val.1) : q = u := by
  have hrightSum : ssum g q.val.2 = ssum g u.val.2 := by
    have hq := q.property.2
    have hu := u.property.2
    rw [hleft, hu] at hq
    exact add_right_cancel hq.symm
  have hright : q.val.2 = u.val.2 := ssum_injective g hg hrightSum
  apply Subtype.ext
  exact Prod.ext hleft hright

/-- Exact expansion identity: the positive upper face is the native padding
face multiplied by `2^|B_q|`. -/
theorem pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q : ReducedSubsetSumCollision g h) :
    2 ^ q.val.2.card * reducedCollisionWeight (m := m) q =
      (blockedSignatureUpperValueLayer g q.val.1).card := by
  have hsupport : (q.val.1 ∪ q.val.2).card =
      q.val.1.card + q.val.2.card := by
    rw [Finset.card_union_of_disjoint q.property.1]
  have hsupportLe : q.val.1.card + q.val.2.card ≤ m := by
    rw [← hsupport]
    simpa using Finset.card_le_univ (q.val.1 ∪ q.val.2)
  rw [card_blockedSignatureUpperValueLayer hg,
    reducedCollisionWeight, hsupport]
  rw [show m - q.val.1.card =
      q.val.2.card + (m - (q.val.1.card + q.val.2.card)) by omega,
    pow_add]

omit [DecidableEq G] in
/-- Support at least six plus canonical cardinality orientation forces at
least three negative coordinates. -/
theorem three_le_negativeCard_of_six_le_support_of_positiveCard_le
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h)
    (hcanonical : q.val.1.card ≤ q.val.2.card)
    (hsix : 6 ≤ (reducedCollisionSupport q).card) :
    3 ≤ q.val.2.card := by
  have hsupport : (reducedCollisionSupport q).card =
      q.val.1.card + q.val.2.card := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint q.property.1]
  omega

/-- Every large-support canonically oriented collision supplies at least
eight times its padding weight in its positive upper face. -/
theorem eight_mul_reducedCollisionWeight_le_positiveUpper_card
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q : ReducedSubsetSumCollision g h)
    (hcanonical : q.val.1.card ≤ q.val.2.card)
    (hsix : 6 ≤ (reducedCollisionSupport q).card) :
    8 * reducedCollisionWeight (m := m) q ≤
      (blockedSignatureUpperValueLayer g q.val.1).card := by
  have hthree :=
    three_le_negativeCard_of_six_le_support_of_positiveCard_le
      q hcanonical hsix
  have hpow : 8 ≤ 2 ^ q.val.2.card := by
    simpa using Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) hthree
  rw [← pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card
    hg q]
  exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) q) hpow

/-- The factor-eight supply sums over an arbitrary finite large-support,
canonically oriented family. -/
theorem eight_mul_sum_weight_le_positiveUpperIncidenceMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    8 * F.sum (reducedCollisionWeight (m := m)) ≤
      reducedCollisionPositiveUpperIncidenceMass F := by
  rw [reducedCollisionPositiveUpperIncidenceMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  exact eight_mul_reducedCollisionWeight_le_positiveUpper_card
    hg q (hcanonical q hq) (hsix q hq)

/-- Distinct equal-cardinality forced sets give positive upper faces with at
most half-face intersection. -/
theorem two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_card_eq_of_ne
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (C D : Finset (Fin m))
    (hcard : C.card = D.card) (hne : C ≠ D) :
    2 * (blockedSignatureUpperValueLayer g C ∩
        blockedSignatureUpperValueLayer g D).card ≤
      2 ^ (m - C.card) := by
  have hproper : C ⊂ C ∪ D := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_left, ?_⟩
    intro heq
    have hDC : D ⊆ C := by
      intro x hxD
      have hx : x ∈ C ∪ D := Finset.mem_union_right _ hxD
      rwa [← heq] at hx
    have hDCeq : D = C :=
      Finset.eq_of_subset_of_card_le hDC (by omega)
    exact hne hDCeq.symm
  have hcardStep : C.card + 1 ≤ (C ∪ D).card := by
    have := Finset.card_lt_card hproper
    omega
  have hunionLe : (C ∪ D).card ≤ m := by
    simpa using Finset.card_le_univ (C ∪ D)
  have hexponent : m - (C ∪ D).card + 1 ≤ m - C.card := by omega
  have hpow := Nat.pow_le_pow_right
    (by norm_num : 0 < (2 : ℕ)) hexponent
  rw [blockedSignatureUpperValueLayer,
    blockedSignatureUpperValueLayer,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    blockedSignatureUpperSubsetLayers_inter,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer]
  simpa [pow_succ, Nat.mul_comm] using hpow

/-- Exact size of every upper face in one positive-cardinality stratum. -/
theorem card_positiveUpperValueLayer_of_mem_stratum
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ)
    (q : ReducedSubsetSumCollision g h)
    (hq : q ∈ reducedCollisionPositiveCardStratum F a) :
    (blockedSignatureUpperValueLayer g q.val.1).card = 2 ^ (m - a) := by
  have hqa := (mem_reducedCollisionPositiveCardStratum_iff.mp hq).2
  rw [card_blockedSignatureUpperValueLayer hg, hqa]

/-- The positive upper faces in a fixed-cardinality stratum are pairwise
half-overlapping. -/
theorem two_mul_positiveUpperValueLayers_inter_le_of_mem_stratum
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ)
    (q : ReducedSubsetSumCollision g h)
    (hq : q ∈ reducedCollisionPositiveCardStratum F a)
    (u : ReducedSubsetSumCollision g h)
    (hu : u ∈ reducedCollisionPositiveCardStratum F a)
    (hqu : q ≠ u) :
    2 * (blockedSignatureUpperValueLayer g q.val.1 ∩
        blockedSignatureUpperValueLayer g u.val.1).card ≤
      2 ^ (m - a) := by
  have hqcard := (mem_reducedCollisionPositiveCardStratum_iff.mp hq).2
  have hucard := (mem_reducedCollisionPositiveCardStratum_iff.mp hu).2
  have hleft : q.val.1 ≠ u.val.1 := by
    intro hEq
    exact hqu (reducedSubsetSumCollision_eq_of_left_eq hg q u hEq)
  simpa [hqcard] using
    two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_card_eq_of_ne
      hg q.val.1 u.val.1 (hqcard.trans hucard.symm) hleft

/-- Second-moment packing of every fixed positive-cardinality stratum. -/
theorem two_mul_card_mul_positiveUpperSize_le_succ_mul_union_card
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ) :
    2 * (reducedCollisionPositiveCardStratum F a).card * 2 ^ (m - a) ≤
      ((reducedCollisionPositiveCardStratum F a).card + 1) *
        (reducedCollisionPositiveUpperValueUnion F a).card := by
  classical
  let S := reducedCollisionPositiveCardStratum F a
  let L : ReducedSubsetSumCollision g h → Finset G :=
    fun q ↦ blockedSignatureUpperValueLayer g q.val.1
  by_cases hS : S.Nonempty
  · have hpack := two_mul_card_mul_weight_le_succ_mul_familyUnion_card
      S L (2 ^ (m - a)) hS (by positivity)
      (fun q hq ↦ card_positiveUpperValueLayer_of_mem_stratum
        hg F a q (by simpa [S] using hq))
      (fun q hq u hu hqu ↦
        two_mul_positiveUpperValueLayers_inter_le_of_mem_stratum
          hg F a q (by simpa [S] using hq)
            u (by simpa [S] using hu) hqu)
    simpa [S, L, reducedCollisionPositiveUpperValueUnion] using hpack
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hEmpty, reducedCollisionPositiveUpperValueUnion]

/-- Load-bearing stratum inequality: support-six factor-eight expansion plus
the global half-overlap packing gives a sixteen-to-one weighted bound. -/
theorem sixteen_mul_positiveCardStratumWeight_le_succ_mul_upperUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ)
    (hcanonical : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    16 * (reducedCollisionPositiveCardStratum F a).sum
        (reducedCollisionWeight (m := m)) ≤
      ((reducedCollisionPositiveCardStratum F a).card + 1) *
        (reducedCollisionPositiveUpperValueUnion F a).card := by
  classical
  let S := reducedCollisionPositiveCardStratum F a
  have hmass : 8 * S.sum (reducedCollisionWeight (m := m)) ≤
      S.card * 2 ^ (m - a) := by
    calc
      8 * S.sum (reducedCollisionWeight (m := m)) =
          S.sum (fun q ↦ 8 * reducedCollisionWeight (m := m) q) := by
        rw [Finset.mul_sum]
      _ ≤ S.sum (fun q ↦
          (blockedSignatureUpperValueLayer g q.val.1).card) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' := (mem_reducedCollisionPositiveCardStratum_iff.mp hq).1
        exact eight_mul_reducedCollisionWeight_le_positiveUpper_card
          hg q (hcanonical q hq') (hsix q hq')
      _ = S.card * 2 ^ (m - a) := by
        apply Finset.sum_const_nat
        intro q hq
        exact card_positiveUpperValueLayer_of_mem_stratum
          hg F a q (by simpa [S] using hq)
  have hpack := two_mul_card_mul_positiveUpperSize_le_succ_mul_union_card
    hg F a
  change 16 * S.sum (reducedCollisionWeight (m := m)) ≤
    (S.card + 1) * (reducedCollisionPositiveUpperValueUnion F a).card
  calc
    16 * S.sum (reducedCollisionWeight (m := m)) =
        2 * (8 * S.sum (reducedCollisionWeight (m := m))) := by ring
    _ ≤ 2 * (S.card * 2 ^ (m - a)) := Nat.mul_le_mul_left 2 hmass
    _ = 2 * S.card * 2 ^ (m - a) := by ring
    _ ≤ (S.card + 1) *
        (reducedCollisionPositiveUpperValueUnion F a).card := by
      simpa [S] using hpack

/-- Numerical full-cube form of the stratum packing. -/
theorem sixteen_mul_positiveCardStratumWeight_le_succ_mul_two_pow
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) (a : ℕ)
    (hcanonical : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    16 * (reducedCollisionPositiveCardStratum F a).sum
        (reducedCollisionWeight (m := m)) ≤
      ((reducedCollisionPositiveCardStratum F a).card + 1) * 2 ^ m := by
  have hpack := sixteen_mul_positiveCardStratumWeight_le_succ_mul_upperUnion
    hg F a hcanonical hsix
  have hunion : (reducedCollisionPositiveUpperValueUnion F a).card ≤
      (subsetSumRange g).card := Finset.card_le_card
        (reducedCollisionPositiveUpperValueUnion_subset_subsetSumRange F a)
  rw [card_subsetSumRange g hg] at hunion
  exact hpack.trans (Nat.mul_le_mul_left _ hunion)

omit [DecidableEq G] in
/-- Positive-cardinality strata partition an arbitrary reduced-collision
family exactly, including padding weights. -/
theorem sum_positiveCardStratumWeights_eq_sum_weight
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    ∑ a ∈ Finset.range (m + 1),
        (reducedCollisionPositiveCardStratum F a).sum
          (reducedCollisionWeight (m := m)) =
      F.sum (reducedCollisionWeight (m := m)) := by
  classical
  have hall : F.filter (fun q ↦ q.val.1.card ∈ Finset.range (m + 1)) = F := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    simp only [Finset.mem_range]
    have hsub : q.val.1 ⊆ reducedCollisionSupport q := by
      intro x hx
      exact Finset.mem_union_left _ hx
    have hle : q.val.1.card ≤ m :=
      (Finset.card_le_card hsub).trans
        (by simpa using Finset.card_le_univ (reducedCollisionSupport q))
    omega
  have hfiber :=
    Finset.sum_fiberwise_eq_sum_filter F (Finset.range (m + 1))
      (fun q : ReducedSubsetSumCollision g h ↦ q.val.1.card)
      (reducedCollisionWeight (m := m))
  change (∑ a ∈ Finset.range (m + 1),
      (F.filter (fun q ↦ q.val.1.card = a)).sum
        (reducedCollisionWeight (m := m))) =
    (F.filter (fun q ↦ q.val.1.card ∈ Finset.range (m + 1))).sum
      (reducedCollisionWeight (m := m)) at hfiber
  rw [hall] at hfiber
  simpa [reducedCollisionPositiveCardStratum] using hfiber

section CriticalLargeSupportFamily

/-- The complete non-root critical canonical family. -/
noncomputable def criticalCanonicalNonrootCollisions
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  classical
  exact (criticalCanonicalReducedCollisions g).erase r

/-- Milestone 2ct: in the live-root genuine residual, the whole non-root
canonical family simultaneously has factor-eight positive-upper supply,
partitions exactly by positive cardinality, and satisfies the sharp
second-moment packing inequality in every stratum. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    8 * F.sum (reducedCollisionWeight (m := n)) ≤
        reducedCollisionPositiveUpperIncidenceMass F ∧
      (∑ a ∈ Finset.range (n + 1),
          (reducedCollisionPositiveCardStratum F a).sum
            (reducedCollisionWeight (m := n)) =
        F.sum (reducedCollisionWeight (m := n))) ∧
      ∀ a : ℕ,
        16 * (reducedCollisionPositiveCardStratum F a).sum
            (reducedCollisionWeight (m := n)) ≤
          ((reducedCollisionPositiveCardStratum F a).card + 1) *
            (reducedCollisionPositiveUpperValueUnion F a).card := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  have hmem : ∀ v ∈ F,
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r := by
    intro v hv
    have hv' : v ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hv
    have hv'' := Finset.mem_erase.mp hv'
    exact ⟨hv''.2, hv''.1⟩
  have hcanonical : ∀ v ∈ F, v.val.1.card ≤ v.val.2.card := by
    intro v hv
    have hvcritical := (hmem v hv).1
    have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hvcritical
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  refine ⟨eight_mul_sum_weight_le_positiveUpperIncidenceMass
      hg F hcanonical hsix,
    sum_positiveCardStratumWeights_eq_sum_weight F, ?_⟩
  intro a
  exact sixteen_mul_positiveCardStratumWeight_le_succ_mul_upperUnion
    hg F a hcanonical hsix

/-- The previous theorem uses exactly the already proved quarter-star budget:
the non-root family remains bounded by one quarter of the dominant padding
weight while exposing at least eight times that weight as positive-upper
incidence mass. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_with_quarterBudget
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    4 * F.sum (reducedCollisionWeight (m := n)) ≤
        reducedCollisionWeight (m := n) r ∧
      8 * F.sum (reducedCollisionWeight (m := n)) ≤
        reducedCollisionPositiveUpperIncidenceMass F := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  have hquarter :=
    genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight
      hqodd g hg r hr hres hBcard
  have hpacking :=
    genuineDominant_liveRoot_largeSupport_positiveUpper_packing
      hqodd g hg r hr hres hAcard hBcard
  constructor
  · simpa [F, criticalCanonicalNonrootCollisions,
      canonicalCrossStarWeight, hh, criticalCanonicalReducedCollisions]
      using hquarter
  · exact hpacking.1

end CriticalLargeSupportFamily

end MinModulus
