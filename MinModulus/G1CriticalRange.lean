/-
# Subset-sum overlap in the critical G1 range

Validity makes the `2^m` subset sums of the anchored differences of an
`(m+1)`-tuple distinct.  If the ambient cyclic group has order below
`2^(m+1)`, this subset-sum cube must overlap its translate by the half modulus.
Every point of that overlap gives an explicit half-witness whose non-anchor
coefficients lie in `{-1,0,1}`.

The quantitative overlap inequality is the missing way in which the strict
modulus range can enter G1.  In particular, the no-half-witness/halving branch
of two-adic descent is impossible whenever the global induction is still below
its claimed stratum endpoint.
-/
import MinModulus.Descent

namespace MinModulus

open Finset

section SubsetSumRange

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The image of the full subset-sum cube of the anchored differences. -/
noncomputable def subsetSumRange (g : Fin (m + 1) → G) : Finset G :=
  Finset.univ.image (ssum g)

/-- A translate of the anchored subset-sum cube. -/
noncomputable def subsetSumShiftRange (g : Fin (m + 1) → G) (h : G) : Finset G :=
  (subsetSumRange g).image (fun x => x + h)

/-- Validity makes the subset-sum range have its full cube cardinality. -/
theorem card_subsetSumRange (g : Fin (m + 1) → G) (hg : ValidTuple g) :
    (subsetSumRange g).card = 2 ^ m := by
  rw [subsetSumRange, Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- Translation preserves the full subset-sum cube cardinality. -/
theorem card_subsetSumShiftRange (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) : (subsetSumShiftRange g h).card = 2 ^ m := by
  rw [subsetSumShiftRange,
    Finset.card_image_of_injective _ (fun _ _ hxy => add_right_cancel hxy),
    card_subsetSumRange g hg]

/-- Inclusion-exclusion for a subset-sum cube and any one of its translates:
the missing mass from the ambient group must occur in their intersection. -/
theorem two_pow_le_card_add_subsetSumShift_overlap
    [Fintype G] (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    2 ^ (m + 1) ≤ Fintype.card G +
      ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  have hunion : ((subsetSumRange g) ∪ (subsetSumShiftRange g h)).card ≤
      Fintype.card G := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hsum := Finset.card_union_add_card_inter
    (subsetSumRange g) (subsetSumShiftRange g h)
  rw [card_subsetSumRange g hg, card_subsetSumShiftRange g hg] at hsum
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  omega

/-- Quantitative cyclic form: if `N + K < 2^(m+1)`, every translate of the
subset-sum cube overlaps it in more than `K` points. -/
theorem subsetSumShift_overlap_card_gt_of_add_lt
    {N K : ℕ} [NeZero N] (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (h : ZMod N) (hroom : N + K < 2 ^ (m + 1)) :
    K < ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  have hover := two_pow_le_card_add_subsetSumShift_overlap g hg h
  rw [ZMod.card] at hover
  omega

end SubsetSumRange

section CollisionWitness

variable {m : ℕ}

/-- Coefficients associated with a subset-sum collision.  The anchor absorbs
the cardinality difference, while every tail coefficient is a difference of
two indicators and hence belongs to `{-1,0,1}`. -/
def subsetCollisionCoeffs (S T : Finset (Fin m)) : Fin (m + 1) → ℤ :=
  Fin.cons ((T.card : ℤ) - (S.card : ℤ))
    (fun j => (if j ∈ S then 1 else 0) - (if j ∈ T then 1 else 0))

lemma subsetCollisionCoeffs_sum (S T : Finset (Fin m)) :
    ∑ i, subsetCollisionCoeffs S T i = 0 := by
  rw [subsetCollisionCoeffs, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib]
  simp

variable {G : Type*} [AddCommGroup G]

lemma subsetCollisionCoeffs_weighted_sum (g : Fin (m + 1) → G)
    (S T : Finset (Fin m)) :
    ∑ i, subsetCollisionCoeffs S T i • g i = ssum g S - ssum g T := by
  rw [subsetCollisionCoeffs, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_smul, Finset.sum_sub_distrib]
  rw [ssum_eq, ssum_eq]
  simp only [ite_smul, one_zsmul, zero_zsmul, Finset.sum_ite_mem,
    Finset.univ_inter]
  module

lemma subsetCollisionCoeffs_ge_neg_one (S T : Finset (Fin m))
    (hcard : S.card ≤ T.card) :
    ∀ i, -1 ≤ subsetCollisionCoeffs S T i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change (-1 : ℤ) ≤ (T.card : ℤ) - (S.card : ℤ)
    have hc : (S.card : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast hcard
    omega
  · intro j
    simp only [subsetCollisionCoeffs, Fin.cons_succ]
    split_ifs <;> omega

/-- A subset-sum equality differing by `h` produces an admissible witness at
`h` after orienting the sets by cardinality. -/
theorem witness_of_subsetSum_eq_add (g : Fin (m + 1) → G)
    {h : G} (hh : h ≠ 0) {S T : Finset (Fin m)} (hcard : S.card ≤ T.card)
    (hvalue : ssum g S = ssum g T + h) :
    Witness g h (subsetCollisionCoeffs S T) := by
  refine ⟨?_, subsetCollisionCoeffs_ge_neg_one S T hcard,
    subsetCollisionCoeffs_sum S T, ?_⟩
  · intro hc
    have hzero : ∑ i, subsetCollisionCoeffs S T i • g i = 0 := by
      simp [hc]
    rw [subsetCollisionCoeffs_weighted_sum, hvalue] at hzero
    apply hh
    exact sub_eq_zero.mp (by simpa [add_comm] using hzero)
  · rw [subsetCollisionCoeffs_weighted_sum, hvalue]
    abel

lemma subsetCollisionCoeffs_tail_bounds (S T : Finset (Fin m)) (j : Fin m) :
    -1 ≤ subsetCollisionCoeffs S T j.succ ∧
      subsetCollisionCoeffs S T j.succ ≤ 1 := by
  simp only [subsetCollisionCoeffs, Fin.cons_succ]
  split_ifs <;> omega

end CollisionWitness

section OverlapWitness

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A nonempty overlap with an order-two translate produces a collision
witness.  Swapping the two subsets preserves the target because `h = -h`. -/
theorem exists_subsetCollision_witness_of_overlap
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hoverlap : ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).Nonempty) :
    ∃ S T : Finset (Fin m), S.card ≤ T.card ∧
      Witness g h (subsetCollisionCoeffs S T) := by
  obtain ⟨x, hx⟩ := hoverlap
  have hxrange := (Finset.mem_inter.mp hx).1
  have hxshift := (Finset.mem_inter.mp hx).2
  rw [subsetSumRange] at hxrange
  obtain ⟨S, _, hS⟩ := Finset.mem_image.mp hxrange
  rw [subsetSumShiftRange] at hxshift
  obtain ⟨y, hyrange, hy⟩ := Finset.mem_image.mp hxshift
  rw [subsetSumRange] at hyrange
  obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hyrange
  have hST : ssum g S = ssum g T + h := by
    calc
      ssum g S = x := hS
      _ = y + h := hy.symm
      _ = ssum g T + h := by rw [hT]
  rcases le_total S.card T.card with hcard | hcard
  · exact ⟨S, T, hcard, witness_of_subsetSum_eq_add g hh0 hcard hST⟩
  · have hTS : ssum g T = ssum g S + h := by
      calc
        ssum g T = (ssum g T + h) + h := by rw [add_assoc, hh, add_zero]
        _ = ssum g S + h := by rw [← hST]
    exact ⟨T, S, hcard, witness_of_subsetSum_eq_add g hh0 hcard hTS⟩

/-- Below `2^(m+1)`, a valid tuple modulo an even `N=2M` necessarily has a
half-witness.  It can be chosen with every non-anchor coefficient in
`{-1,0,1}`. -/
theorem exists_light_half_witness_of_lt_two_pow
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2 ^ (m + 1)) :
    ∃ c : Fin (m + 1) → ℤ, Witness g (M : ZMod N) c ∧
      ∀ j : Fin m, -1 ≤ c j.succ ∧ c j.succ ≤ 1 := by
  have hover := subsetSumShift_overlap_card_gt_of_add_lt
    (K := 0) g hg (M : ZMod N) (by omega)
  have hoverlap : ((subsetSumRange g) ∩
      (subsetSumShiftRange g (M : ZMod N))).Nonempty :=
    Finset.card_pos.mp hover
  obtain ⟨S, T, _, hW⟩ := exists_subsetCollision_witness_of_overlap g
    (half_add_half hN) (half_ne_zero hN hM) hoverlap
  exact ⟨subsetCollisionCoeffs S T, hW,
    subsetCollisionCoeffs_tail_bounds S T⟩

end OverlapWitness

end MinModulus
