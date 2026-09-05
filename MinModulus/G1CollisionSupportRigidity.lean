/-
# Collision support rigidity and free-coordinate seeds for critical overlap counting

In a group whose only elements killed by two are zero and the chosen
involution, a reduced half-collision is determined by its tail support up
to swapping its two sides. Thus canonical representatives have distinct
supports. If every collision used the entire tail, overlap would be at most
two. Strict criticality excludes that case at every choice of anchor.

Consequently each anchor admits a tail-light half-witness with a zero at
another coordinate. This free coordinate supplies an actual padding choice.
Duplicating a coordinate in a subset can return to the subset-sum cube only
through a smaller subset not containing that coordinate.

These are general counting constraints, not a deletion theorem. A return
outside the overlap may still belong to one cube; the ambient complement
required by exact criticality must still be controlled.
-/
import MinModulus.G1CriticalThreeOmissions
import MinModulus.OddOrder

namespace MinModulus

open Finset

/-- Equal reduced tail supports determine a half-collision up to swap,
using the uniqueness of the nonzero involution and subset-sum injectivity. -/
theorem reducedCollision_eq_or_swap_of_support_eq
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hinv : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    (r s : ReducedSubsetSumCollision g h)
    (hsupport : r.val.1 ∪ r.val.2 = s.val.1 ∪ s.val.2) :
    s = r ∨ s = reducedSubsetSumCollisionSwapEquiv hh r := by
  have hu : ssum g r.val.1 + ssum g r.val.2 =
      ssum g s.val.1 + ssum g s.val.2 := by
    rw [← ssum_union_of_disjoint g r.property.1,
      ← ssum_union_of_disjoint g s.property.1, hsupport]
  have htwo : (ssum g r.val.1 - ssum g s.val.1) +
      (ssum g r.val.1 - ssum g s.val.1) = 0 := by
    calc
      _ = (ssum g r.val.1 + ssum g r.val.2) -
          (ssum g s.val.1 + ssum g s.val.2) := by
        rw [r.property.2, s.property.2]
        abel
      _ = 0 := sub_eq_zero.mpr hu
  rcases hinv _ htwo with hz | heq
  · left
    have hAC := sub_eq_zero.mp hz
    have hBD : ssum g r.val.2 = ssum g s.val.2 := by
      rw [hAC] at hu
      exact add_left_cancel hu
    apply Subtype.ext
    exact Prod.ext ((ssum_injective g hg hAC).symm) ((ssum_injective g hg hBD).symm)
  · right
    have hCB : ssum g s.val.1 = ssum g r.val.2 := by
      apply add_right_cancel (b := h)
      calc
        _ = ssum g r.val.1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp heq).symm
        _ = ssum g r.val.2 + h := r.property.2
    have hDA : ssum g s.val.2 = ssum g r.val.1 := by
      calc
        _ = (ssum g s.val.2 + h) + h := by rw [add_assoc, hh, add_zero]
        _ = ssum g s.val.1 + h := by rw [← s.property.2]
        _ = ssum g r.val.2 + h := by rw [hCB]
        _ = ssum g r.val.1 := r.property.2.symm
    apply Subtype.ext
    exact Prod.ext (ssum_injective g hg hCB) (ssum_injective g hg hDA)

/-- Canonical half-collisions cannot carry the same tail support twice. -/
theorem canonicalReducedCollision_support_injective
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hinv : ∀ x : G, x + x = 0 → x = 0 ∨ x = h) :
    Set.InjOn (fun r : ReducedSubsetSumCollision g h ↦ r.val.1 ∪ r.val.2)
      (canonicalReducedCollisions (g := g) hh) := by
  intro r hr s hs heq
  rcases reducedCollision_eq_or_swap_of_support_eq g hg hh hinv r s heq with hsame | hswap
  · exact hsame.symm
  · have hr' := mem_canonicalReducedCollisions_iff.mp hr
    have hs' := mem_canonicalReducedCollisions_iff.mp hs
    rw [hswap] at hs'
    exact False.elim ((canonicalReducedCollision_swap_iff_not hh hne r).mp hs' hr')

/-- More than two overlap points force a reduced collision with a genuinely
free tail coordinate. All-full-support collisions contribute at most two. -/
theorem exists_canonicalReducedCollision_with_free_tail_of_two_lt_overlap
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hinv : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    (hover : 2 < (subsetSumRange g ∩ subsetSumShiftRange g h).card) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        ∃ j : Fin m, j ∉ r.val.1 ∪ r.val.2 := by
  classical
  by_contra hnot
  let F := canonicalReducedCollisions (g := g) hh
  have hfull : ∀ r ∈ F, r.val.1 ∪ r.val.2 = Finset.univ := by
    intro r hr
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    exact hnot ⟨r, hr, j, hj⟩
  have hcard : F.card ≤ 1 := Finset.card_le_one.mpr (by
    intro r hr s hs
    exact canonicalReducedCollision_support_injective g hg hh hne hinv hr hs
      ((hfull r hr).trans (hfull s hs).symm))
  have hsum : F.sum reducedCollisionWeight = F.card := by
    calc
      _ = F.sum (fun _ ↦ 1) := Finset.sum_congr rfl (by
        intro r hr
        simp [reducedCollisionWeight, hfull r hr])
      _ = F.card := by simp
  have heq := card_subsetSumOverlap_eq_two_mul_canonical_weights g hg hh hne
  change (subsetSumRange g ∩ subsetSumShiftRange g h).card =
    2 * F.sum reducedCollisionWeight at heq
  omega

/-- Transport a free tail coordinate of the canonical collision to a zero
coefficient of its associated tail-light half-witness. -/
theorem exists_half_witness_light_with_free_tail_of_two_lt_overlap
    {m N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hover : 2 < (subsetSumRange g ∩ subsetSumShiftRange g (M : ZMod N)).card) :
    ∃ c : Fin (m + 1) → ℤ, Witness g (M : ZMod N) c ∧
      (∀ j : Fin m, c j.succ ≤ 1) ∧ ∃ j : Fin m, c j.succ = 0 := by
  obtain ⟨r, hr, j, hj⟩ :=
    exists_canonicalReducedCollision_with_free_tail_of_two_lt_overlap g hg
      (half_add_half hN) (half_ne_zero hN hM)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx) hover
  refine ⟨subsetCollisionCoeffs r.val.1 r.val.2,
    witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
      (canonicalReducedCollision_card_le (mem_canonicalReducedCollisions_iff.mp hr))
      r.property.2,
    fun j ↦ (subsetCollisionCoeffs_tail_bounds r.val.1 r.val.2 j).2, j, ?_⟩
  have hjA : j ∉ r.val.1 := fun h ↦ hj (Finset.mem_union_left _ h)
  have hjB : j ∉ r.val.2 := fun h ↦ hj (Finset.mem_union_right _ h)
  simp [subsetCollisionCoeffs, hjA, hjB]

/-- In every nontrivial critical tuple, every chosen anchor admits a
half-witness light off that anchor and zero at a distinct coordinate.
This witness need not be the separately supplied three-omission witness. -/
theorem exists_half_witness_light_off_anchor_and_zero_of_critical
    {m s q : ℕ} (hm : 1 ≤ m) (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (m + 1) (s + 1))
    (r : Fin (m + 1)) :
    ∃ c : Fin (m + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      (∀ i, i ≠ r → c i ≤ 1) ∧ ∃ j, j ≠ r ∧ c j = 0 := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1)) (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  let e := Equiv.swap (0 : Fin (m + 1)) r
  have hg' : ValidTuple (fun i ↦ g (e i)) := validTuple_embedding e.toEmbedding g hg
  have hover : 2 < (subsetSumRange (fun i ↦ g (e i)) ∩
      subsetSumShiftRange (fun i ↦ g (e i))
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))).card := by
    have hbound := critical_subsetSum_half_overlap_add_two_le hm hq
      (fun i ↦ g (e i)) hg' hcritical
    have hpos : 0 < 2 ^ min (s + 1) (Nat.log 2 (m + 1)) := by positivity
    omega
  obtain ⟨c, hc, hlight, j, hj⟩ :=
    exists_half_witness_light_with_free_tail_of_two_lt_overlap hN hM
      (fun i ↦ g (e i)) hg' hover
  refine ⟨fun i ↦ c (e.symm i), witness_reindex_perm g e hc, ?_, e j.succ, ?_, ?_⟩
  · intro i hir
    dsimp only
    have hi0 : e.symm i ≠ 0 := by
      intro hi
      have hh := congrArg e hi
      apply hir
      simpa [e] using hh
    obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hi0
    rw [hk]
    exact hlight k
  · intro heq
    have h0 : e (0 : Fin (m + 1)) = r := by simp [e]
    exact Fin.succ_ne_zero j (e.injective (heq.trans h0.symm))
  · simpa using hj

/-- Adding a second copy of a present coordinate can return to the cube
only through a strictly smaller subset omitting that coordinate. -/
theorem duplicate_subset_sum_representation_descends
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (S T : Finset (Fin m)) (j : Fin m) (hjS : j ∈ S)
    (hvalue : ssum g S + diff g j = ssum g T) :
    j ∉ T ∧ T.card < S.card := by
  have hjT : j ∉ T := by
    intro hjT
    have hsumT : ssum g (T.erase j) + diff g j = ssum g T :=
      Finset.sum_erase_add T (diff g) hjT
    have hsets : S = T.erase j := ssum_injective g hg (add_right_cancel
      (hvalue.trans hsumT.symm))
    have : j ∈ T.erase j := hsets ▸ hjS
    exact Finset.notMem_erase j T this
  refine ⟨hjT, ?_⟩
  by_contra hnot
  have hST : S.card ≤ T.card := by omega
  let d : Fin m → ℤ := fun i ↦
    (if i ∈ S then 1 else 0) + (if i = j then 1 else 0) -
      (if i ∈ T then 1 else 0)
  apply validTuple_no_diff_relation g hg (d := d)
  · intro hd
    have hj := congrFun hd j
    simp [d, hjS, hjT] at hj
  · intro i
    dsimp [d]
    split_ifs <;> omega
  · have hsum : (∑ i, d i) = (S.card : ℤ) + 1 - T.card := by
      simp [d, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsum]
    have hST' : (S.card : ℤ) ≤ T.card := by exact_mod_cast hST
    omega
  · have hsum : (∑ i, d i • diff g i) =
        ssum g S + diff g j - ssum g T := by
      simp only [d, sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [sum_indicator_smul, sum_single_smul, sum_indicator_smul]
      simp [ssum]
    rw [hsum, hvalue, sub_self]

end MinModulus
