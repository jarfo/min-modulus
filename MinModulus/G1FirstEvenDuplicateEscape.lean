/-
# First-even duplicate-coordinate escape and its uncovered-residue limitation

For an odd half modulus, a nonempty half-invariant set disjoint from its
one-step translate cannot be closed under the two-step translate. Applied
to overlap points whose two subset representations omit a fixed coordinate,
this forces an actual duplicate-coordinate exit from the overlap.

The endpoint need not lie outside both cubes. This is an escape theorem,
not the still-open three-omission deletion or an uncovered-residue count.
-/
import MinModulus.G1CollisionSupportRigidity
import MinModulus.G1Counterexample

namespace MinModulus

open Finset

/-- Odd half-periods prevent a half-invariant set disjoint from its
one-step translate from being closed under the two-step translate. -/
theorem exists_double_translate_exit_of_odd_half_period
    {G : Type*} [AddCommGroup G] {q : ℕ} (hq : Odd q)
    (a h : G) (hh : h + h = 0) (hqa : q • a = 0 ∨ q • a = h)
    (F : Set G) (hF : F.Nonempty)
    (hhalf : ∀ x ∈ F, x + h ∈ F)
    (hseparate : ∀ x ∈ F, x + a ∉ F) :
    ∃ x ∈ F, x + (a + a) ∉ F := by
  classical
  by_contra hnot
  have hclosed : ∀ x ∈ F, x + (a + a) ∈ F := by
    intro x hx
    by_contra hn
    exact hnot ⟨x, hx, hn⟩
  obtain ⟨x, hx⟩ := hF
  have hiter : ∀ k : ℕ, x + k • (a + a) ∈ F := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [succ_nsmul, ← add_assoc]
      exact hclosed _ ih
  obtain ⟨k, hk⟩ := hq
  have harith : 2 * (k + 1) = q + 1 := by omega
  have hvalue : (k + 1) • (a + a) = q • a + a := by
    rw [← two_nsmul, ← mul_nsmul, harith, succ_nsmul]
  have hy := hiter (k + 1)
  rw [hvalue] at hy
  rcases hqa with hz | heq
  · rw [hz, zero_add] at hy
    exact hseparate x hx hy
  · rw [heq] at hy
    have hz := hhalf _ hy
    have he : (x + (h + a)) + h = x + a := by
      calc
        _ = (x + a) + (h + h) := by abel
        _ = x + a := by rw [hh, add_zero]
    rw [he] at hz
    exact hseparate x hx hz

/-- A free-coordinate half-collision at an odd half modulus forces another
free-coordinate collision whose duplicated padding leaves the overlap.
This does not assert that the endpoint leaves both cubes. -/
theorem exists_free_collision_duplicate_outside_overlap_of_odd_half
    {m q : ℕ} (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 * q)) (hg : ValidTuple g)
    (A B : Finset (Fin m)) (j : Fin m) (hjA : j ∉ A) (hjB : j ∉ B)
    (hAB : ssum g A = ssum g B + (q : ZMod (2 * q))) :
    ∃ S T : Finset (Fin m), j ∉ S ∧ j ∉ T ∧
      ssum g S = ssum g T + (q : ZMod (2 * q)) ∧
      ssum g S + (diff g j + diff g j) ∉
        subsetSumRange g ∩ subsetSumShiftRange g (q : ZMod (2 * q)) := by
  classical
  letI : NeZero (2 * q) := ⟨(mul_pos (by norm_num) hq.pos).ne'⟩
  let h : ZMod (2 * q) := q
  let a := diff g j
  have hh : h + h = 0 := half_add_half rfl
  have hqa : q • a = 0 ∨ q • a = h := by
    apply zmod_eq_zero_or_half_of_add_self_eq_zero (M := q) rfl
    calc
      _ = (2 * q) • a := by simp only [two_mul, add_smul]
      _ = 0 := by simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let F : Set (ZMod (2 * q)) := {x | ∃ S T : Finset (Fin m),
    j ∉ S ∧ j ∉ T ∧ ssum g S = x ∧ ssum g T = x + h}
  have hseed : ssum g A ∈ F := by
    refine ⟨A, B, hjA, hjB, rfl, ?_⟩
    rw [hAB, add_assoc, hh, add_zero]
  have hhalf : ∀ x ∈ F, x + h ∈ F := by
    rintro x ⟨S, T, hjS, hjT, hS, hT⟩
    refine ⟨T, S, hjT, hjS, hT, ?_⟩
    rw [add_assoc, hh, add_zero]
    exact hS
  have hins (S : Finset (Fin m)) (hjS : j ∉ S) :
      ssum g (insert j S) = ssum g S + a := by
    simp [ssum, hjS, a, add_comm]
  have hseparate : ∀ x ∈ F, x + a ∉ F := by
    rintro x ⟨S, T, hjS, hjT, hS, hT⟩ ⟨U, V, hjU, hjV, hU, hV⟩
    have he : ssum g (insert j S) = ssum g U := by rw [hins S hjS, hS, hU]
    have hs := ssum_injective g hg he
    exact hjU (hs ▸ Finset.mem_insert_self j S)
  obtain ⟨x, hx, hexit⟩ := exists_double_translate_exit_of_odd_half_period
    hq a h hh hqa F ⟨_, hseed⟩ hhalf hseparate
  obtain ⟨S, T, hjS, hjT, hS, hT⟩ := hx
  refine ⟨S, T, hjS, hjT, ?_, ?_⟩
  · change ssum g S = ssum g T + h
    rw [hS, hT, add_assoc, hh, add_zero]
  · intro hover
    have hxQ : x + (a + a) ∈ subsetSumRange g := by
      simpa [hS, a] using (Finset.mem_inter.mp hover).1
    have hxhQ : x + (a + a) + h ∈ subsetSumRange g := by
      have hz := (Finset.mem_inter.mp hover).2
      change ssum g S + (a + a) ∈ (subsetSumRange g).image (fun y ↦ y + h) at hz
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hz
      have heq : x + (a + a) + h = y := by
        rw [hS] at he
        rw [← he, add_assoc, hh, add_zero]
      rw [heq]
      exact hy
    obtain ⟨U, _, hU⟩ := Finset.mem_image.mp hxQ
    obtain ⟨V, _, hV⟩ := Finset.mem_image.mp hxhQ
    have hjU : j ∉ U := (duplicate_subset_sum_representation_descends
      g hg (insert j S) U j (by simp) (by
        change ssum g (insert j S) + a = ssum g U
        rw [hins S hjS, hS, add_assoc]
        exact hU.symm)).1
    have hjV : j ∉ V := (duplicate_subset_sum_representation_descends
      g hg (insert j T) V j (by simp) (by
        rw [hins T hjT, hT]
        calc
          _ = x + (a + a) + h := by abel
          _ = ssum g V := hV.symm)).1
    exact hexit ⟨U, V, hjU, hjV, hU, hV⟩

/-- Actual criticality supplies the free collision, so every nontrivial
first-even critical tuple has a duplicate-coordinate exit from its overlap.
Neither common-touch failure nor G2 is assumed. -/
theorem exists_duplicate_outside_overlap_of_first_even_critical
    {m q : ℕ} (hm : 1 ≤ m) (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 * q)) (hg : ValidTuple g)
    (hcritical : 2 * q < stratumBound (m + 1) 1) :
    ∃ S T : Finset (Fin m), ∃ j : Fin m, j ∉ S ∧ j ∉ T ∧
      ssum g S = ssum g T + (q : ZMod (2 * q)) ∧
      ssum g S + (diff g j + diff g j) ∉
        subsetSumRange g ∩ subsetSumShiftRange g (q : ZMod (2 * q)) := by
  classical
  letI : NeZero (2 * q) := ⟨(mul_pos (by norm_num) hq.pos).ne'⟩
  have hh : (q : ZMod (2 * q)) + q = 0 := half_add_half rfl
  have hne : (q : ZMod (2 * q)) ≠ 0 := half_ne_zero rfl hq.pos
  have hover : 2 < (subsetSumRange g ∩ subsetSumShiftRange g (q : ZMod (2 * q))).card := by
    have hb := critical_subsetSum_half_overlap_add_two_le (s := 0) hm hq g hg hcritical
    have hp : 0 < 2 ^ min 1 (Nat.log 2 (m + 1)) := by positivity
    simp only [zero_add, pow_zero, one_mul] at hb
    omega
  obtain ⟨r, _, j, hj⟩ := exists_canonicalReducedCollision_with_free_tail_of_two_lt_overlap
    g hg hh hne (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero rfl x hx) hover
  have hjA : j ∉ r.val.1 := fun h ↦ hj (Finset.mem_union_left _ h)
  have hjB : j ∉ r.val.2 := fun h ↦ hj (Finset.mem_union_right _ h)
  obtain ⟨S, T, hjS, hjT, hST, hexit⟩ :=
    exists_free_collision_duplicate_outside_overlap_of_odd_half hq g hg
      r.val.1 r.val.2 j hjA hjB r.property.2
  exact ⟨S, T, j, hjS, hjT, hST, hexit⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- In the existing valid first-even counterexample, one free coordinate
has a nonempty collision face but every direct duplicate exit lies in
exactly one cube. Thus the escape conclusion cannot be strengthened to
outside both cubes at an arbitrary fixed free coordinate without more input.
This tuple is outside the critical range. -/
theorem g1Counterexample_fixed_coordinate_duplicate_only_single_cube :
    let g := g1CounterexampleTuple
    let h : ZMod 1006 := 503
    let j : Fin 6 := 2
    let R := ((Finset.univ : Finset (Finset (Fin 6))).filter (fun S ↦ j ∉ S)).image (ssum g)
    let F := R ∩ R.image (fun x ↦ x + h)
    let Q := subsetSumRange g
    let Qh := subsetSumShiftRange g h
    F.Nonempty ∧
      F.image (fun x ↦ x + (diff g j + diff g j)) ⊆ (Q \ Qh) ∪ (Qh \ Q) := by
  decide

end MinModulus
