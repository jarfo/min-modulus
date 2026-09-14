import Mathlib

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Missing incidences between disjoint coordinate sets inject into the
unordered pair family that covers them. -/
theorem cross_missing_incidence_sum_le_pair_family
    {α : Type*} [DecidableEq α] (A S : Finset α) (hAS : Disjoint A S)
    (R : α → Finset α) (D : Finset (Finset α))
    (hD : ∀ a ∈ A, ∀ i ∈ S \ R a, ({a,i} : Finset α) ∈ D) :
    (∑ a ∈ A, (S \ R a).card) ≤ D.card := by
  classical
  let I := A.sigma (fun a ↦ S \ R a)
  let f : (Σ _a : α, α) → Finset α := fun x ↦ {x.1,x.2}
  have hmap : ∀ x ∈ I, f x ∈ D := by
    intro x hx
    obtain ⟨ha,hi⟩ := Finset.mem_sigma.mp hx
    exact hD x.1 ha x.2 hi
  have hinj : Set.InjOn f I := by
    intro x hx y hy he
    obtain ⟨ha,hi⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hb,hj⟩ := Finset.mem_sigma.mp hy
    have hiS := (Finset.mem_sdiff.mp hi).1
    have hjS := (Finset.mem_sdiff.mp hj).1
    have hab : x.1=y.1 := by
      have hh : x.1 ∈ f y := by rw [← he]; simp [f]
      rcases (show x.1=y.1 ∨ x.1=y.2 by simpa only [f,Finset.mem_insert,Finset.mem_singleton] using hh) with h | h
      · exact h
      · exact False.elim (Finset.disjoint_left.mp hAS ha (h.symm ▸ hjS))
    have hij : x.2=y.2 := by
      have hh : x.2 ∈ f y := by rw [← he]; simp [f]
      rcases (show x.2=y.1 ∨ x.2=y.2 by simpa only [f,Finset.mem_insert,Finset.mem_singleton] using hh) with h | h
      · exact False.elim (Finset.disjoint_left.mp hAS hb (h ▸ hiS))
      · exact h
    cases x with | mk a i =>
      cases y with | mk b j =>
        dsimp only at hab hij
        subst b
        subst j
        rfl
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [I,Finset.card_sigma] using hc

/-- A uniform bound by two deficits and an error term can be averaged
over a finite set with at least two members. -/
theorem pair_deficit_average_bound
    {α : Type*} [DecidableEq α] (A : Finset α) (hA : 2 ≤ A.card)
    (d : α → ℕ) (M C : ℕ)
    (hp : ∀ a ∈ A, ∀ b ∈ A, a≠b → M ≤ d a+d b+C) :
    A.card*M ≤ 2*(∑ a ∈ A, d a)+C*A.card := by
  classical
  have hpoint (a : α) (ha : a ∈ A) :
      (A.card-1)*M+d a ≤ (A.card-1)*(d a+C)+(∑ b ∈ A, d b) := by
    have hsum := Finset.sum_le_sum (s:=A.erase a)
      (fun b hb ↦ hp a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm)
    have he := Finset.sum_erase_add A d ha
    have hc := Finset.card_erase_of_mem ha
    have heq : (∑ b ∈ A.erase a, (d a+d b+C)) =
        (A.erase a).card*(d a+C)+(∑ b ∈ A.erase a, d b) := by
      calc
        _ = ∑ b ∈ A.erase a, (d a+C+d b) := by congr 1; funext b; omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const,Nat.nsmul_eq_mul]
    rw [heq] at hsum
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,hc] at hsum
    omega
  have hsum := Finset.sum_le_sum (s:=A) hpoint
  have hl : (∑ a ∈ A, ((A.card-1)*M+d a)) =
      A.card*((A.card-1)*M)+(∑ a ∈ A, d a) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  have hr : (∑ a ∈ A, ((A.card-1)*(d a+C)+(∑ b ∈ A, d b))) =
      (A.card-1)*((∑ a ∈ A, d a)+A.card*C)+A.card*(∑ b ∈ A, d b) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  rw [hl,hr] at hsum
  have hc : A.card=(A.card-1)+1 := by omega
  have ht : A.card*(∑ a ∈ A, d a) = (A.card-1)*(∑ a ∈ A, d a)+(∑ a ∈ A, d a) := by
    conv_lhs => rw [hc]
    ring
  rw [ht] at hsum
  have hmul : (A.card-1)*(A.card*M) ≤
      (A.card-1)*(2*(∑ a ∈ A, d a)+C*A.card) := by
    nlinarith only [hsum]
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

end MinModulus.Research
