import MinModulus.LinearCycleEscape

namespace MinModulus
open Finset
open scoped Classical

/-- Complete affine forest data with at most one extra collision cut,
a longest genuine endpoint, and strict failure of its exact corner charge. -/
def BoundedCornerObstructingForest {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (b : G) : Prop :=
    ∃ B : Finset (Fin n), A ⊆ B ∧ B.card ≤ A.card+1 ∧
      ∃ L : B → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n ∧
        ∃ E : (Σ a : B, Fin (L a)) ≃ Fin n, ∃ x : B → G,
          (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
          ∃ a : B, (∀ c, L c ≤ L a) ∧
            (∀ (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b) ∧
              2^(L a-3) < chainFamilyCornerCard n L

/-- An actual acyclic valid tuple below binary size supplies a complete
forest with at most one extra collision cut. Its longest genuine arm
fails the exact bounded-corner charge, at every positive arm length. -/
theorem exists_obstructing_forest_of_acyclic_subbinary_valid_tuple
    {n : ℕ} (hn : 3 ≤ n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (hsub : Fintype.card G < 2^n)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin n)) (b : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ R : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (R i))=2 • g (e i)+b)) :
    BoundedCornerObstructingForest g A b := by
  classical
  obtain ⟨B,hAB,hcard,L,hL,E,x,hchain,a,hmax,hend⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision (by omega) g hg hh hinv A b hA hacyclic
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  refine ⟨B,hAB,hcard,L,hL,hsize,E,x,hchain,a,hmax,hend,?_⟩
  by_cases h4 : 4 ≤ L a
  · by_contra hnot
    have hcharge : chainFamilyCornerError n L ≤ 2^(L a-3) := by
      simp only [chainFamilyCornerError,hsize,Nat.sub_self,pow_zero,mul_one]
      omega
    have hbinary := binary_card_bound_of_partial_genuine_bounded_corner (by omega) L hL
      g hg b x E.toEmbedding hchain a h4 hcharge
      (hend ⟨L a-1,by have := hL a; omega⟩ (by change L a-1+1=L a; have := hL a; omega))
    omega
  · have hLpos := hL a
    have hpow : 2 ≤ 2^(L a) := by
      calc
        _ = (2 : ℕ)^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
    have hC : 2 ≤ chainFamilyCornerCard n L :=
      (le_min (by omega : 2 ≤ n) hpow).trans (selected_side_le_chain_family_corner_card (by omega) L a)
    simpa only [show L a-3=0 by omega,pow_zero] using (by omega : 1 < chainFamilyCornerCard n L)

/-- Cyclic groups have at most one nonzero involution, so the constructive
forest extraction applies without a separate collision hypothesis. -/
theorem obstructing_forest_of_acyclic_subbinary_zmod_tuple
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ R : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (R i))=2 • g (e i)+b)) :
    BoundedCornerObstructingForest g A b := by
  have hcard : Fintype.card (ZMod N) < 2^n := by simpa using hsub
  rcases Nat.even_or_odd N with hev | hod
  · obtain ⟨M,hM⟩ := hev
    have hNM : N=2*M := by omega
    exact exists_obstructing_forest_of_acyclic_subbinary_valid_tuple hn g hg hcard
      (half_add_half hNM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu)
      A b hA hacyclic
  · exact exists_obstructing_forest_of_acyclic_subbinary_valid_tuple hn g hg hcard
      (h:=0) (by simp) (fun u hu ↦ Or.inl (add_self_injective_zmod hod u 0 (by simpa using hu)))
      A b hA hacyclic

/-- A low-escape shift of an original global counterexample supplies the
complete obstructing forest, with actual coordinates and a genuine endpoint. -/
theorem obstructing_forest_of_global_counterexample_at_low_escape_shift
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    BoundedCornerObstructingForest g A b := by
  apply obstructing_forest_of_acyclic_subbinary_zmod_tuple hn g hg
    (hsmall.trans_le (Nat.sub_le _ _)) A b hA
  intro m hm e R hc
  have h := linear_escapes_of_global_counterexample_with_affine_cycle hn hm g hg hsmall b e R hc
  have hfilter : Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)=A := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hA]
  rw [hfilter] at h
  omega

/-- The original exact-stratum counterexample has the same constructive
alternative at each low-escape shift, without changing its target bound. -/
theorem obstructing_forest_of_stratum_counterexample_at_low_escape_shift
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (A : Finset (Fin n)) (b : ZMod (2^s*q))
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    BoundedCornerObstructingForest g A b := by
  letI : NeZero (2^s*q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by positivity) hq.pos)⟩
  apply obstructing_forest_of_acyclic_subbinary_zmod_tuple hn g hg
    (hsmall.trans_le (Nat.sub_le _ _)) A b hA
  intro m hm e R hc
  have h := linear_escapes_of_stratum_counterexample_with_affine_cycle hq hn hm g hg hsmall b e R hc
  have hfilter : Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)=A := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hA]
  rw [hfilter] at h
  omega

/-- In the original odd counterexample, every low-escape shift has an
actual complete forest whose longest genuine arm fails corner charge. -/
theorem obstructing_forest_of_odd_counterexample_at_low_escape_shift
    {n N : ℕ} (hN : Odd N) (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1)
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    BoundedCornerObstructingForest g A b := by
  have h := obstructing_forest_of_stratum_counterexample_at_low_escape_shift (n:=n) (s:=0) hN hn
  rw [show (2 : ℕ)^0*N=N by simp] at h
  exact h g hg (by simpa [stratumBound] using hsmall) A b hA hcount

/-- Direct G3 extraction at every low-escape shift of the original exceptional
modulus; the possible doubled collision costs at most one extra forest arm. -/
theorem obstructing_forest_of_exceptional_tuple_at_low_escape_shift
    {n : ℕ} (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (A : Finset (Fin n)) (b : ZMod (2*globalBound (n-1)))
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    BoundedCornerObstructingForest g A b := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact obstructing_forest_of_global_counterexample_at_low_escape_shift hn g hg hsmall A b hA hcount

/-- At every shift of an original global counterexample, either escapes
exceed the linear threshold or an actual obstructing complete forest exists. -/
theorem linear_escape_or_obstructing_forest_of_global_counterexample
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) :
    n < 5*A.card+1 ∨ BoundedCornerObstructingForest g A b := by
  by_cases hcount : 5*A.card+1 ≤ n
  · exact Or.inr (obstructing_forest_of_global_counterexample_at_low_escape_shift hn g hg hsmall A b hA hcount)
  · exact Or.inl (by omega)

end MinModulus
