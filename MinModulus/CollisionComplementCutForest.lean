import MinModulus.CollisionComplementForests
import MinModulus.G1SubtupleWitnessKernel

namespace MinModulus
open Finset
open scoped Classical

/-- At most one cut extracts an actual forest outside any heavier
collision side in an ambient group with at most one nonzero involution.
Native coordinates and the strict diameter budget are retained, and a
widest arm still ends at a genuine escape from the selected block. -/
theorem exists_actual_cut_forest_budget_disjoint_heavier_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hC : C.Nonempty) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset C) (hA : ∀ i : C, i ∈ A ↔ ¬ ∃ j : C, g j.val=2 • g i.val+b) :
    ∃ B : Finset C, A ⊆ B ∧ B.card ≤ A.card+1 ∧
      ∃ L : B → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=C.card ∧
        ∃ E : (Σ a : B, Fin (L a)) ≃ C, ∃ x : B → G,
          (∀ a (j : Fin (L a)), g (E ⟨a,j⟩).val+b=2^j.val • x a) ∧
          (∑ a, (2^(L a)-1)) < C.card+(U.card-V.card) ∧
          ∃ a : B, (∀ c, L c ≤ L a) ∧
            ∀ (j : Fin (L a)), j.val+1=L a → ∀ v : C,
              g v.val ≠ 2 • g (E ⟨a,j⟩).val+b := by
  classical
  let δ : Fin C.card ≃ C := (Equiv.cast (congrArg Fin (Fintype.card_coe C).symm)).trans (Fintype.equivFin C).symm
  let e : Fin C.card ↪ Fin n := δ.toEmbedding.trans (Function.Embedding.subtype _)
  let q : Fin C.card → G := fun i ↦ g (δ i).val
  have hq : ValidTuple q := validTuple_embedding e g hg
  let A₀ := A.map δ.symm.toEmbedding
  have hAeq (i : Fin C.card) : i ∈ A₀ ↔ δ i ∈ A := by simp [A₀]
  have hA₀ : ∀ i, i ∈ A₀ ↔ ¬ ∃ j, q j=2 • q i+b := by
    intro i
    rw [hAeq,hA]
    constructor
    · intro hi ⟨j,hj⟩
      exact hi ⟨δ j,hj⟩
    · intro hi ⟨j,hj⟩
      apply hi
      exact ⟨δ.symm j,by simpa only [q,δ.apply_symm_apply] using hj⟩
  obtain ⟨B₀,hAB₀,hB₀,L₀,hL₀,F,x₀,hchain₀,a₀,hmax,hgenuine⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision (Finset.card_pos.mpr hC) q hq hh hinv A₀ b hA₀
      (fun hm e' P ↦ not_affine_doubling_cycle_disjoint_heavier_collision hm g hg b U V C hd he hlt
        (e'.trans δ.toEmbedding) P)
  let B := B₀.map δ.toEmbedding
  let ε : B ≃ B₀ := δ.symm.subtypeEquiv (by intro i; simp [B])
  let L : B → ℕ := fun a ↦ L₀ (ε a)
  let x : B → G := fun a ↦ x₀ (ε a)
  let E : (Σ a : B, Fin (L a)) ≃ C := (Equiv.sigmaCongrLeft ε).trans (F.trans δ)
  have hL : ∀ a, 0 < L a := fun a ↦ hL₀ (ε a)
  have hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩).val+b=2^j.val • x a := by
    intro a j
    exact hchain₀ (ε a) j
  have hsum : (∑ a, L a)=C.card := by
    simpa only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_coe] using Fintype.card_congr E
  refine ⟨B,?_,?_,L,hL,hsum,E,x,hchain,?_,?_⟩
  · intro a ha
    exact Finset.mem_map.mpr ⟨δ.symm a,hAB₀ ((hAeq _).mpr (by simpa only [δ.apply_symm_apply] using ha)),δ.apply_symm_apply a⟩
  · simpa only [B,A₀,Finset.card_map] using hB₀
  · exact forest_diameter_lt_card_add_heavier_collision_gap L g hg b U V C hd he hlt E x hchain
  · obtain ⟨a,rfl⟩ := ε.surjective a₀
    refine ⟨a,fun c ↦ hmax (ε c),?_⟩
    intro j hj v hv
    apply hgenuine j hj (δ.symm v)
    simpa only [q,δ.apply_symm_apply,E,Equiv.trans_apply,Equiv.sigmaCongrLeft_apply] using hv

/-- A possible single doubled collision costs at most one in the
escape count: the selected block's size is at most its number of actual
escapes plus the outside collision gap. -/
theorem complement_escape_count_lower_bound_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset C) (hA : ∀ i : C, i ∈ A ↔ ¬ ∃ j : C, g j.val=2 • g i.val+b) :
    C.card ≤ A.card+(U.card-V.card) := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨B,_,hB,L,_,hs,_,_,_,hbudget,_⟩ :=
      exists_actual_cut_forest_budget_disjoint_heavier_collision g hg b U V C hC hd he hlt hh hinv A hA
    have hlinear (l : ℕ) : 2*l ≤ 2^l := by
      induction l with
      | zero => norm_num
      | succ l ih =>
        by_cases hl : l=0
        · subst l; norm_num
        · have hlpos : 1 ≤ l := by omega
          rw [pow_succ]
          nlinarith
    have hpoint (a : B) : 2*L a ≤ (2^(L a)-1)+1 := by
      have hh := hlinear (L a)
      have hp : 0 < 2^(L a) := by positivity
      omega
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun a _ ↦ hpoint a)
    simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_coe,smul_eq_mul,mul_one,hs] at hsum
    omega
  · have hc : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp [hc]

end MinModulus
