import MinModulus.CollisionComplementRanks

namespace MinModulus
open Finset
open scoped Classical

/-- No affine doubling cycle can lie entirely outside the heavier
side of an actual unequal subset collision of a valid tuple. -/
theorem not_affine_doubling_cycle_disjoint_heavier_collision
    {n m : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (e : Fin m ↪ C) (P : Equiv.Perm (Fin m)) :
    ¬ ∀ i, g (e (P i)).val=2 • g (e i).val+b := by
  classical
  intro hcycle
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let E : Fin m ↪ Fin n := e.trans (Function.Embedding.subtype _)
  let T := Finset.univ.map E
  have hT : T.Nonempty := ⟨E ⟨0,hm⟩,Finset.mem_map.mpr ⟨⟨0,hm⟩,Finset.mem_univ _,rfl⟩⟩
  have hU : U ⊆ Finset.univ \ T := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro ht
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp ht
    exact Finset.disjoint_left.mp hd hi (hj ▸ (e j).property)
  apply not_validTuple_of_outside_collision_and_doubling_predecessors
    (fun i ↦ g i+b) T hT ?_ U V hU he hlt hv
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
  refine ⟨E (P.symm j),Finset.mem_map.mpr ⟨P.symm j,Finset.mem_univ _,rfl⟩,?_⟩
  change g (e j).val+b=2 • (g (e (P.symm j)).val+b)
  have hh := hcycle (P.symm j)
  rw [P.apply_symm_apply] at hh
  rw [hh,two_nsmul,two_nsmul]
  abel

/-- All actual chains outside a heavier collision side share one
strict aggregate diameter budget, even when the lighter side meets them. -/
theorem forest_diameter_lt_card_add_heavier_collision_gap
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (E : (Σ a : β, Fin (L a)) ≃ C) (x : β → G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩).val+b=2^j.val • x a) :
    (∑ a, (2^(L a)-1)) < C.card+(U.card-V.card) := by
  classical
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let r : C → ℕ := fun i ↦ (E.symm i).2.val
  have hr (a : β) (j : Fin (L a)) : r (E ⟨a,j⟩)=j.val := by
    change (fun p : Σ a : β, Fin (L a) ↦ p.2.val) (E.symm (E ⟨a,j⟩))=j.val
    rw [E.symm_apply_apply]
  have hp : ∀ i, 0 < r i → ∃ j : C, r i=r j+1 ∧ g i.val+b=2 • (g j.val+b) := by
    intro i hi
    obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective i
    have hj : 0 < j.val := by simpa only [hr] using hi
    let k : Fin (L a) := ⟨j.val-1,by omega⟩
    refine ⟨E ⟨a,k⟩,?_,?_⟩
    · simp only [hr,k]
      omega
    · rw [hchain,hchain,smul_smul]
      change 2^j.val • x a=(2*2^(j.val-1)) • x a
      have hpow : (2 : ℕ)^j.val=2*2^(j.val-1) := by
        calc
          _ = 2^((j.val-1)+1) := congrArg (fun t : ℕ ↦ (2 : ℕ)^t) (by omega)
          _ = _ := pow_succ' _ _
      exact congrArg (fun t : ℕ ↦ t • x a) hpow
  have hweight : (∑ i : C, 2^(r i))=∑ a, (2^(L a)-1) := by
    rw [← E.sum_comp (fun i : C ↦ 2^(r i)),Fintype.sum_sigma]
    simp only [hr]
    exact Finset.sum_congr rfl (fun a _ ↦ sum_binary_powers (L a))
  rw [← hweight]
  apply ranked_growth_lt_card_add_outside_collision_gap (fun i ↦ g i+b) hv C r hp U V ?_ he hlt
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc ↦ Finset.disjoint_left.mp hd hi hc⟩

/-- An arbitrary actual unequal collision extracts an entire affine
forest on any disjoint coordinate set with injective doubling. Original
coordinates, designated endpoints, and the strict growth budget survive. -/
theorem exists_actual_forest_budget_disjoint_heavier_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (hinj : Function.Injective (fun i : C ↦ 2 • g i.val))
    (A : Finset C) (hclosed : ∀ i : C, i ∉ A → ∃ j : C, g j.val=2 • g i.val+b) :
    ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=C.card ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ C, ∃ x : A → G,
        (∀ a (j : Fin (L a)), g (E ⟨a,j⟩).val+b=2^j.val • x a) ∧
        (∀ a (j : Fin (L a)), j.val+1=L a → E ⟨a,j⟩=a.val) ∧
        (∑ a, (2^(L a)-1)) < C.card+(U.card-V.card) := by
  obtain ⟨L,hL,hs,E,x,hchain,hend⟩ := exists_affine_chain_forest_of_injective_acyclic_doubling
    (fun i : C ↦ g i.val) hinj A b hclosed
    (fun hm e P ↦ not_affine_doubling_cycle_disjoint_heavier_collision hm g hg b U V C hd he hlt e P)
  refine ⟨L,hL,by simpa only [Fintype.card_coe] using hs,E,x,hchain,hend,?_⟩
  exact forest_diameter_lt_card_add_heavier_collision_gap L g hg b U V C hd he hlt E x hchain

end MinModulus
