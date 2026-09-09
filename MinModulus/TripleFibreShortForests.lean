import MinModulus.TripleFibreEscapeRoutes
import MinModulus.CollisionForest

namespace MinModulus
open Finset
open scoped Classical

/-- Every actual doubling chain at a triple-fibre shift has at most
ceil(log2 n) vertices; the chain map need not be assumed injective. -/
theorem doubling_chain_length_le_clog_of_triple_fibre
    {n m : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z x : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (e : Fin m → Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x) : m ≤ Nat.clog 2 n := by
  let f : ℕ → Fin n := fun t ↦ e ⟨min t (m-1),by have := Nat.min_le_right t (m-1); omega⟩
  have hstep : ∀ t, t < m-1 → g (f (t+1))+b=2 • (g (f t)+b) := by
    intro t ht
    have hv (s : ℕ) : g (f s)+b=2^(min s (m-1)) • x := hchain _
    rw [hv,hv,Nat.min_eq_left (by omega : t+1 ≤ m-1),Nat.min_eq_left (by omega : t ≤ m-1)]
    rw [pow_succ',mul_smul]
  have h := walk_length_lt_clog_of_triple_fibre g hg b z htriple f hstep
  omega

/-- Every arm of any complete actual chain forest is logarithmically
short whenever a triple subset-sum fibre exists. -/
theorem forest_arms_le_clog_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ∀ a, L a ≤ Nat.clog 2 n := by
  intro a
  exact doubling_chain_length_le_clog_of_triple_fibre (hL a) g hg b z (x a) htriple
    (fun i ↦ E ⟨a,i⟩) (hchain a)

/-- The number of arms in any actual forest must compensate for
the logarithmic arm-length restriction imposed by a triple fibre. -/
theorem dimension_le_forest_arm_count_mul_clog_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n ≤ Fintype.card β*Nat.clog 2 n := by
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ ↦ forest_arms_le_clog_of_triple_fibre L hL g hg E x b z hchain htriple a)
  simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul] using h

/-- A triple fibre extracts a complete forest of logarithmically
short actual arms after at most one cut, preserving a longest arm
that ends at an original escape. No acyclicity or forest is an input. -/
theorem exists_short_affine_forest_of_one_collision_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ∃ B : Finset (Fin n), affineDoublingEscapes g b ⊆ B ∧ B.card ≤ (affineDoublingEscapes g b).card+1 ∧
      ∃ L : B → ℕ, (∀ a, 0 < L a) ∧ (∀ a, L a ≤ Nat.clog 2 n) ∧
        ∃ E : (Σ a : B, Fin (L a)) ≃ Fin n, ∃ x : B → G,
          (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
          ∃ a : B, (∀ c, L c ≤ L a) ∧
            ∀ (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hc := Finset.card_le_univ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))
    simp only [Fintype.card_finset,Fintype.card_fin,hn0,pow_zero] at hc
    omega
  obtain ⟨B,hAB,hB,L,hL,E,x,hchain,a,hmax,hgen⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision hn g hg hh hinv (affineDoublingEscapes g b) b
      (by intro i; simp [affineDoublingEscapes])
      (fun hm e P ↦ no_affine_cycle_of_triple_fibre hm g hg b z htriple e P)
  exact ⟨B,hAB,hB,L,hL,forest_arms_le_clog_of_triple_fibre L hL g hg E x b z hchain htriple,
    E,x,hchain,a,hmax,hgen⟩

/-- Every cyclic triple-fibre shift admits a complete logarithmically
short forest with at most one additional terminal and a genuine
longest arm. All data are extracted from the original tuple. -/
theorem exists_short_affine_forest_of_cyclic_triple_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ∃ B : Finset (Fin n), affineDoublingEscapes g b ⊆ B ∧ B.card ≤ (affineDoublingEscapes g b).card+1 ∧
      ∃ L : B → ℕ, (∀ a, 0 < L a) ∧ (∀ a, L a ≤ Nat.clog 2 n) ∧
        ∃ E : (Σ a : B, Fin (L a)) ≃ Fin n, ∃ x : B → ZMod N,
          (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
          ∃ a : B, (∀ c, L c ≤ L a) ∧
            ∀ (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b := by
  rcases Nat.even_or_odd N with hev | hod
  · obtain ⟨M,hM⟩ := hev
    have hNM : N=2*M := by omega
    apply exists_short_affine_forest_of_one_collision_triple_fibre g hg b z (half_add_half hNM)
      (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu)
    simpa only [Finset.sum_eq_multiset_sum] using htriple
  · refine exists_short_affine_forest_of_one_collision_triple_fibre g hg b z (h := 0) (by simp) ?_ ?_
    · intro u hu
      left
      apply add_self_injective_zmod hod
      simpa using hu
    · simpa only [Finset.sum_eq_multiset_sum] using htriple

end MinModulus
