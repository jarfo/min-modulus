import MinModulus.ObstructingChainForest

namespace MinModulus
open Finset
open scoped Classical

/-- Every genuine arm in any complete subbinary forest fails its exact
bounded-corner charge, including the positive lengths below four. -/
theorem corner_charge_fails_of_complete_subbinary_genuine_arm
    {n : ℕ} (hn : 3 ≤ n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (hsub : Fintype.card G < 2^n)
    (E : (Σ a, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^(L a-3) < chainFamilyCornerCard n L := by
  classical
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  by_cases h4 : 4 ≤ L a
  · by_contra hnot
    have hcharge : chainFamilyCornerError n L ≤ 2^(L a-3) := by
      simp only [chainFamilyCornerError,hsize,Nat.sub_self,pow_zero,mul_one]
      omega
    have hbinary := binary_card_bound_of_partial_genuine_bounded_corner (by omega) L hL
      g hg b x E.toEmbedding hchain a h4 hcharge hgenuine
    omega
  · have hLpos := hL a
    have hpow : 2 ≤ 2^(L a) := by
      calc
        _ = (2 : ℕ)^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
    have hC : 2 ≤ chainFamilyCornerCard n L :=
      (le_min (by omega : 2 ≤ n) hpow).trans (selected_side_le_chain_family_corner_card (by omega) L a)
    simpa only [show L a-3=0 by omega,pow_zero] using (by omega : 1 < chainFamilyCornerCard n L)

/-- A complete forest indexed by precisely the genuine escapes, retaining
all endpoint identities and corner-charge failure at every arm. -/
def ExactGenuineObstructingForest {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (b : G) : Prop :=
  ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n ∧
    ∃ E : (Σ a : A, Fin (L a)) ≃ Fin n, ∃ x : A → G,
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b) ∧
      ∀ a, 2^(L a-3) < chainFamilyCornerCard n L

/-- Injective doubling eliminates the extra cut and retains every genuine
endpoint in the complete acyclic subbinary forest. -/
theorem exact_genuine_forest_of_injective_acyclic_subbinary_tuple
    {n : ℕ} (hn : 3 ≤ n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (hsub : Fintype.card G < 2^n)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ R : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (R i))=2 • g (e i)+b)) :
    ExactGenuineObstructingForest g A b := by
  classical
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra hh
    exact hi ((hA i).mpr hh)
  obtain ⟨L,hL,hsize,E,x,hchain,hend⟩ :=
    exists_affine_chain_forest_of_injective_acyclic_doubling g hinj A b hclosed hacyclic
  have hgen : ∀ a (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b := by
    intro a i hi v hv
    rw [hend a i hi] at hv
    exact (hA a.val).mp a.property ⟨v,hv⟩
  refine ⟨L,hL,by simpa using hsize,E,x,hchain,hend,hgen,?_⟩
  intro a
  exact corner_charge_fails_of_complete_subbinary_genuine_arm hn L hL g hg hsub E x b hchain a
    (hgen a ⟨L a-1,by have := hL a; omega⟩ (by change L a-1+1=L a; have := hL a; omega))

/-- The exact forest retains the previously extracted longest-arm obstruction. -/
theorem exact_genuine_obstructing_forest_implies_obstructing_forest
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (b : G)
    (h : ExactGenuineObstructingForest g A b) : BoundedCornerObstructingForest g A b := by
  classical
  obtain ⟨L,hL,hsize,E,x,hchain,_,hgenuine,hcharge⟩ := h
  have hne : Finset.univ.Nonempty (α := A) := ⟨(E.symm ⟨0,hn⟩).1,Finset.mem_univ _⟩
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image Finset.univ L hne
  exact ⟨A,Subset.rfl,by omega,L,hL,hsize,E,x,hchain,a,
    fun c ↦ hmax c (Finset.mem_univ _),hgenuine a,hcharge a⟩

/-- With injective doubling, an original global counterexample supplies
exactly one genuine arm per true escape at every low-escape shift. -/
theorem exact_genuine_forest_of_injective_global_counterexample
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    ExactGenuineObstructingForest g A b := by
  apply exact_genuine_forest_of_injective_acyclic_subbinary_tuple hn g hg
    (by simpa using hsmall.trans_le (Nat.sub_le _ _)) hinj A b hA
  intro m hm e R hc
  have h := linear_escapes_of_global_counterexample_with_affine_cycle hn hm g hg hsmall b e R hc
  have hfilter : Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)=A := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hA]
  rw [hfilter] at h
  omega

/-- The exact-stratum obstruction retains every true endpoint when
doubling is injective, without a failed half-descent assumption. -/
theorem exact_genuine_forest_of_injective_stratum_counterexample
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : ZMod (2^s*q))
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    ExactGenuineObstructingForest g A b := by
  letI : NeZero (2^s*q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by positivity) hq.pos)⟩
  apply exact_genuine_forest_of_injective_acyclic_subbinary_tuple hn g hg
    (by simpa using hsmall.trans_le (Nat.sub_le _ _)) hinj A b hA
  intro m hm e R hc
  have h := linear_escapes_of_stratum_counterexample_with_affine_cycle hq hn hm g hg hsmall b e R hc
  have hfilter : Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)=A := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hA]
  rw [hfilter] at h
  omega

/-- Odd moduli automatically have injective doubling; the original odd
counterexample therefore retains exactly its true escapes as endpoints. -/
theorem exact_genuine_forest_of_odd_counterexample
    {n N : ℕ} (hN : Odd N) (hn : 3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1)
    (A : Finset (Fin n)) (b : ZMod N)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card+1 ≤ n) :
    ExactGenuineObstructingForest g A b := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN.pos⟩
  have hinj : Function.Injective (fun i ↦ 2 • g i) := by
    intro i j he
    exact validTuple_injective g hg (add_self_injective_zmod hN _ _ (by simpa only [two_nsmul] using he))
  have h := exact_genuine_forest_of_injective_stratum_counterexample (n:=n) (s:=0) hN hn
  rw [show (2 : ℕ)^0*N=N by simp] at h
  exact h g hg (by simpa [stratumBound] using hsmall) hinj A b hA hcount

/-- In the original critical G1 setting, failed half descent itself supplies
injective doubling. Every low-escape shift therefore has the exact forest. -/
theorem exact_genuine_forest_of_critical_without_half_at_low_escape_shift
    {n s q : ℕ} (hq : Odd q) (hn : 2 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q))
    (A : Finset (Fin (n+1))) (b : ZMod (2^(s+1)*q))
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b) (hcount : 5*A.card ≤ n) :
    ExactGenuineObstructingForest g A b := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hinj : Function.Injective (fun i ↦ 2 • g i) := by
    apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  exact exact_genuine_forest_of_injective_stratum_counterexample hq (by omega)
    g hg hc hinj A b hA (by omega)

end MinModulus
