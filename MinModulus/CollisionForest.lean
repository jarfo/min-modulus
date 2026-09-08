import MinModulus.ActualEscapeDescent

/-! Cut the unique possible doubled collision away from a longest
terminal path. The resulting actual forest has at most one extra arm,
and a widest arm still ends at a genuine escape. This removes global
doubling injectivity from the scalar acyclic packing bound. -/

namespace MinModulus
open Finset Function
open scoped Classical

/-- Any first-hit rank is bounded by the length of a path to its terminal set. -/
theorem terminal_rank_le_of_iterate_mem
    {α : Type*} (R : α → α) (A : Set α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i ∈ A)
    (hr : ∀ i, i ∉ A → r i=r (R i)+1)
    (t : ℕ) (i : α) (ht : R^[t] i ∈ A) : r i ≤ t := by
  induction t generalizing i with
  | zero => have hh := (hz i).mpr (by simpa using ht); omega
  | succ t ih =>
    by_cases hi : i ∈ A
    · rw [(hz i).mpr hi]; omega
    · have hn := ih (R i) (by simpa only [iterate_succ_apply] using ht)
      rw [hr i hi]
      omega

/-- An ordered path is recovered by iterating its actual successor map. -/
theorem iterate_eq_of_ordered_chain
    {α : Type*} {L : ℕ} (hL : 0 < L) (R : α → α) (f : Fin L → α)
    (hf : ∀ (i : Fin L) (hi : i.val+1 < L), R (f i)=f ⟨i.val+1,hi⟩)
    (t : ℕ) (ht : t < L) : R^[t] (f ⟨0,hL⟩)=f ⟨t,ht⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ_apply',ih (by omega),hf ⟨t,by omega⟩]

/-- Cutting a vertex away from a longest terminal path keeps a longest
forest arm ending at an original terminal. The cut contributes at most
one additional arm. -/
theorem exists_ranked_cut_forest_with_longest_genuine_arm
    {α : Type*} [Fintype α] [DecidableEq α] (R : α → α) (A : Finset α)
    (r : α → ℕ) (hz : ∀ i, r i=0 ↔ i ∈ A)
    (hr : ∀ i, i ∉ A → r i=r (R i)+1)
    (w j : α) (hmax : ∀ i, r i ≤ r w)
    (havoid : ∀ t, t ≤ r w → R^[t] w ≠ j)
    (hinj : ∀ i, i ∉ insert j A → ∀ l, l ∉ insert j A → R i=R l → i=l) :
    ∃ L : ↥(insert j A : Finset α) → ℕ, (∀ a, 0 < L a) ∧
      ∃ E : (Σ a : ↥(insert j A : Finset α), Fin (L a)) ≃ α,
        (∀ a (i : Fin (L a)) (hi : i.val+1 < L a),
          R (E ⟨a,i⟩)=E ⟨a,⟨i.val+1,hi⟩⟩) ∧
        (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
        ∃ a : ↥(insert j A : Finset α), a.val ∈ A ∧ ∀ c, L c ≤ L a := by
  classical
  let B := insert j A
  have hhit : ∀ i, ∃ t : ℕ, R^[t] i ∈ (↑B : Set α) := by
    intro i
    refine ⟨r i,Finset.mem_insert_of_mem ?_⟩
    apply (hz _).mp
    simpa only [Nat.sub_self] using rank_iterate_before_terminal_set R (↑A : Set α) r hz hr i (le_refl _)
  obtain ⟨ρ,hρz,hρr⟩ := exists_rank_of_all_orbits_hit_set R (↑B : Set α) hhit
  have hρle (i : α) : ρ i ≤ r i := by
    apply terminal_rank_le_of_iterate_mem R (↑B : Set α) ρ hρz hρr
    apply Finset.mem_insert_of_mem
    apply (hz _).mp
    simpa only [Nat.sub_self] using rank_iterate_before_terminal_set R (↑A : Set α) r hz hr i (le_refl _)
  have hρw : ρ w=r w := by
    have hb : R^[ρ w] w ∈ B := by
      apply (hρz _).mp
      simpa only [Nat.sub_self] using rank_iterate_before_terminal_set R (↑B : Set α) ρ hρz hρr w (le_refl _)
    have ha : R^[ρ w] w ∈ A := (Finset.mem_insert.mp hb).resolve_left (havoid _ (hρle w))
    have hzero := (hz _).mpr ha
    have hvalue := rank_iterate_before_terminal_set R (↑A : Set α) r hz hr w (hρle w)
    have := hρle w
    omega
  let Q : α → α := fun i ↦ if i ∈ B then i else R i
  obtain ⟨L,hL,E,hEr,hEa,hEe⟩ := exists_full_chain_forest_of_ranked_injective_map Q B
    (by intro i hi; simp [Q,hi]) ρ hρz
    (by intro i hi; simpa only [Q,if_neg hi] using hρr i hi)
    (by intro i hi l hl he; exact hinj i hi l hl (by simpa only [Q,if_neg hi,if_neg hl] using he))
  have hstep (a : B) (i : Fin (L a)) (hi : i.val+1 < L a) :
      R (E ⟨a,i⟩)=E ⟨a,⟨i.val+1,hi⟩⟩ := by
    have hnot : E ⟨a,i⟩ ∉ B := by
      intro hm
      have h0 := (hρz _).mpr hm
      have hd := hEr a i
      omega
    simpa only [Q,if_neg hnot] using hEa a i hi
  have hbound (a : B) : L a ≤ r w+1 := by
    have he := hEr a ⟨0,hL a⟩
    have hh := (hρle (E ⟨a,⟨0,hL a⟩⟩)).trans (hmax _)
    have := hL a
    simp only [Nat.sub_zero] at he
    omega
  obtain ⟨⟨a,i⟩,hw⟩ := E.surjective w
  have haL : L a=r w+1 := by
    have he := hEr a i
    rw [hw,hρw] at he
    have := hbound a
    omega
  have hi0 : i.val=0 := by
    have he := hEr a i
    rw [hw,hρw] at he
    omega
  have hstart : E ⟨a,⟨0,hL a⟩⟩=w := by
    convert hw using 1
    exact congrArg (fun t : Fin (L a) ↦ E ⟨a,t⟩) (Fin.ext hi0.symm)
  refine ⟨L,hL,E,hstep,hEe,a,?_,fun c ↦ by rw [haL]; exact hbound c⟩
  have hend : R^[L a-1] w=a.val := by
    rw [← hstart,iterate_eq_of_ordered_chain (hL a) R (fun t ↦ E ⟨a,t⟩) (hstep a) _ (by have := hL a; omega)]
    exact hEe a _ (by have := hL a; simp only; omega)
  have hne : a.val ≠ j := by
    rw [← hend]
    exact havoid _ (by omega)
  exact (Finset.mem_insert.mp a.property).resolve_left hne

/-- A full path to a genuine escape has injective doubles, even when
one collision occurs elsewhere in the tuple. -/
theorem doubling_injective_on_ranked_terminal_path
    {α : Type*} {G : Type*} [AddCommGroup G]
    (g : α → G) (hg : Function.Injective g) (R : α → α) (A : Set α)
    (b : G) (hA : ∀ i, i ∈ A → ¬ ∃ l, g l=2 • g i+b)
    (hd : ∀ i, i ∉ A → g (R i)=2 • g i+b)
    (r : α → ℕ) (hz : ∀ i, r i=0 ↔ i ∈ A)
    (hr : ∀ i, i ∉ A → r i=r (R i)+1) (w : α) :
    Function.Injective (fun t : Fin (r w+1) ↦ 2 • g (R^[t.val] w)) := by
  intro p q he
  change 2 • g (R^[p.val] w)=2 • g (R^[q.val] w) at he
  have hp := rank_iterate_before_terminal_set R A r hz hr w (by omega : p.val ≤ r w)
  have hq := rank_iterate_before_terminal_set R A r hz hr w (by omega : q.val ≤ r w)
  by_cases hpa : R^[p.val] w ∈ A
  · by_cases hqa : R^[q.val] w ∈ A
    · have hp0 := (hz _).mpr hpa
      have hq0 := (hz _).mpr hqa
      apply Fin.ext
      omega
    · exact (hA _ hpa ⟨R (R^[q.val] w),by rw [hd _ hqa,he]⟩).elim
  · by_cases hqa : R^[q.val] w ∈ A
    · exact (hA _ hqa ⟨R (R^[p.val] w),by rw [hd _ hpa,he]⟩).elim
    · have hnext : R (R^[p.val] w)=R (R^[q.val] w) :=
        hg (by rw [hd _ hpa,hd _ hqa,he])
      have hpr := hr _ hpa
      have hqr := hr _ hqa
      have he' := congrArg r hnext
      have hpp : p.val < r w := by
        have hp0 : r (R^[p.val] w) ≠ 0 := fun h ↦ hpa ((hz _).mp h)
        omega
      have hqq : q.val < r w := by
        have hq0 : r (R^[q.val] w) ≠ 0 := fun h ↦ hqa ((hz _).mp h)
        omega
      apply Fin.ext
      omega

/-- Any actual acyclic cyclic-style doubling graph is a forest after
at most one cut, with a widest arm ending at a genuine escape. -/
theorem exists_affine_forest_with_longest_genuine_arm_of_one_collision
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin n)) (b : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ l, g l=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b)) :
    ∃ B : Finset (Fin n), A ⊆ B ∧ B.card ≤ A.card+1 ∧
      ∃ L : B → ℕ, (∀ a, 0 < L a) ∧
        ∃ E : (Σ a : B, Fin (L a)) ≃ Fin n, ∃ x : B → G,
          (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
          ∃ a : B, (∀ c, L c ≤ L a) ∧
            ∀ (i : Fin (L a)), i.val+1=L a → ∀ v, g v ≠ 2 • g (E ⟨a,i⟩)+b := by
  classical
  have hclosed : ∀ i, i ∉ A → ∃ l, g l=2 • g i+b := by
    intro i hi
    by_contra ht
    exact hi ((hA i).mpr ht)
  by_cases hinj : Function.Injective (fun i ↦ 2 • g i)
  · obtain ⟨L,hL,_,E,x,hchain,hend⟩ :=
      exists_affine_chain_forest_of_injective_acyclic_doubling g hinj A b hclosed hacyclic
    have hne : Finset.univ.Nonempty (α := A) := ⟨(E.symm ⟨0,hn⟩).1,Finset.mem_univ _⟩
    obtain ⟨a,_,hmax⟩ := Finset.exists_max_image Finset.univ L hne
    refine ⟨A,Subset.rfl,by omega,L,hL,E,x,hchain,a,fun c ↦ hmax c (Finset.mem_univ _),?_⟩
    intro i hi v hv
    have he := hend a i hi
    rw [he] at hv
    exact (hA a.val).mp a.property ⟨v,hv⟩
  let R : Fin n → Fin n := fun i ↦ if hi : i ∈ A then i else Classical.choose (hclosed i hi)
  have hd : ∀ i, i ∉ A → g (R i)=2 • g i+b := by
    intro i hi
    simpa only [R,dif_neg hi] using Classical.choose_spec (hclosed i hi)
  obtain ⟨r,hz,hr⟩ : ∃ r : Fin n → ℕ, (∀ i, r i=0 ↔ i ∈ A) ∧
      ∀ i, i ∉ A → r i=r (R i)+1 := by
    rcases rank_or_nonempty_cycle_avoiding_set R (↑A : Set (Fin n)) with hh | ⟨m,hm,e,P,he,hP⟩
    · exact hh
    · exact (hacyclic hm e P (by intro i; rw [hP,hd _ (he i)])).elim
  obtain ⟨w,_,hw⟩ := Finset.exists_max_image Finset.univ r ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  let f : Fin (r w+1) → Fin n := fun t ↦ R^[t.val] w
  let C := Finset.univ.image f
  have hfi := doubling_injective_on_ranked_terminal_path g (validTuple_injective g hg) R (↑A : Set (Fin n))
    b (fun i hi ↦ (hA i).mp hi) hd r hz hr w
  have hC : Set.InjOn (fun i ↦ 2 • g i) C := by
    intro i hi l hl he
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hl
    exact congrArg f (hfi he)
  have hproper : ∃ j, j ∉ C := by
    by_contra hall
    push Not at hall
    exact hinj (fun i l he ↦ hC (hall i) (hall l) he)
  obtain ⟨j,hj,hji⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv C hC hproper
  have havoid : ∀ t, t ≤ r w → R^[t] w ≠ j := by
    intro t ht he
    apply hj
    exact Finset.mem_image.mpr ⟨⟨t,by omega⟩,Finset.mem_univ _,he⟩
  have hRi : ∀ i, i ∉ insert j A → ∀ l, l ∉ insert j A → R i=R l → i=l := by
    intro i hi l hl he
    have hi' : i ≠ j ∧ i ∉ A := by simpa only [Finset.mem_insert,not_or] using hi
    have hl' : l ≠ j ∧ l ∉ A := by simpa only [Finset.mem_insert,not_or] using hl
    apply hji i hi'.1 l hl'.1
    apply add_right_cancel (b := b)
    rw [← hd i hi'.2,← hd l hl'.2,he]
  obtain ⟨L,hL,E,hstep,hend,a,ha,hmax⟩ :=
    exists_ranked_cut_forest_with_longest_genuine_arm R A r hz hr w j (fun i ↦ hw i (Finset.mem_univ _)) havoid hRi
  let x : ↥(insert j A : Finset (Fin n)) → G := fun c ↦ g (E ⟨c,⟨0,hL c⟩⟩)+b
  refine ⟨insert j A,Finset.subset_insert _ _,Finset.card_insert_le _ _,L,hL,E,x,?_,a,hmax,?_⟩
  · intro c
    apply powers_of_ordered_doubling_arrows (hL c)
    intro i hi
    have hnot : E ⟨c,i⟩ ∉ A := by
      intro hmem
      have hfix : R (E ⟨c,i⟩)=E ⟨c,i⟩ := by simp only [R,dif_pos hmem]
      have he := E.injective ((hstep c i hi).symm.trans hfix)
      have hv : i.val+1=i.val := by
        have := Sigma.mk.inj he
        have ht : (⟨i.val+1,hi⟩ : Fin (L c))=i := eq_of_heq this.2
        exact congrArg Fin.val ht
      omega
    rw [← hstep c i hi,hd _ hnot]
    simp only [two_nsmul]
    abel
  · intro i hi v hv
    have he := hend a i hi
    rw [he] at hv
    exact (hA a.val).mp ha ⟨v,hv⟩

/-- For a positive dimension the multiset binomial error grows with rank. -/
theorem forest_binomial_mono_rank {n u v : ℕ} (hn : 0 < n) (huv : u ≤ v) :
    (n+u-1).choose u ≤ (n+v-1).choose v := by
  rw [← Nat.choose_symm (by omega : u ≤ n+u-1),← Nat.choose_symm (by omega : v ≤ n+v-1)]
  have hu : n+u-1-u=n-1 := by omega
  have hv : n+v-1-v=n-1 := by omega
  rw [hu,hv]
  exact Nat.choose_le_choose (n-1) (by omega)

/-- A single collision costs at most one arm in the scalar packing
threshold. No doubling injectivity is assumed about the actual tuple. -/
theorem binary_card_bound_of_acyclic_escape_threshold_with_one_collision
    {n r : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin n)) (hcard : A.card=r) (b : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ l, g l=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b))
    (hcharge : (n+r).choose (r+1) ≤ 2^(n/(r+1)-3)) : 2^n ≤ Fintype.card G := by
  classical
  obtain ⟨_,havg,hwide⟩ := escape_average_conditions_of_binomial_charge hn (by omega : 0 < r+1)
    (by simpa only [show n+(r+1)-1=n+r by omega] using hcharge)
  obtain ⟨B,_,hB,L,hL,E,x,hchain,a,hmax,hgen⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision (by omega) g hg hh hinv A b hA hacyclic
  have hsize : (∑ c, L c)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnL : n ≤ (r+1)*L a := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hmax c)
    simp only [hsize,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right (L a) (by omega))
  have hLa : n/(r+1) ≤ L a := Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hnL)
  apply binary_card_bound_of_one_genuine_arm_short_interval (by omega) L hL g hg E x b hchain a
    (hwide.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hLa)) (by omega) ?_
    (hgen ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega))
  have hb := forest_binomial_mono_rank (by omega : 0 < n) (by simpa only [Fintype.card_coe] using (hB.trans (by omega : A.card+1 ≤ r+1)))
  rw [show n+(r+1)-1=n+r by omega] at hb
  simpa only [Fintype.card_coe] using hb.trans (hcharge.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le_sub_right hLa 3)))

end MinModulus
