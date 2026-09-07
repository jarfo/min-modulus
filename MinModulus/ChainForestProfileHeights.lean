import MinModulus.ChainForestProfileStrict

/-! An axis base and compatible strip have height at most two. Their
complete family pays a binary deficit of at most four and satisfies the
sharp global bound. Cyclic compatible-family exhaustion is derived.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Assemble two represented axis weights into an actual full-length
rival using the forest's joint binary refinement. -/
theorem not_validTuple_of_two_axis_representations
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (s t : ℕ) (uj ua : ℕ → ℕ)
    (huj : val (L j) uj=s) (hua : val (L a) ua=t)
    (hcost : dsum (L j) uj+dsum (L a) ua ≤ n)
    (hhigh : n ≤ s+t) (hne : t ≠ 2^(L a)-1)
    (hsum : s • x j+t • x a=∑ i, (2^(L i)-1) • x i) : ¬ ValidTuple g := by
  classical
  let X : β → ℕ := fun i ↦ if i=j then s else if i=a then t else 0
  let u : β → ℕ → ℕ := fun i ↦ if i=j then uj else if i=a then ua else fun _ ↦ 0
  have hu : ∀ i, val (L i) (u i)=X i := by
    intro i
    by_cases hij : i=j
    · subst i; simpa only [u,X,if_true] using huj
    · by_cases hia : i=a
      · subst i; simpa only [u,X,if_neg haj,if_true] using hua
      · simp [u,X,hij,hia,val]
  have hlow : (∑ i, dsum (L i) (u i)) ≤ n := by
    have he : (∑ i, dsum (L i) (u i))=dsum (L j) uj+dsum (L a) ua := by
      calc
        _ = ∑ i, ((if i=j then dsum (L j) uj else 0)+(if i=a then dsum (L a) ua else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i=j
          · subst i; simp [u,Ne.symm haj]
          · by_cases hia : i=a
            · subst i; simp [u,haj]
            · simp [u,hij,hia,dsum]
        _ = _ := by simp [Finset.sum_add_distrib]
    rwa [he]
  have hpoint : ∀ i, X i=(if i=j then s else 0)+(if i=a then t else 0) := by
    intro i
    by_cases hij : i=j
    · subst i; simp [X,Ne.symm haj]
    · by_cases hia : i=a
      · subst i; simp [X,haj]
      · simp [X,hij,hia]
  apply not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hlow
  · simpa [hpoint,Finset.sum_add_distrib] using hhigh
  · exact ⟨a,by simpa only [X,if_neg haj,if_true] using hne⟩
  · simpa [hpoint,add_nsmul,ite_smul,Finset.sum_add_distrib] using hsum

/-- A dyadic small axis target next to a length-one zero boundary has
height at most two: taller targets can absorb the parity remainder in
binary refinement after adding enough zero-boundary pairs. -/
theorem dyadic_axis_height_le_two_of_length_one_zero_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hLa : L a=1) (hzero : 2 • x a=0)
    (e : ℕ) (hwidth : 2^e ≤ 2^(L j)) (hbudget : 2^e+2 ≤ n)
    (htarget : (∑ i, (2^(L i)-1) • x i)=(2^e-1) • x j) : e ≤ 1 := by
  classical
  by_contra hnot
  have he : 2 ≤ e := by omega
  have hpow : ∀ k, 2 ≤ k → k+2 ≤ 2^k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ']; nlinarith
  have hgap := hpow e he
  let m := (n-e)/2
  have hmp : 1 ≤ m := by dsimp only [m]; omega
  obtain ⟨uj,huj,hcj⟩ := exists_rep_with_smaller_coin_budget (L j) e (2^e-1)
    (by omega) (by have := Nat.two_pow_pos e; omega)
  obtain ⟨ua,hua,hca⟩ := exists_rep_boundary_multiple (by omega : 0 < L a) m
  have hua' : val (L a) ua=2*m := by simpa only [hLa,pow_one,Nat.mul_comm] using hua
  apply not_validTuple_of_two_axis_representations L g E x b hchain j a haj (2^e-1) (2*m) uj ua huj hua'
  · rw [hca]; dsimp only [m]; omega
  · dsimp only [m]; omega
  · rw [hLa]; norm_num
  · rw [htarget]
    have hz : (2*m) • x a=0 := by rw [mul_nsmul,hzero,smul_zero]
    rw [hz,add_zero]
  · exact hg

/-- In the surviving axis-base/compatible-strip case, both heights are
at most two, in addition to the length-one and zero-boundary conclusions. -/
theorem axis_base_compatible_strip_height_le_two
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    (w j).val+1 ≤ 2 ∧ (v j).val+1 ≤ 2 := by
  classical
  have hLa := axis_base_compatible_strip_arm_length_one hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hcompat a ha hvz
  obtain ⟨heq,hzero⟩ := axis_profile_and_compatible_strip_equal_zero_boundary hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hcompat a ha hvz
  obtain ⟨haj,_,_,e,he,hbudget⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have htarget : (∑ i, (2^(L i)-1) • x i)=(2^e-1) • x j := by
    rw [← hvm.2,show 2^e-1=(v j).val by omega]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  have he1 := dyadic_axis_height_le_two_of_length_one_zero_boundary L g hg E x b hchain j a haj hLa
    (by simpa only [hLa,pow_one] using hzero) e (by omega) (by simpa only [hLa,pow_one,add_comm] using hbudget) htarget
  have hp : 2^e ≤ 2^1 := Nat.pow_le_pow_right (by decide) he1
  norm_num at hp
  omega

/-- An axis profile below the dominant width has exactly its dominant
height many lower-box points. -/
theorem forestProfileLowerBox_card_of_axis
    {β : Type*} [Fintype β] (L : β → ℕ) (j : β)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hj : (v j).val < 2^(L j)) (hz : ∀ i, i ≠ j → (v i).val=0) :
    (forestProfileLowerBox L v).card=(v j).val+1 := by
  classical
  rw [forestProfileLowerBox_card]
  have he : (∏ i, min ((v i).val+1) (2*(2^(L i)-1)+1-(v i).val))=
      min ((v j).val+1) (2*(2^(L j)-1)+1-(v j).val) := by
    apply Finset.prod_eq_single j
    · intro i _ hij; rw [hz i hij]; simp
    · simp
  rw [he]
  have := Nat.two_pow_pos (L j)
  omega

/-- If the actual profile family consists of an axis base and its
compatible strip, at most four lower points pay the entire binary deficit.
This closes the sharp global bound for that family, in any finite group. -/
theorem axis_base_strip_family_four_point_gap_and_global_bound
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hfamily : ∀ u ∈ forestCollisionProfiles n L x, u=v ∨ u=w) :
    2^n ≤ Fintype.card G+4 ∧ globalBound n ≤ Fintype.card G := by
  classical
  obtain ⟨hwh,hvh⟩ := axis_base_compatible_strip_height_le_two hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hcompat a ha hvz
  have hLa := axis_base_compatible_strip_arm_length_one hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hcompat a ha hvz
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha
  have hvcard : (forestProfileLowerBox L v).card ≤ 2 := by
    rw [forestProfileLowerBox_card_of_axis L j v (by omega) hvz]
    exact hvh
  have hwcard : (forestProfileLowerBox L w).card ≤ 2 := by
    rw [forestProfileLowerBox_card_of_strip L j a haj w (by omega) hwa hwz,hLa]
    simpa using hwh
  have hsub : forestCollisionProfiles n L x ⊆ {v,w} := by
    intro u hu
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hfamily u hu
  have hpair : ({v,w} : Finset _).card ≤ 2 := by
    by_cases heq : v=w
    · simp [heq]
    · simp [heq]
  have hcard : (forestCollisionProfiles n L x).card ≤ 2 :=
    (Finset.card_le_card hsub).trans hpair
  have hvol : (∑ u ∈ forestCollisionProfiles n L x, (forestProfileLowerBox L u).card) ≤ 4 := by
    have hh := Finset.sum_le_sum (s := forestCollisionProfiles n L x) (g := fun _ ↦ 2) (fun u hu ↦ show (forestProfileLowerBox L u).card ≤ 2 from by
      rcases hfamily u hu with rfl | rfl
      · exact hvcard
      · exact hwcard)
    simp only [Finset.sum_const,smul_eq_mul] at hh
    omega
  have hpack := profile_volume_card_bound_of_valid_chain_forest L hL g hg E x b hchain
  simp only [← forestProfileLowerBox_card] at hpack
  have hgap : 2^n ≤ Fintype.card G+4 := by omega
  refine ⟨hgap,?_⟩
  have hlog : 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  norm_num at hpow
  unfold globalBound
  omega

/-- Actual bounded profiles with the same overflow pattern coincide. -/
theorem forestCollisionProfiles_eq_of_same_overflow
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hpattern : ∀ i, 2^(L i)-1 < (w i).val ↔ 2^(L i)-1 < (v i).val) : w=v := by
  classical
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have he := small_forest_profile_eq_of_same_overflow L hL hwide g hg E x b hchain
    (fun i ↦ (w i).val) (fun i ↦ (v i).val)
    (fun i ↦ by have := (w i).isLt; omega) (fun i ↦ by have := (v i).isLt; omega)
    hwm.1 hvm.1 hwm.2 hvm.2 hpattern
  funext i
  exact Fin.ext (congrFun he i)

/-- An axis base and an overflow in an entirely compatible cyclic
profile family force that family to be exactly the base and one strip.
Thus no family-exhaustion premise is needed for the four-point deficit
or the sharp global bound in this class. -/
theorem compatible_axis_base_overflow_family_global_bound
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ u ∈ forestCollisionProfiles n L x, ∀ i, i ≠ j → Even (u i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^n ≤ N+4 ∧ globalBound n ≤ N := by
  classical
  have hsmall : ∀ u ∈ forestCollisionProfiles n L x, (u j).val < 2^(L j) := by
    intro u hu
    have hum : (∑ i, (u i).val)<n ∧
        (∑ i, (u i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hu
    have := Finset.single_le_sum (f := fun i ↦ (u i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hvlow : ∀ i, (v i).val ≤ 2^(L i)-1 := by
    intro i
    by_cases hij : i=j
    · subst i; have := hsmall v hv; omega
    · rw [hvz i hij]; omega
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw (hcompat w hw) a ha
  have hfamily : ∀ u ∈ forestCollisionProfiles n L x, u=v ∨ u=w := by
    intro u hu
    by_cases hulo : ∀ i, (u i).val ≤ 2^(L i)-1
    · left
      apply forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain u v hu hv
      intro i
      have := hulo i
      have := hvlow i
      omega
    · obtain ⟨c,hc⟩ := not_forall.mp hulo
      have hc' : 2^(L c)-1 < (u c).val := by omega
      by_cases hca : c=a
      · subst c
        right
        obtain ⟨_,hua,huz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) u hu (hcompat u hu) a hc'
        apply forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain u w hu hw
        intro i
        by_cases hij : i=j
        · subst i; have := hsmall u hu; have := hsmall w hw; omega
        · by_cases hia : i=a
          · subst i; omega
          · rw [huz i hij hia,hwz i hij hia]
      · exact False.elim (no_base_with_two_compatible_strips_in_even_cyclic_forest hn hN hr L hL hwide
          g hg E x b hchain hgen j hwidth w u v hw hu hv (hcompat w hw) (hcompat u hu)
          a c (Ne.symm hca) ha hc' hvlow)
  simpa only [ZMod.card] using axis_base_strip_family_four_point_gap_and_global_bound hn hr L hL hwide
    g hg E x b hchain hgen j hwidth w v hw hv (hcompat w hw) a ha hvz hfamily

end MinModulus
