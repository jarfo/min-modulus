import MinModulus.ChainForestProfileAxisOnly

/-! Comparable distinct small profiles must change a length-one arm.
Repeated positive zero relations give a strict coin saving uniformly
in all arities. Consequently other profiles lie below an axis base
when every arm has a second entry, and a zero target in that class
satisfies the binary bound at even modulus with an odd seed.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A Mersenne weight needs at least one binary coin per chain entry. -/
theorem length_le_dsum_of_mersenne_value {L : ℕ} (hL : 0 < L)
    (u : ℕ → ℕ) (hu : val L u=2^L-1) : L ≤ dsum L u := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  have hh := gmin_le_dsum k u
  rwa [hu,gmin_ones] at hh

/-- A strict forest coin saving itself excludes the all-ones weight,
so no separate coordinate-inequality premise is needed for the rival. -/
theorem not_validTuple_of_chain_forest_strict_coin_budget
    {n : ℕ} {β : Type*} [Fintype β] (L X : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (u : β → ℕ → ℕ) (hu : ∀ i, val (L i) (u i)=X i)
    (hlow : (∑ i, dsum (L i) (u i)) < n) (hhigh : n ≤ ∑ i, X i)
    (hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i) : ¬ ValidTuple g := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    by_contra hn
    have he : ∀ i, X i=2^(L i)-1 := by simpa using hn
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      length_le_dsum_of_mersenne_value (hL i) (u i) ((hu i).trans (he i)))
    omega
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hlow.le hhigh hneq hsum

/-- A positive zero relation supported on arms with second entries
cannot extend a small representation of the target to another small one.
Repeated doubles have fewer than n coins but enough weight to refine to n. -/
theorem not_validTuple_of_small_target_and_doublable_positive_zero
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v z : β → ℕ) (hzpos : 0 < ∑ i, z i)
    (hsmall : (∑ i, v i)+(∑ i, z i)<n)
    (hlong : ∀ i, 0 < z i → 2 ≤ L i)
    (hv : (∑ i, v i • x i)=∑ i, (2^(L i)-1) • x i)
    (hz : (∑ i, z i • x i)=0) : ¬ ValidTuple g := by
  classical
  let V := ∑ i, v i
  let Z := ∑ i, z i
  let q := (n-V-1)/Z
  have hVZ : V+Z<n := hsmall
  have hZ : 0 < Z := hzpos
  have hdiv := Nat.div_add_mod (n-V-1) Z
  have hmod := Nat.mod_lt (n-V-1) hZ
  have hq : 1 ≤ q := by
    by_contra hn
    have hq0 : (n-V-1)/Z=0 := Nat.eq_zero_of_not_pos hn
    rw [hq0,mul_zero,zero_add] at hdiv
    omega
  have hmul : q*Z ≤ n-V-1 := Nat.div_mul_le_self _ _
  have hZle : Z ≤ q*Z := by nlinarith
  have hlow : V+q*Z<n := by omega
  have hhigh : n ≤ V+2*q*Z := by
    have he : n-V-1+V+1=n := by omega
    change Z*q+(n-V-1)%Z=n-V-1 at hdiv
    nlinarith
  let X : β → ℕ := fun i ↦ v i+2*q*z i
  let u : β → ℕ → ℕ := fun i k ↦ (if k=0 then v i else 0)+(if k=1 then q*z i else 0)
  have hu : ∀ i, val (L i) (u i)=X i ∧ dsum (L i) (u i)=v i+q*z i := by
    intro i
    by_cases hzi : z i=0
    · simp [val,dsum,u,X,hzi,hL i]
    · have hLi : 1 < L i := by have := hlong i (by omega); omega
      constructor
      · simp [val,u,X,add_mul,Finset.sum_add_distrib,hL i,hLi]
        ring
      · simp [dsum,u,Finset.sum_add_distrib,hL i,hLi]
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have he : (∑ i, (2*q*z i) • x i)=(2*q) • ∑ i, z i • x i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
    simp only [X,add_nsmul,Finset.sum_add_distrib,he,hz,smul_zero,add_zero,hv]
  apply not_validTuple_of_chain_forest_strict_coin_budget L X hL g E x b hchain u (fun i ↦ (hu i).1)
  · simpa only [hu,Finset.sum_add_distrib,← Finset.mul_sum,V,Z] using hlow
  · simpa only [X,Finset.sum_add_distrib,← Finset.mul_sum,V,Z] using hhigh
  · exact hsum

/-- Distinct comparable small profiles must change a length-one arm.
Otherwise their positive difference can be repeated using actual doubles. -/
theorem exists_length_one_changed_arm_of_comparable_profiles
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hle : ∀ i, (v i).val ≤ (w i).val) (hne : w ≠ v) :
    ∃ i, (v i).val < (w i).val ∧ L i=1 := by
  classical
  by_contra hn
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  let z := fun i ↦ (w i).val-(v i).val
  have hpoint : ∀ i, (v i).val+z i=(w i).val := by intro i; dsimp only [z]; have := hle i; omega
  have hsmall : (∑ i, (v i).val)+(∑ i, z i)<n := by
    rw [← Finset.sum_add_distrib]
    simpa only [hpoint] using hwm.1
  have hpos : 0 < ∑ i, z i := by
    by_contra hnot
    have hs : (∑ i, z i)=0 := by omega
    apply hne
    funext i
    apply Fin.ext
    have hh := Finset.single_le_sum (f := z) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have := hpoint i
    omega
  have hlong : ∀ i, 0 < z i → 2 ≤ L i := by
    intro i hi
    have hlt : (v i).val < (w i).val := by dsimp only [z] at hi; omega
    have hnL : L i ≠ 1 := fun he ↦ hn ⟨i,hlt,he⟩
    have := hL i
    omega
  have hz : (∑ i, z i • x i)=0 := by
    apply add_left_cancel (a := ∑ i, (v i).val • x i)
    calc
      _=∑ i, ((v i).val+z i) • x i := by simp only [add_nsmul,Finset.sum_add_distrib]
      _=∑ i, (w i).val • x i := by simp only [hpoint]
      _=∑ i, (v i).val • x i := hwm.2.trans hvm.2.symm
      _=_ := (add_zero _).symm
  exact not_validTuple_of_small_target_and_doublable_positive_zero L hL g E x b hchain
    (fun i ↦ (v i).val) z hpos hsmall hlong hvm.2 hz hg

/-- If every arm has a second entry, every distinct actual profile lies
strictly below an axis profile on that axis. No parity, dimension, wide-box,
or genuine-endpoint premise is needed. -/
theorem profile_below_axis_profile_of_all_arms_length_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hne : w ≠ v) :
    (w j).val < (v j).val := by
  by_contra hn
  have hle : ∀ i, (v i).val ≤ (w i).val := by
    intro i
    by_cases hij : i=j
    · subst i; omega
    · rw [hvz i hij]; omega
  obtain ⟨i,_,hi⟩ := exists_length_one_changed_arm_of_comparable_profiles L (fun i ↦ by have := hL i; omega)
    g hg E x b hchain w v hw hv hle hne
  have := hL i
  omega

/-- A zero profile is the entire family if every arm has a second entry. -/
theorem profile_eq_zero_profile_of_all_arms_length_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hvzero : ∀ i, (v i).val=0) : w=v := by
  by_contra hne
  obtain ⟨i,_,hi⟩ := exists_length_one_changed_arm_of_comparable_profiles L (fun i ↦ by have := hL i; omega)
    g hg E x b hchain w v hw hv (fun i ↦ by rw [hvzero i]; omega) hne
  have := hL i
  omega

/-- With an odd seed in an even cyclic group, a zero profile and
second entries on every arm force the binary bound. No even seed is needed. -/
theorem binary_bound_of_zero_profile_and_all_arms_length_two
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvzero : ∀ i, (v i).val=0) : 2^n ≤ N := by
  classical
  have hfamily : forestCollisionProfiles n L x={v} := by
    ext w
    constructor
    · intro hw
      have he := profile_eq_zero_profile_of_all_arms_length_two L hL g hg E x b hchain w v hw hv hvzero
      simpa only [Finset.mem_singleton] using he
    · intro hw
      have he : w=v := by simpa only [Finset.mem_singleton] using hw
      simpa only [he] using hv
  have hbias : forestProfileParityBias L x v=1 := by simp [forestProfileParityBias,hvzero]
  have hvol : (∏ i, min ((v i).val+1) (2*(2^(L i)-1)+1-(v i).val))=1 := by simp [hvzero]
  have hh := explicit_profile_bias_card_bound hN L (fun i ↦ by have := hL i; omega) g hg E x b hchain hodd
  rw [hfamily,Finset.sum_singleton,Finset.sum_singleton,hbias,hvol] at hh
  norm_num at hh
  exact_mod_cast hh

/-- A zero target in an even cyclic forest with all arm lengths at
least two satisfies the binary bound whenever one seed is odd, uniformly
in the number and lengths of the chains. -/
theorem binary_bound_of_zero_target_forest_length_two
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (hzero : (∑ i, (2^(L i)-1) • x i)=0) :
    2^n ≤ N := by
  classical
  obtain ⟨a,ha⟩ := hodd
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hn : 0 < n := by
    have := Finset.single_le_sum (f := L) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    have := hL a
    omega
  let v : ∀ i, Fin (2*(2^(L i)-1)+1) := fun i ↦ ⟨0,by omega⟩
  have hv : v ∈ forestCollisionProfiles n L x := by
    simp only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and,v,
      zero_nsmul,Finset.sum_const_zero,hzero]
    exact ⟨hn,True.intro⟩
  exact binary_bound_of_zero_profile_and_all_arms_length_two hN L hL g hg E x b hchain ⟨a,ha⟩ v hv (fun i ↦ rfl)

end MinModulus
