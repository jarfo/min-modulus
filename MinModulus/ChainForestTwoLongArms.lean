import MinModulus.ChainForestCollisionProfiles

/-! Exterior columns with two long arms and arbitrary remaining arms.
Joint-distance collisions replace the former all-long relation hypothesis.
An explicit binomial threshold gives the binary bound and original G1
half descent for this class. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- A subbinary valid forest cannot have a zero boundary in an arm
of width at least 2n+1. An actual small profile and this period would
produce two distinct high-weight points with the same value. -/
theorem boundary_ne_zero_of_subbinary_wide_arm
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a)) :
    2^(L a) • x a ≠ 0 := by
  classical
  intro hz
  obtain ⟨w,hw⟩ := forestCollisionProfiles_nonempty_of_subbinary L hL g hg E x b hchain hsub
  have hw' := (Finset.mem_filter.mp hw).2
  have hwa : (w a).val < n :=
    (Finset.single_le_sum (f := fun i ↦ (w i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans_lt hw'.1
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    omega
  let q := fun i ↦ if 2^(L i)-1 < (w i).val then 2^(L i)-1 else 0
  have hq : ∀ i, q i < 2^(L i) := by
    intro i
    have : 0 < 2^(L i) := by positivity
    dsimp only [q]
    split_ifs <;> omega
  have hqb : ∀ i, (w i).val ≤ 2^(L i)-1+q i ∧ q i ≤ (w i).val := by
    intro i
    have := (w i).isLt
    dsimp only [q]
    split_ifs <;> omega
  have hqa : q a=0 := by dsimp only [q]; rw [if_neg (by omega)]
  obtain ⟨p,hp,hip,_,_⟩ := realize_small_forest_profile L hwide x (fun i ↦ (w i).val) q
    hw'.1 hw'.2 hq (fun i ↦ (hqb i).1) (fun i ↦ (hqb i).2)
  let P := fun i ↦ if i=a then n else p i
  let Q := fun i ↦ if i=a then n+(w a).val+1 else q i
  have hP : ∀ i, P i < 2^(L i) := by
    intro i
    by_cases hi : i=a
    · subst i; dsimp only [P]; rw [if_pos rfl]; omega
    · simpa only [P,if_neg hi] using hp i
  have hQ : ∀ i, Q i < 2^(L i) := by
    intro i
    by_cases hi : i=a
    · subst i; dsimp only [Q]; rw [if_pos rfl]; omega
    · simpa only [Q,if_neg hi] using hq i
  have hPs : n ≤ ∑ i, P i := by
    have hh := Finset.single_le_sum (f := P) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    simpa only [P,if_pos rfl] using hh
  have hQs : n ≤ ∑ i, Q i := by
    have hh := Finset.single_le_sum (f := Q) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    have hQa : Q a=n+(w a).val+1 := by simp [Q]
    rw [hQa] at hh
    omega
  have hid : ∀ i, P i+(w i).val+(if i=a then 2^(L a) else 0)=2^(L i)-1+Q i := by
    intro i
    by_cases hi : i=a
    · subst i
      simp only [P,Q,if_pos rfl,if_true]
      omega
    · simpa only [P,Q,if_neg hi,add_zero] using hip i
  have he : (∑ i, P i • x i)=∑ i, Q i • x i := by
    have hh : (∑ i, P i • x i)+(∑ i, (w i).val • x i)+
        (∑ i, (if i=a then 2^(L a) else 0) • x i)=
        (∑ i, (2^(L i)-1) • x i)+(∑ i, Q i • x i) := by
      simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
    have hu : (∑ i, (if i=a then 2^(L a) else 0) • x i)=0 := by
      simpa only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hz
    rw [hw'.2,hu,add_zero] at hh
    exact add_right_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hh)
  have hh := high_box_injective_of_valid_chain_forest L hL g hg E x b hchain P Q hP hQ hPs hQs he
  have heqa := congrFun hh a
  simp only [P,Q,if_pos rfl] at heqa
  omega

/-- Two sufficiently long named arms force every short exterior
column representation to have zero coordinate on its own axis.
All remaining arms may be arbitrarily short. -/
theorem pivot_eq_zero_of_two_long_arm_column_collision
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a) (ha : n < 2^(L a))
    (t : ℕ) (ht : n+t < 2^(L j))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x j) : p a=0 := by
  classical
  by_contra hnot
  let P := fun i ↦ if i=a then 0 else p i
  let Q := fun i ↦ if i=a then 2^(L a)-p a else if i=j then t else 0
  have hP : ∀ i, P i < 2^(L i) := by
    intro i
    dsimp only [P]
    split_ifs
    · positivity
    · exact hp i
  have hQ : ∀ i, Q i < 2^(L i) := by
    intro i
    dsimp only [Q]
    split_ifs with hi hij
    · subst i; have := hp a; omega
    · subst i; omega
    · positivity
  have hPsum : (∑ i, P i • x i)+p a • x a=∑ i, p i • x i := by
    have hsplit : ∀ i, p i • x i=P i • x i+(if i=a then p a • x a else 0) := by
      intro i
      by_cases hi : i=a <;> simp [P,hi]
    calc
      _=∑ i, (P i • x i+(if i=a then p a • x a else 0)) := by
        simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      _=_ := (Finset.sum_congr rfl (fun i _ ↦ hsplit i)).symm
  have hQsum : (∑ i, Q i • x i)=(2^(L a)-p a) • x a+t • x j := by
    have hsplit : ∀ i, Q i • x i=(if i=a then (2^(L a)-p a) • x a else 0)+
        (if i=j then t • x j else 0) := by
      intro i
      by_cases hi : i=a
      · subst i; simp [Q,Ne.symm hja]
      · by_cases hij : i=j
        · subst i; simp [Q,hja]
        · simp [Q,hi,hij]
    simp only [hsplit,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hPQ : (∑ i, P i • x i)=∑ i, Q i • x i := by
    apply add_right_cancel (b := p a • x a)
    rw [hPsum,heq,hQsum]
    have hsplit : (2^(L a)-p a) • x a+p a • x a=2^(L a) • x a := by
      rw [← add_nsmul,Nat.sub_add_cancel (hp a).le]
    calc
      _=((2^(L a)-p a) • x a+p a • x a)+t • x j := by rw [hsplit]
      _=_ := by abel
  have hne : P ≠ Q := by
    intro hh
    have he := congrFun hh a
    simp only [P,Q,if_pos rfl] at he
    have := hp a
    omega
  have hpdist : n ≤ ∑ i, (2^(L i)-1-P i) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1-P i)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    have hPa : P a=0 := by simp [P]
    rw [hPa,Nat.sub_zero] at hh
    omega
  have hqdist : n ≤ ∑ i, (2^(L i)-1-Q i) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1-Q i)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have hQj : Q j=t := by simp [Q,hja]
    rw [hQj] at hh
    omega
  rcases box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain
    P Q hP hQ hne hPQ with h | h <;> omega

/-- A genuine boundary in either of two long arms is missing from
the entire ordinary box at every subbinary modulus. -/
theorem boundary_not_in_box_of_subbinary_two_long_arms
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a j : β) (hja : j ≠ a)
    (ha : 2*n+1 ≤ 2^(L a)) (hj : n < 2^(L j))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a := by
  classical
  intro he
  have hpa := pivot_eq_zero_of_two_long_arm_column_collision L hL g hg E x b hchain a j hja
    (by omega) 0 (by omega) p hp (by simpa using he)
  have hpos : ∃ i, 0 < p i := by
    by_contra hnot
    have hz : ∀ i, p i=0 := by push Not at hnot; intro i; have := hnot i; omega
    have hzero : 2^(L a) • x a=0 := by simpa only [hz,zero_smul,Finset.sum_const_zero] using he.symm
    exact boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha hzero
  obtain ⟨k,_,e,hentry⟩ := actual_entry_of_valid_positive_forest_boundary L hL g hg E x b hchain
    a (by omega) p hp hpa he.symm hpos
  have htop : 2 • (g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)=2^(L a) • x a := by
    have hLa : L a-1+1=L a := by have := hL a; omega
    simp only [hchain,smul_smul,← pow_succ',hLa]
  apply hgenuine (E ⟨k,e⟩)
  have hk := hchain k e
  rw [← hentry,← htop,two_nsmul] at hk
  apply add_right_cancel (b := b)
  simp only [two_nsmul]
  abel_nf at hk ⊢
  exact hk

/-- One other long arm makes the whole seed interval injective,
by placing both points in the high-weight box. -/
theorem seed_interval_injective_of_other_long_arm
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a) (ha : n < 2^(L a)) :
    Function.Injective (fun t : Fin (2^(L j)) ↦ t.val • x j) := by
  classical
  let P := fun (t : Fin (2^(L j))) i ↦ if i=a then n else if i=j then t.val else 0
  have hp : ∀ t i, P t i < 2^(L i) := by
    intro t i
    dsimp only [P]
    split_ifs with hi hij
    · subst i; exact ha
    · subst i; exact t.isLt
    · positivity
  have hs : ∀ t, n ≤ ∑ i, P t i := by
    intro t
    have hh := Finset.single_le_sum (f := P t) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    simpa only [P,if_pos rfl] using hh
  have heval : ∀ t, (∑ i, P t i • x i)=n • x a+t.val • x j := by
    intro t
    have hpoint : ∀ i, P t i • x i=(if i=a then n • x a else 0)+(if i=j then t.val • x j else 0) := by
      intro i
      by_cases hi : i=a
      · subst i; simp [P,Ne.symm hja]
      · by_cases hij : i=j
        · subst i; simp [P,hja]
        · simp [P,hi,hij]
    simp only [hpoint,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  intro t u he
  change t.val • x j=u.val • x j at he
  have hh := high_box_injective_of_valid_chain_forest L hL g hg E x b hchain (P t) (P u)
    (hp t) (hp u) (hs t) (hs u) (by rw [heval,heval,he])
  have hj := congrFun hh j
  exact Fin.ext (by simpa [P,hja] using hj)

/-- An entire tiny column is missing with just two named long arms.
The other arms need no width restriction or supplied relation. -/
theorem tiny_column_not_in_box_of_subbinary_two_long_arms
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a j : β) (hja : j ≠ a)
    (ha : 2*n+1 ≤ 2^(L a)) (hLj : 4 ≤ L j) (hj : n+2^(L j-4) < 2^(L j))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t ≤ 2^(L j-4))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x j := by
  classical
  intro heq
  have hpa := pivot_eq_zero_of_two_long_arm_column_collision L hL g hg E x b hchain
    a j hja (by omega) t (by omega) p hp heq
  have hpj : p j < t := by
    by_contra hnot
    let P := fun i ↦ if i=j then p j-t else p i
    have hP : ∀ i, P i < 2^(L i) := by
      intro i
      by_cases hi : i=j
      · subst i; simpa only [P,if_pos rfl] using (Nat.sub_le (p j) t).trans_lt (hp j)
      · simpa only [P,if_neg hi] using hp i
    have hsum : (∑ i, P i • x i)+t • x j=∑ i, p i • x i := by
      have hs : ∀ i, p i • x i=P i • x i+(if i=j then t • x j else 0) := by
        intro i
        by_cases hi : i=j
        · subst i
          simp only [P,if_pos rfl,if_true]
          rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
        · simp only [P,if_neg hi,add_zero]
      calc
        _=∑ i, (P i • x i+(if i=j then t • x j else 0)) := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        _=_ := (Finset.sum_congr rfl (fun i _ ↦ hs i)).symm
    have hrep : (∑ i, P i • x i)=2^(L a) • x a := add_right_cancel (hsum.trans heq)
    exact boundary_not_in_box_of_subbinary_two_long_arms L hL g hg E x b hchain hsub a j hja
      ha (by omega) hgenuine P hP hrep
  exact not_validTuple_of_tiny_exterior_column_collision L hL g E x b hchain a j hja
    (by omega) hLj t p hp hpa hpj (by omega) heq hg

/-- The missing column is charged against the arbitrary-arm
binomial packing. This counts actual distinct ambient residues. -/
theorem two_long_arm_column_charged_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a j : β) (hja : j ≠ a)
    (ha : 2*n+1 ≤ 2^(L a)) (hLj : 4 ≤ L j) (hj : n+2^(L j-4) < 2^(L j))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(2^(L j-4)+1) ≤ Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  let f : Fin (2^(L j-4)+1) → G := fun t ↦ 2^(L a) • x a+t.val • x j
  have hi : Function.Injective f := by
    intro t u he
    have he' : t.val • x j=u.val • x j := add_left_cancel he
    have hh := seed_interval_injective_of_other_long_arm L hL g hg E x b hchain a j hja (by omega)
      (a₁ := ⟨t.val,by have := t.isLt; omega⟩) (a₂ := ⟨u.val,by have := u.isLt; omega⟩) he'
    exact Fin.ext (congrArg (fun z : Fin (2^(L j)) ↦ z.val) hh)
  let F := Finset.univ.image f
  have hcard : F.card=2^(L j-4)+1 := by
    simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact tiny_column_not_in_box_of_subbinary_two_long_arms L hL g hg E x b hchain
      hsub a j hja ha hLj hj hgenuine t.val (by have := t.isLt; omega) p hp
  have hh := binomial_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain F havoid
  simpa only [hcard] using hh

/-- One capacious genuine arm and one exponentially charging arm
already force the binary bound. Every other arm is unrestricted. -/
theorem binary_card_bound_of_genuine_two_large_arms
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a) (ha : 2*n+1 ≤ 2^(L a)) (hLj : 4 ≤ L j)
    (hnj : n ≤ 2^(L j-4))
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β) ≤ 2^(L j-4)+1)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have hpow : 2^(L j)=16*2^(L j-4) := by
    rw [show L j=4+(L j-4) by omega,pow_add]
    norm_num
  have hpos : 0 < 2^(L j-4) := by positivity
  have hj : n+2^(L j-4) < 2^(L j) := by omega
  have hh := two_long_arm_column_charged_card_bound hn L hL g hg E x b hchain
    (by omega) a j hja ha hLj hj hgenuine
  omega

/-- The three-chain binomial error is at most the cube of the
actual tuple length. This is a uniform arithmetic inequality. -/
theorem three_chain_binomial_le_cube {n : ℕ} (hn : 0 < n) : (n+2).choose 3 ≤ n^3 := by
  have hh := Nat.ascFactorial_eq_factorial_mul_choose' n 3
  norm_num [Nat.ascFactorial_succ,Nat.ascFactorial_zero,
    show n+3-1=n+2 by omega] at hh
  have hprod : (n+2)*(n+1)*n ≤ (3*n)*(2*n)*n :=
    Nat.mul_le_mul_right n (Nat.mul_le_mul (by omega : n+2 ≤ 3*n) (by omega : n+1 ≤ 2*n))
  nlinarith

/-- For three genuine chains at length at least 67, TWO arms of
width greater than 2n suffice for the binary bound. The third arm may
have any positive length. The largest arm supplies the exponential
column charge automatically. -/
theorem binary_card_bound_of_genuine_three_chains_two_wide_arms
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (a₀ a₁ : β) (hne : a₀ ≠ a₁)
    (ha₀ : 2*n+1 ≤ 2^(L a₀)) (ha₁ : 2*n+1 ≤ 2^(L a₁)) :
    2^n ≤ Fintype.card G := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hnL : n ≤ 3*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 23 ≤ L j := by omega
  have hcube : n^3 ≤ 2^(L j-4) :=
    (Nat.pow_le_pow_left hnL 3).trans (three_length_cube_le_exponential hLj)
  have hn_cube : n ≤ n^3 := by
    have h1 : 1 ≤ n*n := by nlinarith
    have hh := Nat.mul_le_mul_left n h1
    nlinarith
  obtain ⟨a,hja,ha⟩ : ∃ a, j ≠ a ∧ 2*n+1 ≤ 2^(L a) := by
    by_cases he : j=a₀
    · exact ⟨a₁,by rw [he]; exact hne,ha₁⟩
    · exact ⟨a₀,he,ha₀⟩
  apply binary_card_bound_of_genuine_two_large_arms (by omega) L hL g hg E x b hchain
    a j hja ha (by omega) (hn_cube.trans hcube) _ (hgenuine a)
  simp only [hr,show n+3-1=n+2 by omega]
  exact (three_chain_binomial_le_cube (by omega)).trans (hcube.trans (Nat.le_succ _))

/-- Every subbinary genuine three-chain forest of length at least
67 has two arms of width at most 2n. Consequently one actual chain
contains all but at most 2*floor(log_2(2n)) coordinates. -/
theorem exists_dominant_chain_of_subbinary_genuine_three_chain_forest
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hsub : Fintype.card G < 2^n) :
    ∃ j, (∀ i, i ≠ j → 2^(L i) ≤ 2*n) ∧ n-2*Nat.log 2 (2*n) ≤ L j := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hrest : ∀ i, i ≠ j → 2^(L i) ≤ 2*n := by
    intro i hij
    by_contra hnot
    have hjpow := Nat.pow_le_pow_right (by decide : 0 < 2) (hmax i (Finset.mem_univ _))
    have hh := binary_card_bound_of_genuine_three_chains_two_wide_arms hn hr L hL g hg E x b hchain
      hgenuine i j hij (by omega) (by omega)
    omega
  refine ⟨j,hrest,?_⟩
  have hlog : ∀ i ∈ Finset.univ.erase j, L i ≤ Nat.log 2 (2*n) := by
    intro i hi
    exact Nat.le_log_of_pow_le (by decide) (hrest i (Finset.mem_erase.mp hi).1)
  have hsmall := Finset.sum_le_sum hlog
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,hr,smul_eq_mul] at hsmall
  have hsum := Finset.sum_erase_add Finset.univ L (Finset.mem_univ j)
  rw [hsize] at hsum
  omega

/-- Direct original G1 half descent when two of the actual chains
have width greater than twice the parent length, from length 67.
The third arm is unrestricted and genuine endpoints are derived. -/
theorem admitsValidTuple_half_of_critical_three_chains_two_wide_arms
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a)
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val)
    (a₀ a₁ : A) (hne : a₀ ≠ a₁)
    (ha₀ : 2*(n+1)+1 ≤ 2^(L a₀)) (ha₁ : 2*(n+1)+1 ≤ 2^(L a₁)) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half
    hq g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a.val a.property t
  have hh := binary_card_bound_of_genuine_three_chains_two_wide_arms (by omega) hr L hL
    g hg E x b hchain hgen a₀ a₁ hne ha₀ ha₁
  rw [ZMod.card] at hh
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  omega

/-- Original large three-escape no-half data now extract a single
dominant chain with two logarithmically short companions. The actual
forest, endpoints, two odd seeds and full joint span are preserved. -/
theorem exists_dominant_forest_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    A.card=3 ∧ ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n+1 ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ Fin (n+1), ∃ x : A → ZMod (2^(s+1)*q),
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
      (∀ a : A, ∀ j, g j ≠ 2 • g a.val+b) ∧
      2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card ∧
      AddSubgroup.closure (Set.range x)=⊤ ∧
      ∃ j, (∀ a, a ≠ j → 2^(L a) ≤ 2*(n+1)) ∧
        n+1-2*Nat.log 2 (2*(n+1)) ≤ L j := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a t
  have hsub : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
    rw [ZMod.card]
    exact hc.trans_le (Nat.sub_le _ _)
  exact ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,
    exists_dominant_chain_of_subbinary_genuine_three_chain_forest (by omega) hr L hL
      g hg E x b hchain hgen hsub⟩

/-- The dominant chain is an actual coherent SI prefix in the
original modulus, with at most 2*floor(log_2(2k)) extra coordinates.
No unit multiplier, quotient transport or independent lift is assumed. -/
theorem exists_logarithmic_extra_prefix_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ m, n+1-2*Nat.log 2 (2*(n+1)) ≤ m ∧
      ∃ e : Fin m ↪ Fin (n+1), ∃ c d : ZMod (2^(s+1)*q),
        ∀ i, g (e i)=(2^i.val-1) • c+d := by
  obtain ⟨_,L,_,_,E,x,hchain,_,_,_,_,j,_,hlarge⟩ :=
    exists_dominant_forest_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  let e : Fin (L j) ↪ Fin (n+1) :=
    { toFun := fun i ↦ E ⟨j,i⟩
      inj' := by
        intro i k he
        exact eq_of_heq (Sigma.mk.inj (E.injective he)).2 }
  refine ⟨L j,hlarge,e,x j,x j-b,?_⟩
  intro i
  have hh := hchain j i
  have hpow : (2^i.val-1) • x j+x j=2^i.val • x j := by
    conv_lhs => rhs; rw [← one_nsmul (x j)]
    have hpos : 1 ≤ 2^i.val := Nat.one_le_pow _ _ (by decide)
    rw [← add_nsmul,Nat.sub_add_cancel hpos]
  apply add_right_cancel (b := b)
  change g (E ⟨j,i⟩)+b=((2^i.val-1) • x j+(x j-b))+b
  rw [hh,← hpow]
  abel

end MinModulus
