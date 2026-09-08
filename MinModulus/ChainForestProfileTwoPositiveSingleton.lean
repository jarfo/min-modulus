import MinModulus.ChainForestProfileCompatibleSupport

/-! A rank-three profile with two positive even companion coefficients
is the complete profile family when its axis is sufficiently wide.
Quantitative rectangle separation and uniform binary coin savings turn
every coexisting overflow into an actual shifted rival, in any abelian
group. In the cyclic parity setting the surviving rectangle has an
explicit height-charged deficit bound. The unrestricted conjecture is open. -/

namespace MinModulus
open Finset

/-- An actual overflow's lower edge lies strictly beyond the base
coefficient on that arm. Otherwise the two profile rectangles meet.
This permits arbitrary arity, seeds and coefficients on all other arms. -/
theorem underflow_profile_below_single_overflow_lower_edge
    {n : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1)
    (a : β) (hwa : 2^(L a)-1 < (w a).val)
    (hwlow : ∀ i, i ≠ a → (w i).val ≤ 2^(L i)-1) :
    (v a).val < (w a).val-(2^(L a)-1) := by
  classical
  by_contra hh
  let q : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨if i=a then (w i).val-(2^(L i)-1) else 0,by
    split_ifs with hi
    · have := (w i).isLt
      have := Nat.two_pow_pos (L i)
      omega
    · positivity⟩
  have hqw : q ∈ forestProfileLowerBox L w := by
    simp only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i
    by_cases hi : i=a
    · subst i
      have := (w a).isLt
      have := Nat.two_pow_pos (L a)
      simp only [q,if_true]
      omega
    · have := hwlow i hi
      simp only [q,if_neg hi]
      omega
  have hqv : q ∈ forestProfileLowerBox L v := by
    simp only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i
    have := hvlow i
    by_cases hi : i=a
    · subst i
      simp only [q,if_true]
      omega
    · simp only [q,if_neg hi]
      omega
  have hne : w ≠ v := by
    intro he
    have := congrArg (fun p ↦ (p a).val) he
    have := hvlow a
    omega
  exact (Finset.disjoint_left.mp (forestProfileLowerBox_disjoint_of_ne L hL hwide
    g hg E x b hchain w v hw hv hne)) hqw hqv

/-- The dyadic excess of any actual three-chain overflow is larger
than the corresponding coefficient of every no-overflow base. -/
theorem three_chain_overflow_excess_gt_underflow_base
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1)
    (a : β) (hwa : 2^(L a)-1 < (w a).val) :
    ∃ e, (w a).val+1=2^(L a)+2^e ∧ (v a).val < 2^e := by
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  obtain ⟨e,he⟩ := dyadic_excess_of_three_chain_profile_overflow hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) hbound hwm.1 hwm.2 a hwa
  have hother := dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) hbound hwm.1 hwm.2 a hwa
  have hs := underflow_profile_below_single_overflow_lower_edge L hL hwide g hg E x b hchain
    v w hv hw hvlow a hwa (fun i hi ↦ (hother i hi).1.le)
  exact ⟨e,he,by have := Nat.two_pow_pos (L a); omega⟩

/-- A base with two positive even companions leaves no other
compatible profile. Every distinct profile overflows one companion
with dyadic excess strictly greater than that base coefficient. -/
theorem other_profile_incompatible_overflow_of_two_positive_even_companions
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hne : w ≠ v) :
    (¬ ∀ i, i ≠ j → Even (w i).val) ∧
      ∃ c e, c ≠ j ∧ 2^(L c)-1 < (w c).val ∧
        (w c).val+1=2^(L c)+2^e ∧ (v c).val < 2^e := by
  classical
  obtain ⟨hvlow,_⟩ := two_positive_even_companions_interior_power_budget
    hr L hL g hg E x b hchain j a k haj hkj hka v hv ha heva hk hevk
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hover : ∃ c, 2^(L c)-1 < (w c).val := by
    by_contra hh
    have hwlow : ∀ i, (w i).val ≤ 2^(L i)-1 := by
      intro i; by_contra hi; exact hh ⟨i,by omega⟩
    exact hne (forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain
      w v hw hv (fun i ↦ by have := hwlow i; have := hvlow i; omega))
  obtain ⟨c,hc⟩ := hover
  have hcj : c ≠ j := by
    intro he; subst c
    have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  obtain ⟨e,he,hsep⟩ := three_chain_overflow_excess_gt_underflow_base hr L hL hwide
    g hg E x b hchain v w hv hw hvlow c hc
  refine ⟨?_,c,e,hcj,hc,he,hsep⟩
  intro hcompat
  have hstrip := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth
    w hw hcompat c hc
  have hz : (v c).val=0 := by rw [hstrip.2.1] at he; omega
  have hfull : ({j,a,k} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hm : c ∈ ({j,a,k} : Finset β) := by rw [hfull]; exact Finset.mem_univ _
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hcj' | hca | hck
  · exact hcj hcj'
  · subst c; omega
  · subst c; omega

/-- A two-positive-compatible base is the entire signed parity
correction: its height survives and every other actual profile has zero
bias. This identity concerns the complete family, not selected profiles. -/
theorem profile_bias_sum_eq_height_of_two_positive_even_companions
    {n N : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    (∑ w ∈ forestCollisionProfiles n L x, forestProfileParityBias L x w)=((v j).val+1 : ℕ) := by
  classical
  obtain ⟨hvlow,_⟩ := two_positive_even_companions_interior_power_budget
    hr L hL g hg E x b hchain j a k haj hkj hka v hv ha heva hk hevk
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hfull : ({j,a,k} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcompat : ∀ i, i ≠ j → Even (v i).val := by
    intro i hij
    have hm : i ∈ ({j,a,k} : Finset β) := by rw [hfull]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hi | hi | hi
    · exact False.elim (hij hi)
    · subst i; exact heva
    · subst i; exact hevk
  have hvbias := profile_bias_eq_signed_height_of_unique_even_seed L hL x j hj hother hwidth v hvm.1 hcompat
  have hzero : (Finset.univ.filter (fun i ↦ 2^(L i)-1 < (v i).val))=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have := hvlow i
    omega
  rw [hzero,Finset.card_empty,pow_zero,one_mul] at hvbias
  rw [Finset.sum_eq_single v]
  · simpa only [Nat.cast_add,Nat.cast_one] using hvbias
  · intro w hw hne
    have hc := (other_profile_incompatible_overflow_of_two_positive_even_companions
      hr L hL hwide g hg E x b hchain j a k haj hkj hka hwidth v hv ha heva hk hevk w hw hne).1
    push Not at hc
    obtain ⟨i,hij,hi⟩ := hc
    exact profile_parity_bias_eq_zero_of_odd_coordinate L x w i (hother i hij) (Nat.not_even_iff_odd.mp hi)
  · exact fun hn ↦ False.elim (hn hv)

/-- The complete parity-corrected deficit bound for a base with two
positive even companions retains one full base height. Other profiles
can contribute only their unsigned rectangle volumes. -/
theorem height_charged_profile_bound_of_two_positive_even_companions
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    2^n+((v j).val+1) ≤ N+∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  have hh := explicit_profile_bias_card_bound hN L hL g hg E x b hchain ⟨a,hother a haj⟩
  rw [profile_bias_sum_eq_height_of_two_positive_even_companions hr L hL hwide
    g hg E x b hchain j a k haj hkj hka hwidth hj hother v hv ha heva hk hevk,
    abs_of_nonneg (Nat.cast_nonneg _)] at hh
  exact_mod_cast hh

/-- Allowing one larger binary coin can only reduce the greedy cost. -/
theorem gmin_succ_width_le (w z : ℕ) : gmin (w+1) z ≤ gmin w z := by
  induction w generalizing z with
  | zero => simp only [gmin]; omega
  | succ w ih =>
    simp only [gmin]
    exact Nat.add_le_add_left (ih (z/2)) _

/-- Greedy cost is antitone in the largest available binary exponent. -/
theorem gmin_antitone_width {w v : ℕ} (hw : w ≤ v) (z : ℕ) : gmin v z ≤ gmin w z := by
  induction v,hw using Nat.le_induction with
  | base => exact le_rfl
  | succ v hv ih => exact (gmin_succ_width_le v z).trans ih

/-- An even weight loses no coins when divided by two with its width. -/
theorem gmin_double_weight (w z : ℕ) : gmin (w+1) (2*z)=gmin w z := by
  simp [gmin]

/-- A small positive dyadic increment after an arbitrary positive
height drop stays inside the original axis coin budget. -/
theorem gmin_dyadic_increment_height_drop
    {L u H : ℕ} (hu : u < L) (hH : 0 < H) :
    gmin (L-1) (2^L-1+2^u-H) ≤ L := by
  have hL : 0 < L := by omega
  have hKpos := Nat.two_pow_pos L
  have hK : 2^L=2*2^(L-1) := by rw [← pow_succ',Nat.sub_add_cancel hL]
  by_cases hle : 2^u ≤ H
  · have hz : 2^L-1+2^u-H < 2^L := by have := Nat.two_pow_pos L; omega
    have hc := gmin_le_of_lt_binary_width (w:=L-1) (t:=2^L-1+2^u-H)
      (by simpa only [Nat.sub_add_cancel hL] using hz)
    omega
  · have hup : 0 < u := by
      by_contra hn
      have hu0 : u=0 := by omega
      have hs : 2^u=1 := by rw [hu0]; rfl
      exact hle (by rw [hs]; omega)
    let d := 2^u-H-1
    have hd : d < 2^u-1 := by dsimp [d]; omega
    have hc := gmin_le_of_lt_binary_ones (w:=u-1) (t:=d)
      (by simpa only [Nat.sub_add_cancel hup] using hd)
    have hc' := (gmin_antitone_width (show u-1 ≤ L-1 by omega) d).trans hc
    have hz : 2^L-1+2^u-H=d+2*2^(L-1) := by dsimp [d]; omega
    rw [hz,gmin_add_top_multiple]
    omega

/-- The non-overflow companion in a shifted profile pair saves one
coin whenever its old coefficient is a positive even binary power. -/
theorem gmin_shifted_positive_power_companion
    {L f t : ℕ} (ht : 0 < t) (hfL : f < L) (htL : t < L) :
    gmin (L-1) (2^L+2^f-2^t-2) ≤ L-1 := by
  have hL : 2 ≤ L := by omega
  by_cases hf0 : f=0
  · subst f
    apply gmin_le_of_lt_binary_ones
    rw [Nat.sub_add_cancel (by omega : 1 ≤ L),pow_zero]
    have htwo := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ t by omega)
    have hfour := Nat.pow_le_pow_right (by decide : 0 < 2) hL
    norm_num at htwo hfour
    omega
  have hf : 0 < f := by omega
  have hpow (d : ℕ) (hd : 0 < d) : 2^d=2*2^(d-1) := by rw [← pow_succ',Nat.sub_add_cancel hd]
  have hlow := Nat.pow_le_pow_right (by decide : 0 < 2) (show t-1 ≤ L-1 by omega)
  have hKhalf := Nat.one_le_two_pow (n:=L-1)
  have hFhalf := Nat.one_le_two_pow (n:=f-1)
  have hz : 2^L+2^f-2^t-2=2*(2^(L-1)-1+2^(f-1)-2^(t-1)) := by
    rw [hpow L (by omega),hpow f hf,hpow t ht]
    omega
  rw [hz]
  conv_lhs => arg 1; rw [show L-1=(L-2)+1 by omega]
  rw [gmin_double_weight]
  have hc := gmin_dyadic_increment_height_drop (L:=L-1) (u:=f-1)
    (H:=2^(t-1)) (by omega) (Nat.two_pow_pos _)
  simpa only [show L-1-1=L-2 by omega] using hc

/-- The overflowing companion in a shifted profile pair costs at
most one extra coin; its positive old power removes a second tail bit. -/
theorem gmin_shifted_overflow_positive_power_companion
    {L e r : ℕ} (hr : 0 < r) (hre : r < e) (heL : e < L) :
    gmin (L-1) (2*2^L+2^e-2^r-2) ≤ L+1 := by
  have he : 2 ≤ e := by omega
  have hL : 3 ≤ L := by omega
  have hpow (d : ℕ) (hd : 0 < d) : 2^d=2*2^(d-1) := by rw [← pow_succ',Nat.sub_add_cancel hd]
  let d := 2^(e-1)-2^(r-1)-1
  have hpowle := Nat.pow_lt_pow_right (by decide : 1 < 2) (show r-1 < e-1 by omega)
  have hd : d < 2^(e-1)-1 := by dsimp [d]; have := Nat.two_pow_pos (r-1); omega
  have hc := gmin_le_of_lt_binary_ones (w:=e-2) (t:=d)
    (by simpa only [show e-2+1=e-1 by omega] using hd)
  have hc' := (gmin_antitone_width (show e-2 ≤ L-2 by omega) d).trans hc
  have hd' : gmin (L-1) (2*d) ≤ e-2 := by
    rw [show L-1=(L-2)+1 by omega,gmin_double_weight]
    exact hc'
  have hz : 2*2^L+2^e-2^r-2=2*d+4*2^(L-1) := by
    rw [hpow L (by omega),hpow e (by omega),hpow r hr]
    dsimp [d]
    omega
  rw [hz,gmin_add_top_multiple]
  omega

/-- A separated overflow beside a two-power companion base gives an
actual shifted rival. The old positive powers pay for the overflowing
arm, so the full original coin budget is sufficient. -/
theorem not_coexisting_two_positive_power_base_and_overflow
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1) (hne : w ≠ v)
    {u r t e f : ℕ} (hrp : 0 < r) (htp : 0 < t)
    (hu : u < L j) (hre : r < e) (he : e < L a) (ht : t < L k) (hf : f < L k)
    (hva : (v a).val=2^r) (hvk : (v k).val=2^t)
    (hwj : (w j).val+1=2^u) (hwa : (w a).val+1=2^(L a)+2^e)
    (hwk : (w k).val+1=2^f) : False := by
  classical
  have hfull : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : n=L j+L a+L k := by
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hfull] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh.symm
  let X := fun i ↦ 2^(L i)-1+(w i).val-(v i).val
  have hcost : ∀ i, gmin (L i-1) (X i) ≤
      if i=a then L a+1 else if i=k then L k-1 else L j := by
    intro i
    have hm : i ∈ ({j,a,k} : Finset β) := by rw [← hfull]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hi | hi | hi
    · subst i
      simp only [if_neg (Ne.symm haj),if_neg (Ne.symm hkj)]
      have hz : X j=2^(L j)-1+2^u-((v j).val+1) := by
        dsimp [X]
        have := hvlow j
        have := Nat.two_pow_pos (L j)
        omega
      rw [hz]
      exact gmin_dyadic_increment_height_drop hu (by omega)
    · subst i
      simp only [if_true]
      have hz : X a=2*2^(L a)+2^e-2^r-2 := by
        dsimp [X]
        have := Nat.two_pow_pos (L a)
        omega
      rw [hz]
      exact gmin_shifted_overflow_positive_power_companion hrp hre he
    · subst i
      simp only [if_neg hka,if_true]
      have hz : X k=2^(L k)+2^f-2^t-2 := by
        dsimp [X]
        have := Nat.two_pow_pos (L k)
        omega
      rw [hz]
      exact gmin_shifted_positive_power_companion htp hf ht
  have hrep : ∀ i, ∃ U, val (L i) U=X i ∧ dsum (L i) U=gmin (L i-1) (X i) := by
    intro i
    simpa only [Nat.sub_add_cancel (hL i)] using exists_rep_gmin (L i-1) (X i)
  choose U hU hcount using hrep
  have hle : ∀ i, (v i).val ≤ 2^(L i)-1+(w i).val := by
    intro i
    have := hvlow i
    omega
  have hbudget := shifted_profile_coin_budget_gt_length L hwide g hg E x b hchain
    v w hv hw hle hne U hU
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ hcost i)
  simp only [← hcount] at hsum
  rw [hfull] at hsum hbudget
  simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hka] at hsum hbudget
  have := hL k
  omega

/-- A compatible base with two positive companions is the ENTIRE
profile family. Every potential coexisting overflow gives an affordable
shifted rival. No seed parity, finite-group, subglobal, or genuine-endpoint premise is required. -/
theorem forestCollisionProfiles_eq_singleton_of_two_positive_even_companions
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    forestCollisionProfiles n L x={v} := by
  classical
  have hfull : ({j,a,k} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcomp : ∀ i, i ≠ j → 0 < (v i).val ∧ Even (v i).val := by
    intro i hij
    have hm : i ∈ ({j,a,k} : Finset β) := by rw [hfull]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hi | hi | hi
    · exact False.elim (hij hi)
    · subst i; exact ⟨ha,heva⟩
    · subst i; exact ⟨hk,hevk⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hv,?_⟩
  intro w hw
  by_contra hne
  obtain ⟨_,c,e,hcj,hc,hce,hsep⟩ := other_profile_incompatible_overflow_of_two_positive_even_companions
    hr L hL hwide g hg E x b hchain j a k haj hkj hka hwidth v hv ha heva hk hevk w hw hne
  have hdcard : ((Finset.univ.erase j).erase c).card=1 := by simp [hr,hcj]
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase j).erase c).card)
  have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
  have hdj : d ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
  obtain ⟨hvlow,H,r,t,_,hrp,_,htp,ht,_,hvr,hvt,_⟩ := two_positive_even_companions_interior_power_budget
    hr L hL g hg E x b hchain j c d hcj hdj hdc v hv
      (hcomp c hcj).1 (hcomp c hcj).2 (hcomp d hdj).1 (hcomp d hdj).2
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  have hsides := dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) hbound hwm.1 hwm.2 c hc
  obtain ⟨_,u,hwu⟩ := hsides j (Ne.symm hcj)
  obtain ⟨hwdlow,f,hwf⟩ := hsides d hdc
  have hre : r < e := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    omega
  have he : e < L c := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    have := hbound c
    have := Nat.two_pow_pos (L c)
    omega
  have hf : f < L d := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    omega
  have hu : u < L j := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    have hp := Finset.sum_le_sum_of_subset (Finset.subset_univ ({j,c} : Finset β))
      (f := fun i ↦ (w i).val)
    rw [Finset.sum_pair (Ne.symm hcj)] at hp
    omega
  exact not_coexisting_two_positive_power_base_and_overflow hr L hL hwide g hg E x b hchain
    j c d hcj hdj hdc v w hv hw hvlow hne hrp htp hu hre he ht hf hvr hvt hwu hce hwf

/-- The remaining two-positive-compatible branch is one explicit
rectangle, with a three-power size budget and its full height charged
against the binary deficit. -/
theorem two_positive_even_companion_singleton_rectangle_bound
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    forestCollisionProfiles n L x={v} ∧
      ∃ h r t, h ≤ L j ∧ 0 < r ∧ r < L a ∧ 0 < t ∧ t < L k ∧
        (v j).val+1=2^h ∧ (v a).val=2^r ∧ (v k).val=2^t ∧
        2^h+2^r+2^t ≤ n ∧ 2^n+2^h ≤ N+2^h*(2^r+1)*(2^t+1) := by
  classical
  have hfamily := forestCollisionProfiles_eq_singleton_of_two_positive_even_companions hr L hL hwide
    g hg E x b hchain j a k haj hkj hka hwidth v hv ha heva hk hevk
  obtain ⟨hlow,h,r,t,hhL,hrp,hrL,htp,htL,hh,hra,htk,hcost⟩ :=
    two_positive_even_companions_interior_power_budget hr L hL g hg E x b hchain
      j a k haj hkj hka v hv ha heva hk hevk
  have hb := height_charged_profile_bound_of_two_positive_even_companions hN hr L hL hwide
    g hg E x b hchain j a k haj hkj hka hwidth hj hother v hv ha heva hk hevk
  rw [hfamily,Finset.sum_singleton] at hb
  have hside : ∀ i, min ((v i).val+1) (2*(2^(L i)-1)+1-(v i).val)=(v i).val+1 := by
    intro i
    have := hlow i
    omega
  simp only [hside] at hb
  have hfull : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  rw [hfull] at hb
  simp only [Finset.prod_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
    Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.prod_singleton,hh,hra,htk] at hb
  exact ⟨hfamily,h,r,t,hhL,hrp,hrL,htp,htL,hh,hra,htk,hcost,by simpa only [mul_assoc] using hb⟩

end MinModulus
