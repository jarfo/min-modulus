import MinModulus.ChainForestProfileStrips

/-! Below binary, actual profile lower rectangles meet every coset of
every subgroup containing a sufficiently dominant seed. Compatible
three-chain overflow strips no wider than the dominant index all miss
the zero quotient class and therefore force the binary bound. The sharp
general profile estimate and the unrestricted global conjecture remain open. -/

namespace MinModulus
open Finset

/-- Every coset of a subgroup containing a sufficiently dominant seed
must meet an actual profile lower rectangle below binary. A missing
profile fibre leaves a balanced box fibre injective and forces the
binary bound. The result permits any number of arms. -/
theorem binary_bound_of_profiles_avoiding_dominant_coset
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) (r : G)
    (havoid : ∀ w ∈ forestCollisionProfiles n L x, ∀ p ∈ forestProfileLowerBox L w,
      (∑ i, (p i).val • x i)-r ∉ H) : 2^n ≤ Fintype.card G := by
  classical
  by_contra hn
  have hsub : Fintype.card G < 2^n := by omega
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let C := {i : β // i ≠ j}
  let B := ∀ i : C, Fin (2^(L i.val))
  let π := QuotientAddGroup.mk' H
  let v : B → G := fun p ↦ ∑ i, (p i).val • x i.val
  obtain ⟨m,hm,hbalance⟩ := balanced_companion_quotient_of_subbinary_dominant_chain
    L hL g hg E x b hchain hsub j hlarge H hx
  let D := {p : B // π (v p)=π r}
  have hD : Fintype.card D=m := by
    simpa only [Nat.card_eq_fintype_card,D,B,C,π,v] using hbalance (π r)
  let P : Fin (2^(L j)) × D → (∀ i, Fin (2^(L i))) := fun p i ↦
    if hi : i=j then hi.symm ▸ p.1 else p.2.val ⟨i,hi⟩
  have hval : ∀ p, (∑ i, (P p i).val • x i)=p.1.val • x j+v p.2.val := by
    intro p
    rw [← (Equiv.optionSubtypeNe j).sum_comp (fun i ↦ (P p i).val • x i),Fintype.sum_option]
    simp only [Equiv.optionSubtypeNe_none,Equiv.optionSubtypeNe_some,P,dif_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_neg i.property]
  have hmem : ∀ p, (∑ i, (P p i).val • x i)-r ∈ H := by
    intro p
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change π ((∑ i, (P p i).val • x i)-r)=0
    rw [hval,map_sub,map_add,map_nsmul]
    have hxzero : π (x j)=0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
    rw [hxzero,nsmul_zero,zero_add,p.2.property,sub_self]
  have hout : ∀ p, P p ∉ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L) := by
    intro p hp
    obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hp
    exact havoid w hw (P p) hpw (hmem p)
  let F : Fin (2^(L j)) × D → H := fun p ↦ ⟨(∑ i, (P p i).val • x i)-r,hmem p⟩
  have hi : Function.Injective F := by
    intro p q he
    have heval := congrArg Subtype.val he
    have hh := box_injective_outside_profile_rectangles L hL g hg E x b hchain
      (a₁ := ⟨P p,hout p⟩) (a₂ := ⟨P q,hout q⟩) (sub_left_inj.mp heval)
    have hP : P p=P q := congrArg Subtype.val hh
    apply Prod.ext
    · have hj := congrFun hP j
      simpa only [P,dif_pos rfl] using hj
    · apply Subtype.ext
      funext i
      have hh := congrFun hP i.val
      simpa only [P,dif_neg i.property] using hh
  have hc := Fintype.card_le_of_injective F hi
  simp only [Fintype.card_prod,Fintype.card_fin,hD] at hc
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hLj : L j ≤ n := by
    rw [← hsize]
    exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hpow : 2^n=2^(L j)*2^(n-L j) := by rw [← pow_add,Nat.add_sub_of_le hLj]
  have hgroup : Fintype.card G=Fintype.card (G ⧸ H)*Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hmul := Nat.mul_le_mul_left (Fintype.card (G ⧸ H)) hc
  simp only [Nat.card_eq_fintype_card] at hm
  rw [← mul_assoc,mul_comm (Fintype.card (G ⧸ H)) (2^(L j)),mul_assoc,hm,← hpow,← hgroup] at hmul
  omega

/-- Below binary, the actual profile rectangles meet EVERY coset of
EVERY subgroup containing the sufficiently dominant seed. -/
theorem profiles_meet_every_dominant_coset
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) (r : G) :
    ∃ w ∈ forestCollisionProfiles n L x, ∃ p ∈ forestProfileLowerBox L w,
      (∑ i, (p i).val • x i)-r ∈ H := by
  classical
  by_contra hnot
  push Not at hnot
  have hh := binary_bound_of_profiles_avoiding_dominant_coset L hL g hg E x b hchain j hlarge H hx r hnot
  omega

/-- Compatible overflow strips whose widths do not exceed the dominant
index all miss the zero quotient class. They cannot alone pay a
subbinary deficit, even when several such strips coexist. -/
theorem binary_bound_of_compatible_strips_width_le_dominant_index
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val)
    (hprofiles : ∀ w ∈ forestCollisionProfiles n L x,
      (∀ i, i ≠ j → Even (w i).val) ∧
        ∃ a, 2^(L a)-1 < (w a).val ∧ 2^(L a) ≤ N.gcd (x j).val) : 2^n ≤ N := by
  classical
  by_contra hn
  have hsub : N < 2^n := by omega
  obtain ⟨e,_,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  letI : NeZero (2^e) := ⟨by positivity⟩
  have hdiv : 2^e ∣ N := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  let π : ZMod N →+ ZMod (2^e) := (ZMod.castHom hdiv (ZMod (2^e))).toAddMonoidHom
  have hπval : ∀ z : ZMod N, π z=(z.val : ZMod (2^e)) := by
    intro z
    change (z.cast : ZMod (2^e))=(z.val : ZMod (2^e))
    exact ZMod.cast_eq_val z
  have hx : π (x j)=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff,← hgcd]
    exact Nat.gcd_dvd_right _ _
  have hwidth : n ≤ 2^(L j) := by
    have hh : n ≤ n*(2^(n-L j)+1) := by nlinarith [Nat.two_pow_pos (n-L j)]
    omega
  have havoid : ∀ w ∈ forestCollisionProfiles n L x, ∀ p ∈ forestProfileLowerBox L w,
      (∑ i, (p i).val • x i)-(0 : ZMod N) ∉ π.ker := by
    intro w hw p hp hmem
    obtain ⟨hcompat,a,ha,hKa⟩ := hprofiles w hw
    obtain ⟨haj,hwa,hz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hcompat a ha
    have hwj : (w j).val < 2^(L j) := by
      have hmem' : (∑ i, (w i).val)<n ∧
          (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
        simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
      have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega
    obtain ⟨_,hpa,hpz⟩ := (forestProfileLowerBox_eq_strip L j a haj w hwj hwa hz p).mp hp
    have heval : π (∑ i, (p i).val • x i)=(p a).val • π (x a) := by
      rw [map_sum]
      simp only [map_nsmul]
      apply Finset.sum_eq_single a
      · intro i _ hia
        by_cases hij : i=j
        · subst i; rw [hx,nsmul_zero]
        · rw [hpz i hij hia,zero_nsmul]
      · simp
    have hzero : (p a).val • π (x a)=0 := by
      rw [← heval]
      simpa only [sub_zero,AddMonoidHom.mem_ker] using hmem
    have hu : IsUnit (π (x a)) := by
      rw [hπval,ZMod.isUnit_iff_coprime]
      exact (hodd a haj).coprime_two_right.pow_right e
    have hdvd : 2^e ∣ (p a).val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      exact hu.mul_left_eq_zero.mp (by simpa only [nsmul_eq_mul] using hzero)
    have hle := Nat.le_of_dvd (by omega : 0 < (p a).val) hdvd
    have := (p a).isLt
    omega
  have hh := binary_bound_of_profiles_avoiding_dominant_coset L hL g hg E x b hchain j hlarge π.ker hx 0 havoid
  have hh' : 2^n ≤ N := by simpa only [ZMod.card] using hh
  omega

end MinModulus
