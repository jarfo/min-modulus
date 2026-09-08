import MinModulus.ChainForestProfileIndexTwo

/-! Unequal odd companion lengths force the dominant index exponent below
both lengths: their projected half-widths cannot cancel otherwise.
A remaining subglobal even-axis forest with a length-two companion has
index exactly two. The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A common divisor killing the dominant seed and both companion widths
also divides the weighted sum of the two companion half-widths for any
actual half-shaped profile. No validity or axis-base premise is needed. -/
theorem half_profile_companion_half_widths_divisible
    {n N D : ℕ} [NeZero N]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (_hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hDN : D ∣ N) (hj : D ∣ (x j).val) (hDa : D ∣ 2^(L a)) (hDk : D ∣ 2^(L k))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1)) :
    D ∣ 2^(L a-1)*(x a).val+2^(L k-1)*(x k).val := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have heq := hwm.2
  rw [hset] at heq
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
    Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at heq
  simp only [← add_assoc] at heq
  have heq' : (w j).val • x j+(2^(L a)+2^(L a-1)) • x a+2^(L k-1) • x k=
      (2^(L j)-1) • x j+2^(L a) • x a+2^(L k) • x k := by
    have hp : ∀ i, 2^(L i)-1+1=2^(L i) := by intro i; have := Nat.two_pow_pos (L i); omega
    have hh := congrArg (fun t ↦ t+x a+x k) heq
    have hleft : ((w j).val • x j+(w a).val • x a+(w k).val • x k)+x a+x k=
        (w j).val • x j+((w a).val+1) • x a+((w k).val+1) • x k := by
      simp only [add_nsmul,one_nsmul]
      abel
    have hright : ((2^(L j)-1) • x j+(2^(L a)-1) • x a+(2^(L k)-1) • x k)+x a+x k=
        (2^(L j)-1) • x j+(2^(L a)-1+1) • x a+(2^(L k)-1+1) • x k := by
      simp only [add_nsmul,one_nsmul]
      abel
    rw [hleft,hright,hwa,hwk,hp a,hp k] at hh
    exact hh
  let π := ZMod.castHom hDN (ZMod D)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod D) := fun t ↦ ZMod.cast_eq_val t
  have hπj : π (x j)=0 := by rw [hπval,ZMod.natCast_eq_zero_iff]; exact hj
  have hca : ((2^(L a) : ℕ) : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDa
  have hck : ((2^(L k) : ℕ) : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDk
  have hh := congrArg π heq'
  simp only [map_add,map_nsmul] at hh
  simp only [hπj,smul_zero,zero_add,nsmul_eq_mul,Nat.cast_add,hca,hck,zero_mul,add_zero] at hh
  rw [hπval,hπval] at hh
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_add,Nat.cast_mul] using hh

/-- Unequal odd companion lengths prevent the whole smaller width from
dividing the dominant gcd. Their half-width valuations cannot cancel. -/
theorem half_profile_unequal_companions_not_min_power_dvd_gcd
    {n N : ℕ} [NeZero N]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (ha : Odd (x a).val) (hk : Odd (x k).val) (hne : L a ≠ L k)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1)) :
    ¬ 2^(min (L a) (L k)) ∣ N.gcd (x j).val := by
  intro hd
  have hh := half_profile_companion_half_widths_divisible hr L hL x j a k haj hkj hka
    (hd.trans (Nat.gcd_dvd_left _ _)) (hd.trans (Nat.gcd_dvd_right _ _))
    (pow_dvd_pow 2 (Nat.min_le_left _ _)) (pow_dvd_pow 2 (Nat.min_le_right _ _)) w hw hwa hwk
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [Nat.min_eq_left hlt.le] at hh
    have hkdiv : 2^(L a) ∣ 2^(L k-1)*(x k).val :=
      (pow_dvd_pow 2 (by omega : L a ≤ L k-1)).trans (dvd_mul_right _ _)
    have haProd : 2^(L a) ∣ 2^(L a-1)*(x a).val := (Nat.dvd_add_iff_left hkdiv).mpr hh
    have haDiv : 2^(L a) ∣ 2^(L a-1) :=
      (ha.coprime_two_left.pow_left (L a)).dvd_of_dvd_mul_right haProd
    have hle := Nat.le_of_dvd (Nat.two_pow_pos (L a-1)) haDiv
    have hp : 2^(L a-1)<2^(L a) := Nat.pow_lt_pow_right (by decide) (by have := hL a; omega)
    omega
  · rw [Nat.min_eq_right hlt.le] at hh
    have hadiv : 2^(L k) ∣ 2^(L a-1)*(x a).val :=
      (pow_dvd_pow 2 (by omega : L k ≤ L a-1)).trans (dvd_mul_right _ _)
    have hkProd : 2^(L k) ∣ 2^(L k-1)*(x k).val := (Nat.dvd_add_iff_right hadiv).mpr hh
    have hkDiv : 2^(L k) ∣ 2^(L k-1) :=
      (hk.coprime_two_left.pow_left (L k)).dvd_of_dvd_mul_right hkProd
    have hle := Nat.le_of_dvd (Nat.two_pow_pos (L k-1)) hkDiv
    have hp : 2^(L k-1)<2^(L k) := Nat.pow_lt_pow_right (by decide) (by have := hL k; omega)
    omega

/-- Below the sharp bound, unequal odd companions bound the dominant
index exponent strictly below BOTH companion lengths. The half-profile
family and index are extracted from the original genuine even-axis forest. -/
theorem even_axis_subglobal_unequal_companions_index_exponent
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hne : L a ≠ L k)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N<globalBound n) :
    ∃ e, 1 ≤ e ∧ e < min (L a) (L k) ∧ N.gcd (x j).val=2^e := by
  classical
  have hwidth : 2*n ≤ 2^(L j) := by
    have hp := Nat.two_pow_pos (n-L j)
    have hh := Nat.mul_le_mul_left n (by omega : 2 ≤ 2^(n-L j)+1)
    nlinarith
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  obtain ⟨hL2,w,c,hcj,hfamily,hc,hinc⟩ := even_axis_subglobal_profile_pair hn hN hr L hL hwide
    g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcaks : c=a ∨ c=k := by
    have hh : c ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    exact hh.resolve_left hcj
  have hnot : ¬ 2^(min (L a) (L k)) ∣ N.gcd (x j).val := by
    rcases hcaks with hca | hck
    · subst c
      obtain ⟨hwa,hwk,_⟩ := even_axis_incompatible_overflow_half_shape (show 2 ∣ N from ⟨M,hN⟩)
        hr L hL2 hwide g hg E x b hchain j a k haj hkj hka (by omega) hj hother v w hv hw hvz hc hinc
      exact half_profile_unequal_companions_not_min_power_dvd_gcd hr L hL x j a k haj hkj hka
        (hother a haj) (hother k hkj) hne w hw hwa hwk
    · subst c
      obtain ⟨hwk,hwa,_⟩ := even_axis_incompatible_overflow_half_shape (show 2 ∣ N from ⟨M,hN⟩)
        hr L hL2 hwide g hg E x b hchain j k a hkj haj (Ne.symm hka) (by omega) hj hother v w hv hw hvz hc hinc
      simpa only [Nat.min_comm] using half_profile_unequal_companions_not_min_power_dvd_gcd hr L hL x
        j k a hkj haj (Ne.symm hka) (hother k hkj) (hother a haj) (Ne.symm hne) w hw hwk hwa
  have hsubbin : N<2^n := lt_of_lt_of_le hsub (Nat.sub_le _ _)
  obtain ⟨e,_,hindex⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsubbin j hlarge
  have hepos : 1 ≤ e := by
    have hd : 2 ∣ N.gcd (x j).val := Nat.dvd_gcd ⟨M,hN⟩ (even_iff_two_dvd.mp hj)
    by_contra he
    have he0 : e=0 := by omega
    rw [hindex,he0,pow_zero] at hd
    norm_num at hd
  refine ⟨e,hepos,?_,hindex⟩
  by_contra he
  apply hnot
  rw [hindex]
  exact pow_dvd_pow 2 (by omega : min (L a) (L k) ≤ e)

/-- Every remaining subglobal genuine even-axis case with a length-two
companion has dominant index exactly two. The equal-length alternative
is already globally closed; unequal lengths use half-width cancellation. -/
theorem even_axis_subglobal_length_two_companion_index_two
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a : β) (haj : a ≠ j) (hLa : L a=2)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N<globalBound n) : N.gcd (x j).val=2 := by
  classical
  have hk : ∃ k, k ≠ j ∧ k ≠ a := by
    have hc : ((Finset.univ.erase j).erase a).card=1 := by simp [hr,haj]
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase j).erase a).card)
    exact ⟨k,(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,(Finset.mem_erase.mp hk).1⟩
  obtain ⟨k,hkj,hka⟩ := hk
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  by_cases hLk : L k=2
  · have hshort : ∀ i, i ≠ j → L i=2 := by
      intro i hij
      have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with hi | hi | hi
      · exact False.elim (hij hi)
      · simpa only [hi] using hLa
      · simpa only [hi] using hLk
    have hh := even_axis_two_length_two_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j hj hother hshort v hv hvz
    omega
  · obtain ⟨e,hepos,he,hindex⟩ := even_axis_subglobal_unequal_companions_index_exponent (by omega : 24 ≤ n)
      hN hr L hL g hg E x b hchain hgen j a k haj hkj hka hlarge hj hother (by omega) v hv hvz hsub
    have he1 : e=1 := by
      rw [hLa] at he
      have := Nat.min_le_left 2 (L k)
      omega
    simpa only [he1,pow_one] using hindex

end MinModulus
