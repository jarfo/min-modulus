import MinModulus.ChainForestProfileEqualCoprime

/-! Uniform rivals for primitive factor two. A bounded index-step phase
puts the main rival below seven quarters of the axis width; its sole
exception saves two coins per companion and lies below three widths. -/

namespace MinModulus

/-- Adding a binary coin width cannot increase the greedy coin cost. -/
theorem gmin_succ_le (w z : ℕ) : gmin (w+1) z ≤ gmin w z := by
  induction w generalizing z with
  | zero => simp only [gmin]; omega
  | succ w ih =>
    change z%2+gmin (w+1) (z/2) ≤ z%2+gmin w (z/2)
    exact Nat.add_le_add_left (ih (z/2)) _

/-- The index-step factor-two companion pair has a uniform coin bound. -/
theorem equal_factor_two_companion_coin_bound {a v : ℕ}
    (ha : 1 ≤ a) (hv : v < 2^a-1) :
    gmin (a-1) v+gmin (a-1) (v+2^(a-1)) ≤ 2*a-1 := by
  rw [gmin_add_pow]
  have hc : gmin (a-1) v ≤ a-1 := gmin_le_of_lt_binary_ones (by
    simpa only [Nat.sub_add_cancel ha] using hv)
  omega

/-- The exceptional factor-two weights save two coins per companion. -/
theorem equal_factor_two_exceptional_coin_bound {a : ℕ} (ha : 2 ≤ a) :
    gmin (a-1) (2^(a-1)-2) ≤ a-2 := by
  have hh := gmin_succ_le (a-2) (2^(a-1)-2)
  have he : a-2+1=a-1 := by omega
  rw [he] at hh
  have hp : 2 ≤ 2^(a-1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hc : gmin (a-2) (2^(a-1)-2) ≤ a-2 :=
    gmin_le_of_lt_binary_ones (by rw [he]; omega)
  omega

/-- Every axis value below seven quarters of the full width has an
actual representation costing at most one coin beyond its length. -/
theorem exists_axis_rep_below_seven_quarters {L z : ℕ} (hL : 2 ≤ L)
    (hz : z < 7*2^(L-2)) :
    ∃ u, val L u=z ∧ dsum L u ≤ L+1 := by
  have he : L-2+(1+1)=L := by omega
  have hp : z/2^(L-2) < 7 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hc : gmin 1 (z/2^(L-2)) ≤ 3 := by simp only [gmin]; omega
  obtain ⟨u,hu,hcu⟩ := exists_rep_binary_block_tail 1 (L-2) (z/2^(L-2)) (z%2^(L-2))
    (Nat.mod_lt _ (by positivity))
  rw [he,Nat.mul_comm,Nat.div_add_mod] at hu
  rw [he] at hcu
  exact ⟨u,hu,by omega⟩

/-- The actual half-profile cost controls the whole factor-two signed
error by less than one full axis width. -/
theorem equal_factor_two_error_lt_axis_width {a n L s : ℕ}
    (ha : 2 ≤ a) (hn : 67 ≤ n) (hs : s=2^(a-1))
    (hcost : 2^(a+1) ≤ n+1) (hL : L+2*a=n) : 8*s*n < 2^L := by
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hT : (2*s-1)+1=2^a := by omega
  have hsmall := equal_maximal_index_error_lt_binary_tail hn hcost hT
  have hmargin := twelve_equal_length_le_of_half_cost hn hcost
  have he : a+(n-3*a)=L := by omega
  have hmul := Nat.mul_lt_mul_of_pos_left hsmall (Nat.two_pow_pos a)
  rw [← pow_add,he] at hmul
  have hcoeff : 8*s ≤ 2^a*(2*(2*s-1)) := by rw [hp]; nlinarith
  have hh := Nat.mul_le_mul_right n hcoeff
  nlinarith only [hmul,hh]

/-- A unit one-each phase and an odd primitive phase select a bounded
index-step companion weight with signed period error exactly minus one. -/
theorem exists_equal_factor_two_phase_weight {T r q : ℕ}
    (hT : 0 < T) (hr : Odd r) (hq : Nat.Coprime q T) :
    ∃ v : ℕ, v < T ∧ ∃ ν : ℤ, 2*(v : ℤ)*q-r=(2*T : ℕ)*ν+1 := by
  letI : NeZero T := ⟨by omega⟩
  obtain ⟨k,hk⟩ := hr
  have hrk : r+1=2*(k+1) := by omega
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime q T).mpr hq
  let v := ((↑(u⁻¹) : ZMod T)*(k+1 : ℕ)).val
  have hv : v < T := ZMod.val_lt _
  have he : (v : ZMod T)*(q : ZMod T)=(k+1 : ℕ) := by
    rw [show (v : ZMod T)=(↑(u⁻¹) : ZMod T)*(k+1 : ℕ) by exact ZMod.natCast_zmod_val _,← hu]
    calc
      _ = ((↑(u⁻¹) : ZMod T)*u)*(k+1 : ℕ) := by ring
      _ = _ := by rw [Units.inv_mul]; simp
  have hd : (T : ℤ) ∣ (v : ℤ)*q-(k+1 : ℕ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ T).mp
    push_cast
    simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mpr he
  obtain ⟨ν,hν⟩ := hd
  refine ⟨v,hv,ν,?_⟩
  have hh : (r : ℤ)+1=2*(k+1 : ℕ) := by exact_mod_cast hrk
  push_cast at hν hh ⊢
  linear_combination 2*hν-hh

/-- The sole excluded index-step weight gives a one-each phase inverse
whose companion weights save two coins each. -/
theorem equal_factor_two_exceptional_phase_inverse {s T r q : ℕ} {ν : ℤ}
    (hs : 2 ≤ s) (hT : T+1=2*s) (hlink : T ∣ 2*r+q)
    (hphase : 2*((T-1 : ℕ) : ℤ)*q-r=(2*T : ℕ)*ν+1) :
    ∃ m : ℤ, ((s-2 : ℕ) : ℤ)*q=(T : ℤ)*m+1 := by
  have hTp : 1 ≤ T := by omega
  obtain ⟨l,hl⟩ := hlink
  have hlZ : 2*(r : ℤ)+q=(T : ℤ)*l := by exact_mod_cast hl
  have hTZ : (T : ℤ)+1=2*s := by exact_mod_cast hT
  simp only [Nat.cast_sub hTp,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at hphase
  have h3 : 3*(q : ℤ)+2=(T : ℤ)*(4*((q : ℤ)-ν)-l) := by
    linear_combination -hlZ-2*hphase
  let A : ℤ := ((s : ℤ)-2)*q-1
  let k : ℤ := (q : ℤ)-(4*((q : ℤ)-ν)-l)
  have h2 : 2*A=(T : ℤ)*k := by
    dsimp [A,k]
    linear_combination -hTZ*(q : ℤ)-h3
  refine ⟨(s : ℤ)*k-A,?_⟩
  simp only [Nat.cast_sub hs,Nat.cast_ofNat]
  have hh : A=(T : ℤ)*((s : ℤ)*k-A) := by
    linear_combination hTZ*A+(s : ℤ)*h2
  dsimp only [A] at hh ⊢
  linarith

/-- The main factor-two signed rival lies in the affordable seven-quarter
axis interval, uniformly over its whole nonexceptional phase range. -/
theorem equal_factor_two_main_axis_window
    {s T n K H c E v : ℕ} {Z : ℤ} (hs : 4 ≤ s) (hT : T+1=2*s)
    (hv : v < T-1) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hE : E ≤ s*H)
    (hwide : 8*s*n < K)
    (herr : (2*T : ℕ)*Z-(2*(v : ℤ)+3*s+1)*K=
      (5*(s : ℤ)-3-2*v)*H+(3*(s : ℤ)-2-2*v)*c-(2*T : ℕ)-E) :
    (n : ℤ) ≤ Z ∧ 4*Z < 7*K := by
  have hS : 0 < 2*T := by omega
  have hw := signed_rival_linear_error_window (S:=2*T) (W:=s)
    (A:=5*(s : ℤ)-3-2*v) (B:=3*(s : ℤ)-2-2*v) (J:=-1) (C:=8*(s : ℤ))
    hH hnc hE hS (by positivity) (by norm_num; omega) (by omega) (by norm_num; omega) (by omega)
  have hwideZ : 8*(s : ℤ)*n < K := by exact_mod_cast hwide
  have hTZ : (T : ℤ)+1=2*s := by exact_mod_cast hT
  have hSZ : (0 : ℤ) < 2*T := by exact_mod_cast hS
  have hR : (3 : ℤ) ≤ 2*v+3*s+1 := by omega
  have hRK := mul_le_mul_of_nonneg_right hR (Int.natCast_nonneg K)
  have hcoeff : 2*(T : ℤ) ≤ 8*s := by omega
  have hSn := mul_le_mul_of_nonneg_right hcoeff (Int.natCast_nonneg n)
  have hgap : (6 : ℤ) ≤ 7*(2*(T : ℤ))-4*(2*(v : ℤ)+3*s+1) := by omega
  have hgapK := mul_le_mul_of_nonneg_right hgap (Int.natCast_nonneg K)
  push_cast at herr hw
  constructor
  · apply (mul_le_mul_iff_right₀ hSZ).mp
    nlinarith only [herr,hw.1,hwideZ,hRK,hSn]
  · apply (mul_lt_mul_iff_right₀ hSZ).mp
    nlinarith only [herr,hw.2,hwideZ,hgapK,Int.natCast_nonneg K]

/-- Every nonexceptional factor-two weight gives an actual affordable
index-step rival throughout the unrestricted companion-length range. -/
theorem exists_equal_factor_two_main_rival
    {a n N L s T M E H c V α z r q v : ℕ} {ν : ℤ}
    (ha : 3 ≤ a) (hs : s=2^(a-1)) (hT : T+1=2*s) (hL : L+2*a=n)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=4*s*2^L) (hE : E ≤ s*H) (hwide : 8*s*n < 2^L)
    (hv : v < T-1) (hphase : 2*(v : ℤ)*q-r=(2*T : ℕ)*ν+1)
    (hap : (2*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((2 : ℤ)^L-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=s • b) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w, n ≤ w ∧ v ≠ 2^a-1 ∧ ∃ u,
      val L u=w ∧ dsum L u+gmin (a-1) (v+s)+gmin (a-1) v ≤ n ∧
      w • x+(v+s) • b+v • d=V • x := by
  have hs4 : 4 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a-1)
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hLp : 2 ≤ L := by
    by_contra hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) (show L ≤ 1 by omega)
    norm_num at hh'
    nlinarith
  let Z : ℤ := (v : ℤ)*z-α+(1-(v : ℤ))*V-ν*M
  have herr : (2*T : ℕ)*Z-(2*(v : ℤ)+3*s+1)*(2 : ℤ)^L=
      (5*(s : ℤ)-3-2*v)*H+(3*(s : ℤ)-2-2*v)*c-(2*T : ℕ)-E := by
    have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    have hm : (M : ℤ)+E=4*(s : ℤ)*(2 : ℤ)^L := by exact_mod_cast hM
    have ht : (T : ℤ)+1=2*s := by exact_mod_cast hT
    dsimp [Z]
    push_cast at hap hphase ⊢
    linear_combination 2*(v : ℤ)*hzp-hap-2*(T : ℤ)*(1-(v : ℤ))*hb+
      hm+(M : ℤ)*hphase+2*ht*((H : ℤ)+c)
  obtain ⟨hlo,hhi⟩ := equal_factor_two_main_axis_window hs4 hT hv hH hnc hE hwide
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using herr)
  have hnonneg : 0 ≤ Z := le_trans (Int.natCast_nonneg n) hlo
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hnonneg
  have hnZ : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by rw [hcast]; exact hlo)
  have hhiN : 4*Z.toNat < 7*2^L := by
    exact_mod_cast (show 4*(Z.toNat : ℤ) < 7*(2^L : ℕ) by rw [hcast]; exact hhi)
  have hpow : 2^L=4*2^(L-2) := by
    rw [show L=2+(L-2) by omega,pow_add]
    norm_num
  have hbound : Z.toNat < 7*2^(L-2) := by rw [hpow] at hhiN; omega
  obtain ⟨u,hu,hcu⟩ := exists_axis_rep_below_seven_quarters hLp hbound
  have hc := equal_factor_two_companion_coin_bound (by omega : 1 ≤ a) (v:=v) (by omega)
  rw [← hs] at hc
  refine ⟨Z.toNat,hnZ,by omega,u,hu,by omega,?_⟩
  have hh := signed_axis_basis_rival_eq x b d 1 ν (ta:=v+s) (tb:=v)
    (by simp) hz hα hmx (by simpa only [one_mul] using hnonneg)
  simpa only [one_mul,Z] using hh

/-- The exceptional factor-two phase has an equal-weight rival below
three axis widths, paid for by two saved coins per companion. -/
theorem exists_equal_factor_two_exceptional_rival
    {a n N L s T M E H c V z q : ℕ} {ν : ℤ}
    (ha : 3 ≤ a) (hs : s=2^(a-1)) (hT : T+1=2*s) (hL : L+2*a=n)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=4*s*2^L) (hE : E ≤ s*H) (hwide : 8*s*n < 2^L)
    (hphase : ((s-2 : ℕ) : ℤ)*q=(T : ℤ)*ν+1)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w, n ≤ w ∧ s-2 ≠ 2^a-1 ∧ ∃ u,
      val L u=w ∧ dsum L u+2*gmin (a-1) (s-2) ≤ n ∧
      w • x+(s-2) • b+(s-2) • d=V • x := by
  have hs4 : 4 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a-1)
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hLp : 1 ≤ L := by
    by_contra hh
    have he : L=0 := by omega
    simp only [he,pow_zero] at hwide
    nlinarith
  let Z : ℤ := ((s-2 : ℕ) : ℤ)*z+(1-((s-2 : ℕ) : ℤ))*V-ν*M
  have herr : (T : ℤ)*Z-(5*(s : ℤ)-2)*(2 : ℤ)^L=
      ((s : ℤ)+1)*H+((s : ℤ)+1)*c-T-E := by
    have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    have hm : (M : ℤ)+E=4*(s : ℤ)*(2 : ℤ)^L := by exact_mod_cast hM
    have ht : (T : ℤ)+1=2*s := by exact_mod_cast hT
    dsimp [Z]
    simp only [Nat.cast_sub (show 2 ≤ s by omega),Nat.cast_ofNat] at hphase ⊢
    linear_combination ((s : ℤ)-2)*hzp-(T : ℤ)*(3-(s : ℤ))*hb+hm+
      (M : ℤ)*hphase+ht*((H : ℤ)+c)
  have hS : 0 < T := by omega
  have hw := signed_rival_linear_error_window (S:=T) (W:=s)
    (A:=(s : ℤ)+1) (B:=(s : ℤ)+1) (J:=-1) (C:=8*(s : ℤ))
    hH hnc hE hS (by positivity) (by norm_num; omega) (by omega) (by norm_num; omega) (by omega)
  have hwideZ : 8*(s : ℤ)*n < (2 : ℤ)^L := by exact_mod_cast hwide
  have hSZ : (0 : ℤ) < T := by exact_mod_cast hS
  have hRK := mul_le_mul_of_nonneg_right (show (3 : ℤ) ≤ 5*(s : ℤ)-2 by omega)
    (show (0 : ℤ) ≤ (2 : ℤ)^L by positivity)
  have hSn := mul_le_mul_of_nonneg_right (show (T : ℤ) ≤ 8*s by omega) (Int.natCast_nonneg n)
  have hgapK := mul_le_mul_of_nonneg_right (show (3 : ℤ) ≤ 3*(T : ℤ)-(5*(s : ℤ)-2) by omega)
    (show (0 : ℤ) ≤ (2 : ℤ)^L by positivity)
  norm_num only [neg_one_mul] at hw
  have hlo : (n : ℤ) ≤ Z := by
    apply (mul_le_mul_iff_right₀ hSZ).mp
    nlinarith only [herr,hw.1,hwideZ,hRK,hSn]
  have hhi : Z < 3*(2 : ℤ)^L := by
    apply (mul_lt_mul_iff_right₀ hSZ).mp
    nlinarith only [herr,hw.2,hwideZ,hgapK]
  have hnonneg : 0 ≤ Z := le_trans (Int.natCast_nonneg n) hlo
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hnonneg
  have hnZ : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by rw [hcast]; exact hlo)
  have hhiN : Z.toNat < 3*2^L := by
    exact_mod_cast (show (Z.toNat : ℤ) < 3*(2 : ℤ)^L by rw [hcast]; exact hhi)
  have hpow : 2^L=2*2^(L-1) := by rw [← pow_succ']; congr 1; omega
  have hd : Z.toNat/2^(L-1) < 6 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have haxis := gmin_le_top_quotient_add_width (L-1) Z.toNat
  have hc := equal_factor_two_exceptional_coin_bound (by omega : 2 ≤ a)
  rw [← hs] at hc
  obtain ⟨u,hu,hcu⟩ := exists_rep_gmin (L-1) Z.toNat
  have he : L-1+1=L := by omega
  rw [he] at hu hcu
  refine ⟨Z.toNat,hnZ,by omega,u,hu,by omega,?_⟩
  have hh := signed_axis_basis_rival_eq (D:=0) (α:=0) x b d 0 ν
    (ta:=s-2) (tb:=s-2) (by simp) hz (by simp) hmx
    (by simpa only [zero_mul,sub_zero] using hnonneg)
  simpa only [zero_mul,sub_zero,Z] using hh

/-- Every unit odd primitive phase at factor two has an affordable
actual rival at arbitrary common companion length. -/
theorem exists_equal_factor_two_primitive_rival
    {a n N L s T M E H c V α z r q : ℕ}
    (ha : 3 ≤ a) (hn : 67 ≤ n) (hs : s=2^(a-1)) (hT : T+1=2*s)
    (hL : L+2*a=n) (hcost : 2^(a+1) ≤ n+1)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=4*s*2^L) (hE : E ≤ s*H)
    (hr : Odd r) (hq : Nat.Coprime q T) (hlink : T ∣ 2*r+q)
    (hap : (2*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((2 : ℤ)^L-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=s • b) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w ta tb, n ≤ w ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^a-1) ∧ ∃ u,
      val L u=w ∧ dsum L u+gmin (a-1) ta+gmin (a-1) tb ≤ n ∧
      w • x+ta • b+tb • d=V • x := by
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hwide := equal_factor_two_error_lt_axis_width (by omega) hn hs hcost hL
  obtain ⟨v,hv,ν,hphase⟩ := exists_equal_factor_two_phase_weight (by omega : 0 < T) hr hq
  by_cases he : v=T-1
  · obtain ⟨m,hm⟩ := equal_factor_two_exceptional_phase_inverse hs2 hT hlink (by simpa only [he] using hphase)
    obtain ⟨w,hw,hne,u,hu,hcu,heval⟩ := exists_equal_factor_two_exceptional_rival
      ha hs hT hL hH hnc hbase hM hE hwide hm hzp x b d hz hmx
    exact ⟨w,s-2,s-2,hw,Or.inl hne,u,hu,by omega,heval⟩
  · obtain ⟨w,hw,hne,u,hu,hcu,heval⟩ := exists_equal_factor_two_main_rival
      ha hs hT hL hH hnc hbase hM hE hwide (by omega) hphase hap hzp x b d hα hz hmx
    exact ⟨w,v+s,v,hw,Or.inr hne,u,hu,hcu,heval⟩


end MinModulus
