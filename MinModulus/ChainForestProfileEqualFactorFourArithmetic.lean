import MinModulus.ChainForestProfileEqualFactorTwo

/-! Uniform factor-four primitive rivals. Binary-block coin bounds and
unit phase selection give two index steps; subtracting the actual half
profile handles their costly upper range. -/

namespace MinModulus

/-- A bounded lower binary block has exactly its own coin cost, separate
from an arbitrary upper block. -/
theorem gmin_binary_block (e w p r : ℕ) (hr : r < 2^e) :
    gmin (e+w) (p*2^e+r)=gmin w p+gmin e r := by
  induction e generalizing r with
  | zero =>
    have he : r=0 := by norm_num at hr; omega
    simp [he,gmin]
  | succ e ih =>
    have hp : 2^(e+1)=2*2^e := by rw [pow_succ']
    have hprod : p*2^(e+1)=2*(p*2^e) := by rw [hp]; ring
    have hrem : (p*2^(e+1)+r)%2=r%2 := by omega
    have hdiv : (p*2^(e+1)+r)/2=p*2^e+r/2 := by omega
    have hhalf : r/2 < 2^e := by omega
    rw [show e+1+w=(e+w)+1 by omega,gmin,hrem,hdiv,ih (r/2) hhalf,gmin]
    omega

/-- A lower block bounded strictly below all ones saves a coin even
when its representation includes one additional upper position. -/
theorem gmin_binary_low_lt_ones {e r : ℕ} (he : 1 ≤ e) (hr : r < 2^e-1) :
    gmin e r ≤ e-1 := by
  have hs : e-1+1=e := by omega
  have hm := gmin_succ_le (e-1) r
  rw [hs] at hm
  have hc : gmin (e-1) r ≤ e-1 := gmin_le_of_lt_binary_ones (by simpa only [hs] using hr)
  omega

/-- Every bounded lower block costs at most its binary length. -/
theorem gmin_binary_low_le {e r : ℕ} (hr : r < 2^e) : gmin e r ≤ e := by
  apply gmin_le_of_lt_binary_ones
  have hp : 2^(e+1)=2*2^e := by rw [pow_succ']
  have hh := Nat.one_le_two_pow (n:=e)
  omega

/-- The two possible odd quarter-width shifts have uniform companion
coin budgets, with the upper quarter saving an extra coin. -/
theorem equal_factor_four_quarter_coin_bounds {e v : ℕ}
    (he : 1 ≤ e) (hv : v < 4*2^e-1) :
    (v < 3*2^e → gmin (e+1) v+gmin (e+1) (v+2^e) ≤ 2*e+3) ∧
    (3*2^e ≤ v → gmin (e+1) v+gmin (e+1) (v+2^e) ≤ 2*e+2) ∧
    (v < 3*2^e-1 → gmin (e+1) v+gmin (e+1) (v+3*2^e) ≤ 2*e+3) := by
  let m := v/2^e
  let r := v%2^e
  have hm : m < 4 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hr : r < 2^e := Nat.mod_lt _ (by positivity)
  have hval : v=m*2^e+r := by dsimp [m,r]; simpa only [Nat.mul_comm] using (Nat.div_add_mod v (2^e)).symm
  have hc := gmin_binary_low_le hr
  have hc' : r < 2^e-1 → gmin e r ≤ e-1 := gmin_binary_low_lt_ones he
  have hk : ∀ k, gmin (e+1) (v+k*2^e)=gmin 1 (m+k)+gmin e r := by
    intro k
    have hh : v+k*2^e=(m+k)*2^e+r := by rw [hval]; ring
    rw [hh]
    exact gmin_binary_block e 1 (m+k) r hr
  have h0 : gmin (e+1) v=gmin 1 m+gmin e r := by simpa using hk 0
  have h1 : gmin (e+1) (v+2^e)=gmin 1 (m+1)+gmin e r := by simpa using hk 1
  have h3 := hk 3
  simp only [h0,h1,h3]
  refine ⟨?_,?_,?_⟩
  all_goals intro h
  all_goals interval_cases m <;> norm_num [gmin] at hval ⊢
  all_goals try omega

/-- Subtracting the half profile in the upper range leaves two short
companion blocks separated by one quarter width. -/
theorem equal_factor_four_half_shift_coin_bound {e v : ℕ}
    (hv : v < 4*2^e-1) (hlo : 3*2^e-1 ≤ v) :
    gmin (e+1) (v-(3*2^e-1))+gmin (e+1) (v-(2*2^e-1)) ≤ 2*e+1 := by
  have hu : 1 ≤ 2^e := Nat.one_le_two_pow
  have hr : v-(3*2^e-1) < 2^e := by omega
  have hsum : v-(2*2^e-1)=2^e+(v-(3*2^e-1)) := by omega
  have h0 := gmin_binary_block e 1 0 (v-(3*2^e-1)) hr
  have h1 := gmin_binary_block e 1 1 (v-(3*2^e-1)) hr
  simp only [zero_mul,zero_add] at h0
  simp only [one_mul] at h1
  rw [hsum,h0,h1]
  norm_num [gmin]
  have hc := gmin_binary_low_le hr
  omega

/-- A prescribed primitive index step and a unit one-each phase select
a bounded companion weight with signed period error minus one. -/
theorem exists_unit_phase_index_step_weight {F T κ r q : ℕ}
    (hT : 0 < T) (hq : Nat.Coprime q T) (hdiv : F ∣ κ*r+1) :
    ∃ v : ℕ, v < T ∧ ∃ ν : ℤ, (F : ℤ)*v*q-(κ : ℤ)*r=(F*T : ℕ)*ν+1 := by
  letI : NeZero T := ⟨by omega⟩
  obtain ⟨h,hh⟩ := hdiv
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime q T).mpr hq
  let v := ((↑(u⁻¹) : ZMod T)*(h : ZMod T)).val
  have hv : v < T := ZMod.val_lt _
  have he : (v : ZMod T)*(q : ZMod T)=h := by
    rw [show (v : ZMod T)=(↑(u⁻¹) : ZMod T)*(h : ZMod T) by exact ZMod.natCast_zmod_val _,← hu]
    calc
      _ = ((↑(u⁻¹) : ZMod T)*u)*(h : ZMod T) := by ring
      _ = _ := by rw [Units.inv_mul]; simp
  have hd : (T : ℤ) ∣ (v : ℤ)*q-h := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ T).mp
    push_cast
    exact sub_eq_zero.mpr he
  obtain ⟨ν,hν⟩ := hd
  refine ⟨v,hv,ν,?_⟩
  have hhZ : (κ : ℤ)*r+1=(F : ℤ)*h := by exact_mod_cast hh
  push_cast
  linear_combination (F : ℤ)*hν-hhZ

/-- Primitive factor four needs only the two odd positive index steps. -/
theorem exists_equal_factor_four_phase_weight {T r q : ℕ}
    (hT : 0 < T) (hr : Odd r) (hq : Nat.Coprime q T) :
    ∃ κ v : ℕ, (κ=1 ∨ κ=3) ∧ v < T ∧ ∃ ν : ℤ,
      4*(v : ℤ)*q-(κ : ℤ)*r=(4*T : ℕ)*ν+1 := by
  obtain ⟨k,hk⟩ := hr
  by_cases h : r%4=1
  · have hd : 4 ∣ 3*r+1 := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨v,hv,ν,hν⟩ := exists_unit_phase_index_step_weight hT hq hd
    exact ⟨3,v,Or.inr rfl,hv,ν,hν⟩
  · have hd : 4 ∣ 1*r+1 := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨v,hv,ν,hν⟩ := exists_unit_phase_index_step_weight hT hq hd
    exact ⟨1,v,Or.inl rfl,hv,ν,hν⟩

/-- The actual half-profile cost controls every linear error coefficient
up to the product of the phase denominator and binary companion width. -/
theorem equal_profile_linear_error_lt_axis_width {a n L T C : ℕ}
    (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1) (hT : T+1=2^a)
    (hL : L+2*a=n) (hC : C ≤ 2^a*(2*T)) : C*n < 2^L := by
  have hsmall := equal_maximal_index_error_lt_binary_tail hn hcost hT
  have hmargin := twelve_equal_length_le_of_half_cost hn hcost
  have he : a+(n-3*a)=L := by omega
  have hh := Nat.mul_lt_mul_of_pos_left hsmall (Nat.two_pow_pos a)
  rw [← pow_add,he] at hh
  have hc := Nat.mul_le_mul_right n hC
  nlinarith only [hh,hc]

/-- A signed error smaller than one axis width preserves a rational
upper boundary whenever its leading numerator has one extra unit of gap. -/
theorem axis_interval_of_signed_error_window
    {n K S U R p q : ℕ} {Z : ℤ}
    (hS : 0 < S) (hSU : S ≤ U) (hR : 3 ≤ R) (hp : 1 ≤ p)
    (hwide : U*n < K) (hgap : p*R+p+1 ≤ q*S)
    (hlo : -(U : ℤ)*n < (S : ℤ)*Z-(R : ℤ)*K)
    (hhi : (S : ℤ)*Z-(R : ℤ)*K < (U : ℤ)*n) :
    (n : ℤ) ≤ Z ∧ (p : ℤ)*Z < (q : ℤ)*K := by
  have hSZ : (0 : ℤ) < S := by exact_mod_cast hS
  have hpZ : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  have hwideZ : (U : ℤ)*n < K := by exact_mod_cast hwide
  have hRK := mul_le_mul_of_nonneg_right (show (3 : ℤ) ≤ R by exact_mod_cast hR) (Int.natCast_nonneg K)
  have hSn := mul_le_mul_of_nonneg_right (show (S : ℤ) ≤ U by exact_mod_cast hSU) (Int.natCast_nonneg n)
  have hgapZ : (p : ℤ)*R+p+1 ≤ (q : ℤ)*S := by exact_mod_cast hgap
  have hgapK := mul_le_mul_of_nonneg_right hgapZ (Int.natCast_nonneg K)
  have hK : (0 : ℤ) < K := by exact_mod_cast (show 0 < K by omega)
  constructor
  · apply (mul_le_mul_iff_right₀ hSZ).mp
    nlinarith only [hlo,hwideZ,hRK,hSn]
  · apply (mul_lt_mul_iff_right₀ hSZ).mp
    have hh := mul_lt_mul_of_pos_left hhi hpZ
    have hw := mul_lt_mul_of_pos_left hwideZ hpZ
    nlinarith only [hh,hw,hgapK,hK]

/-- A unit-error primitive index step has a uniform signed scalar identity,
with no restriction on the primitive factor or companion length. -/
theorem unit_phase_index_step_rival_error
    {F T s w K H c V M E α z r q κ v R : ℕ} {ν : ℤ}
    (hbase : H+c=V+1) (hM : M+E=w*K)
    (hphase : (F : ℤ)*v*q-(κ : ℤ)*r=(F*T : ℕ)*ν+1)
    (hR : (R : ℤ)=(F : ℤ)*v-(κ : ℤ)*((s : ℤ)-1)+w)
    (hap : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M) :
    (F*T : ℕ)*((v : ℤ)*z-(κ : ℤ)*α+(1-(v : ℤ))*V-ν*M)-(R : ℤ)*K=
      ((F*T : ℕ)-(F : ℤ)*v+(κ : ℤ)*((s : ℤ)-1))*H+
      ((F*T : ℕ)-(F : ℤ)*v-(κ : ℤ)*s)*c-(F*T : ℕ)-E := by
  have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hm : (M : ℤ)+E=(w : ℤ)*K := by exact_mod_cast hM
  push_cast at hap hphase ⊢
  linear_combination (F : ℤ)*v*hzp-(κ : ℤ)*hap-(F : ℤ)*T*(1-(v : ℤ))*hb+
    hm+(M : ℤ)*hphase-(K : ℤ)*hR

/-- Subtracting an available companion profile transfers its axis charge
to a rival while preserving the actual group target. -/
theorem rival_eq_after_subtracting_companion_profile
    {N Z V c ta tb pa pb ra rb : ℕ} (x a b : ZMod N)
    (hta : ta=ra+pa) (htb : tb=rb+pb)
    (hprofile : pa • a+pb • b=c • x)
    (hrival : Z • x+ta • a+tb • b=V • x) :
    (Z+c) • x+ra • a+rb • b=V • x := by
  calc
    _ = Z • x+(ra+pa) • a+(rb+pb) • b := by
      rw [add_nsmul,← hprofile]
      simp only [add_nsmul]
      abel
    _ = _ := by rw [← hta,← htb]; exact hrival

/-- The two factor-four index steps remain below two full widths. Away
from the upper quarter of step one they lie below seven quarters; the
step-three rival keeps that bound after adding the half-profile charge. -/
theorem equal_factor_four_axis_windows
    {u T κ v R n K H c E : ℕ} {Z : ℤ} (hu : 4 ≤ u) (hT : T+1=4*u)
    (hκ : κ=1 ∨ κ=3) (hv : v < T) (hR : R=4*v+(16-2*κ)*u+κ)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hE : E ≤ 4*u*H) (hwide : 32*u*n < K)
    (herr : (4*T : ℕ)*Z-(R : ℤ)*K=
      ((4*T : ℕ)-4*(v : ℤ)+(κ : ℤ)*(2*(u : ℤ)-1))*H+
      ((4*T : ℕ)-4*(v : ℤ)-(κ : ℤ)*2*u)*c-(4*T : ℕ)-E) :
    (n : ℤ) ≤ Z ∧ Z < 2*K ∧
      ((v < 3*u ∨ κ=3) → 4*Z < 7*K) ∧ (κ=3 → 4*(Z+c) < 7*K) := by
  have hS : 0 < 4*T := by omega
  have hSU : 4*T ≤ 32*u := by omega
  have hRp : 3 ≤ R := by rcases hκ with rfl | rfl <;> norm_num at hR ⊢ <;> omega
  have hgap2 : 1*R+1+1 ≤ 2*(4*T) := by
    rcases hκ with rfl | rfl <;> norm_num at hR ⊢ <;> omega
  have hgap7 : (v < 3*u ∨ κ=3) → 4*R+4+1 ≤ 7*(4*T) := by
    intro hh
    rcases hκ with rfl | rfl <;> norm_num at hR hh ⊢ <;> omega
  have hw := signed_rival_linear_error_window (S:=4*T) (W:=4*u)
    (A:=(4*T : ℕ)-4*(v : ℤ)+(κ : ℤ)*(2*(u : ℤ)-1))
    (B:=(4*T : ℕ)-4*(v : ℤ)-(κ : ℤ)*2*u) (J:=-1) (C:=32*(u : ℤ))
    hH hnc hE hS (by positivity)
    (by rcases hκ with rfl | rfl <;> norm_num <;> omega)
    (by rcases hκ with rfl | rfl <;> norm_num <;> omega)
    (by rcases hκ with rfl | rfl <;> norm_num <;> omega)
    (by rcases hκ with rfl | rfl <;> norm_num <;> omega)
  have helo : -((32*u : ℕ) : ℤ)*n < (4*T : ℕ)*Z-(R : ℤ)*K := by
    push_cast at herr hw ⊢
    nlinarith only [herr,hw.1]
  have hehi : (4*T : ℕ)*Z-(R : ℤ)*K < ((32*u : ℕ) : ℤ)*n := by
    push_cast at herr hw ⊢
    nlinarith only [herr,hw.2]
  have htwo := axis_interval_of_signed_error_window hS hSU hRp (by decide : 1 ≤ 1)
    hwide hgap2 helo hehi
  refine ⟨htwo.1,by simpa using htwo.2,?_,?_⟩
  · intro hh
    exact (axis_interval_of_signed_error_window hS hSU hRp (by decide : 1 ≤ 4)
      hwide (hgap7 hh) helo hehi).2
  · intro hk
    subst κ
    have hw' := signed_rival_linear_error_window (S:=4*T) (W:=4*u)
      (A:=(4*T : ℕ)-4*(v : ℤ)+3*(2*(u : ℤ)-1))
      (B:=(4*T : ℕ)-4*(v : ℤ)-3*2*u+(4*T : ℕ)) (J:=-1) (C:=32*(u : ℤ))
      hH hnc hE hS (by positivity) (by norm_num; omega) (by norm_num; omega)
      (by norm_num; omega) (by norm_num; omega)
    have hslo : -((32*u : ℕ) : ℤ)*n < (4*T : ℕ)*(Z+c)-(R : ℤ)*K := by
      push_cast at herr hw' ⊢
      nlinarith only [herr,hw'.1]
    have hshi : (4*T : ℕ)*(Z+c)-(R : ℤ)*K < ((32*u : ℕ) : ℤ)*n := by
      push_cast at herr hw' ⊢
      nlinarith only [herr,hw'.2]
    exact (axis_interval_of_signed_error_window hS hSU hRp (by decide : 1 ≤ 4)
      hwide (hgap7 (Or.inr rfl)) hslo hshi).2

/-- An axis value below two full widths costs at most two coins beyond
its length. -/
theorem exists_axis_rep_below_two_widths {L z : ℕ} (hL : 1 ≤ L)
    (hz : z < 2*2^L) : ∃ u, val L u=z ∧ dsum L u ≤ L+2 := by
  have hp : 2^L=2*2^(L-1) := by rw [← pow_succ']; congr 1; omega
  have hd : z/2^(L-1) < 4 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hc := gmin_le_top_quotient_add_width (L-1) z
  obtain ⟨u,hu,hcu⟩ := exists_rep_gmin (L-1) z
  have he : L-1+1=L := by omega
  rw [he] at hu hcu
  exact ⟨u,hu,by omega⟩

/-- Every factor-four odd unit primitive phase yields an affordable
actual rival, using half-profile subtraction in the costly upper range. -/
theorem exists_equal_factor_four_primitive_rival
    {a n N L u T M E H c V α z r q : ℕ}
    (ha : 4 ≤ a) (hn : 67 ≤ n) (hu : u=2^(a-2)) (hT : T+1=4*u)
    (hL : L+2*a=n) (hcost : 2^(a+1) ≤ n+1)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=16*u*2^L) (hE : E ≤ 4*u*H)
    (hr : Odd r) (hq : Nat.Coprime q T)
    (hap : (4*T : ℕ)*(α : ℤ)=(2*(u : ℤ)-1)*((2 : ℤ)^L-H)+2*(u : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=u • b) (hz : z • x+b+d=V • x) (hmx : M • x=0)
    (hhalf : (6*u-1) • b+(2*u-1) • d=c • x) :
    ∃ w ta tb, n ≤ w ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) ta+gmin (a-1) tb ≤ n ∧
      w • x+ta • b+tb • d=V • x := by
  have hu4 : 4 ≤ u := by rw [hu]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a-2)
  have hpa : 2^a=4*u := by
    rw [hu,show a=2+(a-2) by omega,pow_add]
    norm_num
  have hwide : 32*u*n < 2^L := by
    apply equal_profile_linear_error_lt_axis_width hn hcost (by omega : T+1=2^a) hL
    rw [hpa]
    nlinarith
  have hLp : 2 ≤ L := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show L ≤ 1 by omega)
    norm_num at hp
    nlinarith
  obtain ⟨κ,v,hκ,hv,ν,hphase⟩ := exists_equal_factor_four_phase_weight (by omega : 0 < T) hr hq
  let R := 4*v+(16-2*κ)*u+κ
  let Z : ℤ := (v : ℤ)*z-(κ : ℤ)*α+(1-(v : ℤ))*V-ν*M
  have hR : (R : ℤ)=4*(v : ℤ)-(κ : ℤ)*(2*(u : ℤ)-1)+16*u := by
    dsimp [R]
    rcases hκ with rfl | rfl <;> norm_num <;> ring
  have herr : (4*T : ℕ)*Z-(R : ℤ)*(2^L : ℕ)=
      ((4*T : ℕ)-4*(v : ℤ)+(κ : ℤ)*(2*(u : ℤ)-1))*H+
      ((4*T : ℕ)-4*(v : ℤ)-(κ : ℤ)*2*u)*c-(4*T : ℕ)-E := by
    have hh := unit_phase_index_step_rival_error (F:=4) (s:=2*u) (w:=16*u) (K:=2^L)
      hbase hM hphase (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hR)
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using hap)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,mul_assoc,Z] using hh
  have hwin := equal_factor_four_axis_windows hu4 hT hκ hv (show R=4*v+(16-2*κ)*u+κ by rfl)
    hH hnc hE hwide herr
  have hnonneg : 0 ≤ Z := le_trans (Int.natCast_nonneg n) hwin.1
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hnonneg
  have hnZ : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by rw [hcast]; exact hwin.1)
  have heval : Z.toNat • x+(v+κ*u) • b+v • d=V • x := by
    have hh := signed_axis_basis_rival_eq x b d (κ : ℤ) ν (ta:=v+κ*u) (tb:=v)
      (by push_cast; ring) hz hα hmx hnonneg
    exact hh
  have hquarter : ∀ w : ℕ, 4*w < 7*2^L → ∃ k, val L k=w ∧ dsum L k ≤ L+1 := by
    intro w hw
    have hp : 2^L=4*2^(L-2) := by rw [show L=2+(L-2) by omega,pow_add]; norm_num
    apply exists_axis_rep_below_seven_quarters hLp
    rw [hp] at hw
    omega
  have hc := equal_factor_four_quarter_coin_bounds (e:=a-2) (v:=v) (by omega) (by rw [← hu]; omega)
  rw [show a-2+1=a-1 by omega,← hu] at hc
  rcases hκ with rfl | rfl
  · simp only [one_mul] at heval
    by_cases hlo : v < 3*u
    · have hh := hwin.2.2.1 (Or.inl hlo)
      have hbnd : 4*Z.toNat < 7*2^L := by
        exact_mod_cast (show 4*(Z.toNat : ℤ) < 7*(2^L : ℕ) by rw [hcast]; exact hh)
      obtain ⟨k,hk,hck⟩ := hquarter Z.toNat hbnd
      have hcoins := hc.1 hlo
      exact ⟨Z.toNat,v+u,v,hnZ,Or.inr (by omega),k,hk,by omega,heval⟩
    · have hbnd : Z.toNat < 2*2^L := by
        exact_mod_cast (show (Z.toNat : ℤ) < 2*(2^L : ℕ) by rw [hcast]; exact hwin.2.1)
      obtain ⟨k,hk,hck⟩ := exists_axis_rep_below_two_widths (by omega) hbnd
      have hcoins := hc.2.1 (by omega)
      exact ⟨Z.toNat,v+u,v,hnZ,Or.inr (by omega),k,hk,by omega,heval⟩
  · by_cases hlo : v < 3*u-1
    · have hh := hwin.2.2.1 (Or.inr rfl)
      have hbnd : 4*Z.toNat < 7*2^L := by
        exact_mod_cast (show 4*(Z.toNat : ℤ) < 7*(2^L : ℕ) by rw [hcast]; exact hh)
      obtain ⟨k,hk,hck⟩ := hquarter Z.toNat hbnd
      have hcoins := hc.2.2 hlo
      exact ⟨Z.toNat,v+3*u,v,hnZ,Or.inr (by omega),k,hk,by omega,heval⟩
    · have hh := hwin.2.2.2 rfl
      have hbnd : 4*(Z.toNat+c) < 7*2^L := by
        exact_mod_cast (show 4*((Z.toNat : ℤ)+c) < 7*(2^L : ℕ) by rw [hcast]; exact hh)
      obtain ⟨k,hk,hck⟩ := hquarter (Z.toNat+c) hbnd
      have hcoins := equal_factor_four_half_shift_coin_bound (e:=a-2) (v:=v)
        (by rw [← hu]; omega) (by rw [← hu]; omega)
      rw [show a-2+1=a-1 by omega,← hu] at hcoins
      have ht : v+3*u=(v-(3*u-1))+(6*u-1) := by omega
      have hb : v=(v-(2*u-1))+(2*u-1) := by omega
      have hnew := rival_eq_after_subtracting_companion_profile x b d ht hb hhalf heval
      exact ⟨Z.toNat+c,v-(3*u-1),v-(2*u-1),by omega,Or.inr (by omega),k,hk,by omega,hnew⟩


end MinModulus
