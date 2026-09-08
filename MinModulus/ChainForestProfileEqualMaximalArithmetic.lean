import MinModulus.ChainForestProfileEqualStratum

/-! Uniform modular multipliers and variable binary prefixes cover every
maximal-index equal-companion phase. The integral exception has separate
representations below and above its sparse boundary. -/

namespace MinModulus

/-- Every value below the binary width uses at most one coin per position. -/
theorem gmin_le_of_lt_binary_width {w t : ℕ} (ht : t < 2^(w+1)) :
    gmin w t ≤ w+1 := by
  have hh := gmin_le_top_quotient_add_width w t
  have hp : 2^(w+1)=2^w*2 := by rw [pow_succ]
  have hd : t/2^w < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  omega

/-- A value strictly below the all-ones word saves at least one coin. -/
theorem gmin_le_of_lt_binary_ones {w t : ℕ} (ht : t < 2^(w+1)-1) :
    gmin w t ≤ w := by
  induction w generalizing t with
  | zero => norm_num [gmin] at *; omega
  | succ w ih =>
    have hp : 2^(w+1+1)=2*2^(w+1) := by rw [pow_succ']
    have hm := Nat.mod_lt t (by decide : 0 < 2)
    have hd := Nat.mod_add_div t 2
    by_cases he : t%2=0
    · have hh : t/2 < 2^(w+1) := by omega
      rw [gmin,he]
      have hh' := gmin_le_of_lt_binary_width hh
      omega
    · have hh : t/2 < 2^(w+1)-1 := by omega
      rw [gmin]
      have hh' := ih hh
      omega

/-- The actual half-profile cost leaves a uniform linear margin in the
common companion length. -/
theorem twelve_equal_length_le_of_half_cost {a n : ℕ}
    (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1) : 12*a ≤ n := by
  by_cases ha : a ≤ 5
  · omega
  · have hp : ∀ b, 6 ≤ b → 12*b+1 ≤ 2^(b+1) := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => norm_num
      | succ b hb ih =>
        rw [show b+1+1=(b+1)+1 by omega,pow_succ]
        nlinarith
    have hh := hp a (by omega)
    omega

/-- At the variable prefix width, the full linear phase error is smaller
than one lower binary block, uniformly in the companion length. -/
theorem equal_maximal_index_error_lt_binary_tail {a n T : ℕ}
    (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1) (hT : T+1=2^a) :
    2*T*n < 2^(n-3*a) := by
  have ha := twelve_equal_length_le_of_half_cost hn hcost
  have hwide := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
  have hp : 2^(a+1)=2*2^a := by rw [pow_succ']
  have hTn : 2*T ≤ 2*n := by omega
  have hsq : (2*n)*(2*n) < (2^(n/3-2))*(2^(n/3-2)) :=
    Nat.mul_self_lt_mul_self hwide
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show (n/3-2)+(n/3-2) ≤ n-3*a by omega)
  rw [pow_add] at hpow
  have hmul := Nat.mul_le_mul_right n hTn
  nlinarith

/-- Every nonexceptional phase has a strict sub-top annihilator or inverse. -/
theorem exists_equal_maximal_index_small_phase_multiplier
    {T q : ℕ} (hT : 3 ≤ T) (hq : q < T) (hne : q ≠ T-1) :
    ∃ t ν j : ℕ, 1 ≤ t ∧ t < T ∧ (j=0 ∨ j=1) ∧
      t*q=T*ν+j ∧ (j=1 → t < T-1) := by
  by_cases hc : Nat.Coprime q T
  · letI : NeZero T := ⟨by omega⟩
    letI : Fact (1 < T) := ⟨by omega⟩
    obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime q T).mpr hc
    let t := (↑(u⁻¹) : ZMod T).val
    have ht : t < T := ZMod.val_lt _
    have he : (t : ZMod T)*(q : ZMod T)=1 := by
      rw [show (t : ZMod T)=↑(u⁻¹) by exact ZMod.natCast_zmod_val _ ,← hu]
      exact Units.inv_mul u
    have hm : (t*q)%T=1 := by
      have hh := congrArg ZMod.val he
      simpa only [← Nat.cast_mul,ZMod.val_natCast,ZMod.val_one,if_neg (by omega : T ≠ 1)] using hh
    have htpos : 1 ≤ t := by
      by_contra hh
      have hz : t=0 := by omega
      simp [hz] at hm
    have hte : t ≠ T-1 := by
      intro hh
      have heq := Nat.mod_add_div (t*q) T
      have htT : t+1=T := by omega
      have hdiv : T ∣ q+1 := by
        apply Nat.dvd_of_mod_eq_zero
        have hn : q+1+T*((t*q)/T)=T*q := by nlinarith only [heq,hm,htT]
        have hd : T ∣ q+1+T*((t*q)/T) := by rw [hn]; exact dvd_mul_right T q
        exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_iff_left (dvd_mul_right T _)).mpr hd)
      have hlo : T ≤ q+1 := Nat.le_of_dvd (by omega) hdiv
      omega
    refine ⟨t,(t*q)/T,1,htpos,ht,Or.inr rfl,?_,by omega⟩
    have hh := Nat.mod_add_div (t*q) T
    omega
  · let d := Nat.gcd q T
    have hdT : d ∣ T := Nat.gcd_dvd_right q T
    have hdq : d ∣ q := Nat.gcd_dvd_left q T
    have hd : 2 ≤ d := by
      have hp : 0 < d := Nat.gcd_pos_of_pos_right q (by omega)
      change Nat.gcd q T ≠ 1 at hc
      omega
    have heT : d*(T/d)=T := Nat.mul_div_cancel' hdT
    have heq : d*(q/d)=q := Nat.mul_div_cancel' hdq
    have htpos : 1 ≤ T/d := by nlinarith
    have ht : T/d < T := by nlinarith
    refine ⟨T/d,q/d,0,htpos,ht,Or.inl rfl,?_,by omega⟩
    calc
      T/d*q = T/d*(d*(q/d)) := by rw [heq]
      _ = (d*(T/d))*(q/d) := by ring
      _ = T*(q/d)+0 := by rw [heT]; omega

/-- Equal-weight maximal-index geometry only uses the one-each basis. -/
def equalMaximalGeometry (a T W : ℕ) : PrimitiveBasisGeometry :=
  ⟨a,a,0,1,T,T+1,W,0,1⟩

def equalMaximalPlan (T t ν j : ℕ) : PrimitiveBasisRivalPlan :=
  ⟨0,ν,t,t,t+(T+1)*j,0,0⟩

/-- A modular annihilator or inverse gives a uniform variable-width
nonintegral certificate. -/
theorem equal_maximal_index_nonintegral_certificate
    {a n T W q t ν j : ℕ} (ha : 2 ≤ a) (hn : 67 ≤ n)
    (hcost : 2^(a+1) ≤ n+1) (hT : T+1=2^a) (hW : W ≤ T)
    (htpos : 1 ≤ t) (ht : t < T) (hj : j=0 ∨ j=1)
    (hphase : t*q=T*ν+j) (ht' : j=1 → t < T-1) :
    PrimitiveBasisNonintegralCertificate (equalMaximalGeometry a T W)
      a (2*T) n 0 1 0 q (equalMaximalPlan T t ν j) := by
  have hTpos : 0 < T := by omega
  have hmargin := twelve_equal_length_le_of_half_cost hn hcost
  have hsmall := equal_maximal_index_error_lt_binary_tail hn hcost hT
  have hpow : 2^(a-1+1)=2^a := by congr 1; omega
  have hc : gmin (a-1) t ≤ a-1 := gmin_le_of_lt_binary_ones (by omega)
  have hrel : PrimitiveBasisPlanRelation (equalMaximalGeometry a T W) 0 1 0 q
      (equalMaximalPlan T t ν j) := by
    refine ⟨by simp [equalMaximalGeometry,equalMaximalPlan],Or.inl (by
      simp only [equalMaximalGeometry,equalMaximalPlan]
      omega),?_⟩
    have hh : (t : ℤ)*q=(T : ℤ)*ν+j := by exact_mod_cast hphase
    dsimp [equalMaximalGeometry,equalMaximalPlan]
    nlinarith only [congrArg (fun z : ℤ ↦ ((T : ℤ)+1)*z) hh]
  have hJ : primitiveBasisRivalJ (equalMaximalGeometry a T W) (equalMaximalPlan T t ν j) 0 q=-(j : ℤ) := by
    have hh : (t : ℤ)*q=(T : ℤ)*ν+j := by exact_mod_cast hphase
    dsimp [primitiveBasisRivalJ,equalMaximalGeometry,equalMaximalPlan]
    linarith
  have hA : primitiveBasisRivalA (equalMaximalGeometry a T W) (equalMaximalPlan T t ν j) 0 1=(T : ℤ)-t := by
    simp [primitiveBasisRivalA,equalMaximalGeometry,equalMaximalPlan]
  have hB : primitiveBasisRivalB (equalMaximalGeometry a T W) (equalMaximalPlan T t ν j)=(T : ℤ)-t := by
    simp [primitiveBasisRivalB,equalMaximalGeometry,equalMaximalPlan]
  have hprefix : 0 < ((t+(T+1)*j)*2^a)%T ∧
      gmin (a-1) (((t+(T+1)*j)*2^a)/T)+2*gmin (a-1) t ≤ 3*a := by
    rcases hj with rfl | rfl
    · have he : (t+(T+1)*0)*2^a=t+T*t := by rw [← hT]; ring
      rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]
      have hd : (t+T*t)/T=t := by rw [Nat.add_mul_div_left _ _ hTpos,Nat.div_eq_of_lt ht,zero_add]
      rw [hd]
      exact ⟨by omega,by omega⟩
    · have htt : t+1 < T := by have hh := ht' rfl; omega
      have he : (t+(T+1)*1)*2^a=(t+1)+T*(t+T+2) := by rw [← hT]; ring
      rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt htt]
      have hd : (t+1+T*(t+T+2))/T=t+T+2 := by rw [Nat.add_mul_div_left _ _ hTpos,Nat.div_eq_of_lt htt,zero_add]
      rw [hd]
      have hcc : gmin (a-1) (t+1) ≤ a-1 := gmin_le_of_lt_binary_ones (by omega)
      have hp : t+T+2=(t+1)+2^a := by omega
      have hp' : 2^a=2^(a-1)+2^(a-1) := by
        rw [← two_mul,← pow_succ']; congr 1; omega
      rw [hp,hp',← Nat.add_assoc,gmin_add_pow,gmin_add_pow]
      exact ⟨by omega,by omega⟩
  refine ⟨hrel,by simpa [equalMaximalGeometry] using hTpos,by omega,by omega,
    by simpa [equalMaximalGeometry] using (show a+a+a ≤ n by omega),by omega,
    by simpa [equalMaximalGeometry,show a+a+a=3*a by omega] using hsmall,
    by simp only [equalMaximalGeometry,one_mul]; omega,
    by simp only [equalMaximalPlan]; omega,
    by simpa [equalMaximalGeometry,equalMaximalPlan] using hprefix.1,
    by simp only [equalMaximalGeometry,equalMaximalPlan,one_mul]; omega,?_,?_,?_,?_⟩
  all_goals try rw [hA]
  all_goals try rw [hB]
  all_goals try rw [hJ]
  all_goals try simp only [equalMaximalGeometry,one_mul]
  all_goals rcases hj with rfl | rfl <;> norm_num <;> omega

/-- The sole integral phase has an affordable equal-weight rival on
either side of the two-width boundary. -/
theorem exists_equal_maximal_index_exceptional_rival
    {a n N L T W M E H c V z : ℕ} (ha : 2 ≤ a) (hn : 67 ≤ n)
    (hcost : 2^(a+1) ≤ n+1) (hT : T+1=2^a) (hW : 2*W ≤ T)
    (hL : L+2*a=n) (hwidth : 2*n ≤ 2^L)
    (_hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=(T+1)*2^L) (hE : E ≤ W*H)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+((T : ℤ)-1)*M)
    (x b d : ZMod N) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ s, n ≤ s ∧ T-1 ≠ 2^a-1 ∧ ∃ u,
      val L u=s ∧ dsum L u+2*gmin (a-1) (T-1) ≤ n ∧
      s • x+(T-1) • b+(T-1) • d=V • x := by
  have hTp : 3 ≤ T := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    norm_num at hp
    omega
  have hLp : 1 ≤ L := by
    by_contra hh
    have hzero : L=0 := by omega
    simp only [hzero,pow_zero] at hwidth
    omega
  have hp : 2^L=2*2^(L-1) := by rw [← pow_succ']; congr 1; omega
  have hmargin := twelve_equal_length_le_of_half_cost hn hcost
  have htail := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
  have hc : gmin (a-1) (T-1) ≤ a-1 := gmin_le_of_lt_binary_ones (by
    have he : a-1+1=a := by omega
    rw [he,← hT]
    omega)
  let Z : ℤ := ((T-1 : ℕ) : ℤ)*z+(1-((T-1 : ℕ) : ℤ))*V-((T-2 : ℕ) : ℤ)*M
  have herr : (T : ℤ)*(Z-2*(2 : ℤ)^L)=(H : ℤ)+c-T-E := by
    have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    have hm : (M : ℤ)+E=((T : ℤ)+1)*(2 : ℤ)^L := by exact_mod_cast hM
    dsimp [Z]
    simp only [Nat.cast_sub (show 1 ≤ T by omega),Nat.cast_sub (show 2 ≤ T by omega),Nat.cast_one,Nat.cast_ofNat]
    linear_combination ((T : ℤ)-1)*hzp-(T : ℤ)*(2-(T : ℤ))*hb+hm
  have hEn : E+T ≤ T*n := by
    have hh := Nat.mul_le_mul_left W (show H ≤ n by omega)
    have hh' := Nat.mul_le_mul_right n hW
    have hh'' := Nat.mul_le_mul_left T (show 2 ≤ n by omega)
    nlinarith only [hE,hh,hh',hh'']
  have hlow : 2*(2 : ℤ)^L-n ≤ Z := by
    have he : (E : ℤ)+T ≤ (T : ℤ)*n := by exact_mod_cast hEn
    have ht : (0 : ℤ) < T := by exact_mod_cast (show 0 < T by omega)
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith only [herr,he,Int.natCast_nonneg H,Int.natCast_nonneg c]
  have hhigh : Z < 2*(2 : ℤ)^L+n := by
    have hnc' : (H : ℤ)+c ≤ n := by exact_mod_cast hnc
    have ht : (1 : ℤ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
    apply (mul_lt_mul_iff_right₀ (show (0 : ℤ) < T by omega)).mp
    have hmul := mul_le_mul_of_nonneg_right ht (Int.natCast_nonneg n)
    nlinarith only [herr,hnc',ht,hmul,Int.natCast_nonneg E]
  have hnonneg : 0 ≤ Z := by
    have hw : 2*(n : ℤ) ≤ (2 : ℤ)^L := by exact_mod_cast hwidth
    linarith only [hlow,hw,Int.natCast_nonneg n]
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hnonneg
  have hlo : 2*2^L ≤ Z.toNat+n := by
    exact_mod_cast (show 2*(2 : ℤ)^L ≤ (Z.toNat : ℤ)+n by rw [hcast]; linarith only [hlow])
  have hhi : Z.toNat < 2*2^L+n := by
    exact_mod_cast (show (Z.toNat : ℤ) < 2*(2 : ℤ)^L+n by rw [hcast]; exact hhigh)
  have hrep : ∃ u, val L u=Z.toNat ∧ dsum L u+2*gmin (a-1) (T-1) ≤ n := by
    by_cases hb : Z.toNat < 2*2^L
    · have hbound : 3*2^(L-1) ≤ Z.toNat := by omega
      have hrem : Z.toNat-3*2^(L-1) < 2^(L-1) := by omega
      obtain ⟨u,hu,hcu⟩ := exists_rep_binary_block_tail 0 (L-1) 3 (Z.toNat-3*2^(L-1)) hrem
      have he : L-1+(0+1)=L := by omega
      rw [he,Nat.add_sub_of_le hbound] at hu
      rw [he] at hcu
      norm_num [gmin] at hcu
      exact ⟨u,hu,by omega⟩
    · have hbound : 4*2^(L-1) ≤ Z.toNat := by omega
      have hrem : Z.toNat-4*2^(L-1) < 2^(n/3-2) := by omega
      obtain ⟨u,hu,hcu⟩ := exists_rep_binary_block_bounded_tail 0 (L-1) (n/3-2) 4
        (Z.toNat-4*2^(L-1)) (by omega) hrem
      have he : L-1+(0+1)=L := by omega
      rw [he,Nat.add_sub_of_le hbound] at hu
      rw [he] at hcu
      norm_num [gmin] at hcu
      exact ⟨u,hu,by omega⟩
  obtain ⟨u,hu,hcu⟩ := hrep
  refine ⟨Z.toNat,by omega,by omega,u,hu,hcu,?_⟩
  have hh := signed_axis_basis_rival_eq (D:=0) (α:=0) x b d 0 ((T-2 : ℕ) : ℤ)
    (ta:=T-1) (tb:=T-1) (by simp) hz (by simp) hmx
    (by simpa only [zero_mul,sub_zero] using hnonneg)
  simpa only [zero_mul,sub_zero,Z] using hh

/-- Every maximal-index equal-companion phase admits an affordable
actual rival, at arbitrary common companion lengths. -/
theorem exists_equal_maximal_index_rival
    {a n N L T W M E H c V z q : ℕ} (ha : 2 ≤ a) (hn : 67 ≤ n)
    (hcost : 2^(a+1) ≤ n+1) (hT : T+1=2^a) (hW : 2*W ≤ T)
    (hL : L+2*a=n) (hwidth : 2*n ≤ 2^L)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=(T+1)*2^L) (hE : E ≤ W*H) (hq : q < T)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ s t, n ≤ s ∧ t ≠ 2^a-1 ∧ ∃ u,
      val L u=s ∧ dsum L u+2*gmin (a-1) t ≤ n ∧
      s • x+t • b+t • d=V • x := by
  have hTp : 3 ≤ T := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    norm_num at hp
    omega
  by_cases he : q=T-1
  · obtain ⟨s,hs,hne,u,hu,hcu,heval⟩ := exists_equal_maximal_index_exceptional_rival
      ha hn hcost hT hW hL hwidth hH hnc hbase hM hE (by
        simpa only [he,Nat.cast_sub (show 1 ≤ T by omega),Nat.cast_one] using hzp) x b d hz hmx
    exact ⟨s,T-1,hs,hne,u,hu,hcu,heval⟩
  · obtain ⟨t,ν,j,htpos,ht,hj,hphase,ht'⟩ :=
      exists_equal_maximal_index_small_phase_multiplier hTp hq he
    have hcert := equal_maximal_index_nonintegral_certificate ha hn hcost hT
      (by omega : W ≤ T) htpos ht hj hphase ht'
    obtain ⟨s,hs,hne,u,hu,hcu,heval⟩ := exists_rival_of_primitive_basis_nonintegral_certificate
      (equalMaximalGeometry a T W) (equalMaximalPlan T t ν j)
      (n:=n) (N:=N) (L:=L) (M:=M) (E:=E) (H:=H) (c:=c) (V:=V) (α:=0) (z:=z)
      (P:=0) (Q:=1) (r:=0) (q:=q) (by rfl)
      (by simpa [equalMaximalGeometry,two_mul,add_assoc] using hL) hH hnc hbase hM hE
      (by simp [equalMaximalGeometry]) (by simpa [equalMaximalGeometry] using hzp)
      x b d (by simp [equalMaximalGeometry]) hz hmx hcert
    refine ⟨s,t,hs,?_,u,hu,?_,heval⟩
    · simpa only [equalMaximalPlan,equalMaximalGeometry,or_self] using hne
    · simpa only [equalMaximalPlan,equalMaximalGeometry,two_mul,add_assoc] using hcu


end MinModulus
