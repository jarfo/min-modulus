import MinModulus.ChainForestProfileSumTen

/-! Uniform compatible primitive phases for equal companion widths.
The original top and half relations retain a divisibility link even when
the axis period and the primitive denominator have a common factor. A
general certificate handles rivals just below integral binary boundaries. -/

namespace MinModulus

/-- The actual half relation couples the primitive phases for every
equal companion width, without cancelling the denominator modulo the
axis period. -/
theorem equal_companion_primitive_phase_link
    {N D F s T M K H c V z α r q : ℕ} (hs : 1 ≤ s) (hM : 0 < M)
    (hDF : D*F=2*s) (hT : T+1=2*s) (hbase : H+c=V+1)
    (hαphase : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzphase : (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (hhalf : (3*s-1) • a+(s-1) • b=c • x) : T ∣ 2*r+q := by
  let Y : ℤ := (F : ℤ)*α+((s : ℤ)-1)*V-((s : ℤ)-1)*z-c
  have hY : Y • x=0 := by
    have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDF
    push_cast at hDcast
    have h3s : 1 ≤ 3*s := by omega
    simp only [nsmul_eq_mul,Nat.cast_sub h3s,Nat.cast_sub hs,Nat.cast_one,
      Nat.cast_mul,Nat.cast_ofNat] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one]
    linear_combination (F : ZMod N)*hα-((s : ZMod N)-1)*hz+hhalf+hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hTZ : (T : ℤ)+1=2*s := by exact_mod_cast hT
  have hscalar : (T : ℤ)*Y=((r : ℤ)-((s : ℤ)-1)*q)*M := by
    dsimp [Y]
    push_cast at hαphase
    linear_combination hαphase-((s : ℤ)-1)*hzphase-
      ((s : ℤ)-1)*hbaseZ-hTZ*c
  have hcanc : (r : ℤ)-((s : ℤ)-1)*q=(T : ℤ)*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  have hlinkZ : (T : ℤ) ∣ 2*r+q := by
    refine ⟨2*p+q,?_⟩
    linear_combination 2*hcanc-hTZ*q
  exact_mod_cast hlinkZ

/-- Original equal-width top and half relations determine both bounded
primitive phases whenever their two base coefficients lie below the
actual axis period. No coprimality of that period and the denominator
is assumed. -/
theorem exists_equal_companion_bounded_primitive_phases
    {N D F s T K H c V : ℕ} [NeZero N] [NeZero D]
    (hs : 1 ≤ s) (hK : 1 ≤ K) (hHK : H ≤ K)
    (hDF : D*F=2*s) (hT : T+1=2*s) (hbase : H+c=V+1)
    (hBhi : (s-1)*K+s*c < N/D+(s-1)*H)
    (hChi : K+(T-1)*V < N/D+1)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(2*s-1) • a+(2*s-1) • b=V • x)
    (hhalf : (3*s-1) • a+(s-1) • b=c • x) :
    ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
      α • x=D • a ∧ z • x+a+b=V • x ∧ r < F*T ∧ q < T ∧ T ∣ 2*r+q ∧
      (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/D : ℕ) := by
  have h2s : 1 ≤ 2*s := by omega
  have hTpos : 0 < T := by omega
  have hD2s : D ∣ 2*s := ⟨F,hDF.symm⟩
  have hFT : 0 < F*T := by
    have hF : 0 < F := by nlinarith only [hDF,hs]
    positivity
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    h2s h2s hD2s hD2s x a b hindex htop
  obtain ⟨α,hα,hαrel⟩ := exists_companion_multiple_axis_coefficient x a hindex
  have ho : addOrderOf x=N/D := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  let B := (s-1)*K+s*c-(s-1)*H
  have hB : B+(s-1)*H=(s-1)*K+s*c := by
    have hh := Nat.mul_le_mul_left (s-1) hHK
    dsimp [B]
    omega
  have hprimitive : (F*T*α) • x=B • x := by
    have hh := equal_companion_axis_multiple_relation hs hK hDF hbase hB x a b hαrel htop hhalf
    simpa only [show 2*s-1=T by omega] using hh
  obtain ⟨r,hr,hrrel⟩ := exists_bounded_axis_multiple_phase x ho hFT hα (by omega : B < N/D) hprimitive
  let C := K+(T-1)*V-1
  have hC : C+1=K+(T-1)*V := by dsimp [C]; omega
  have honeeach : (T*z) • x=C • x := by
    have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
    push_cast at hCcast
    simp only [Nat.cast_sub hTpos,Nat.cast_one] at hCcast
    rw [show 2*s-1=T by omega] at htop
    simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one,Nat.cast_mul] at hzrel htop ⊢
    linear_combination (T : ZMod N)*hzrel-htop-hCcast*x
  obtain ⟨q,hq,hqrel⟩ := exists_bounded_axis_multiple_phase x ho hTpos hz (by omega : C < N/D) honeeach
  have hrZ : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*(N/D : ℕ) := by
    have hh : (F*T : ℕ)*(α : ℤ)=(B : ℤ)+(r : ℤ)*(N/D : ℕ) := by exact_mod_cast hrrel
    have hBZ := congrArg (fun t : ℕ ↦ (t : ℤ)) hB
    push_cast at hBZ
    simp only [Nat.cast_sub hs,Nat.cast_one] at hBZ
    linear_combination hh+hBZ
  have hqZ : (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/D : ℕ) := by
    have hh : (T : ℤ)*z=(C : ℤ)+(q : ℤ)*(N/D : ℕ) := by exact_mod_cast hqrel
    have hCZ := congrArg (fun t : ℕ ↦ (t : ℤ)) hC
    push_cast at hCZ
    simp only [Nat.cast_sub hTpos,Nat.cast_one] at hCZ
    linear_combination hh+hCZ
  have hlink := equal_companion_primitive_phase_link hs (by omega : 0 < N/D) hDF hT hbase
    hrZ hqZ x a b ho hαrel hzrel hhalf
  exact ⟨α,z,r,q,hα,hz,hαrel,hzrel,hr,hq,hlink,hrZ,hqZ⟩


/-- A nonpositive error cone fixes the prefix immediately preceding an
integral boundary. The full lower block is charged to the axis length. -/
def PrimitiveBasisBelowIntegralCertificate (g : PrimitiveBasisGeometry)
    (C n₀ : ℕ) (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) : Prop :=
  PrimitiveBasisPlanRelation g P Q r q p ∧
  0 < g.F*g.T ∧ 1 ≤ n₀ ∧ 1 ≤ p.shift ∧ g.a+g.b+p.shift ≤ n₀ ∧
  0 < C ∧ C*n₀ < 2^(n₀-(g.a+g.b+p.shift)) ∧ 2 ≤ p.boundary ∧
  (g.F*g.T)*p.boundary=2^p.shift*p.R ∧
  gmin (p.shift-1) (p.boundary-1)+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤ g.a+g.b+p.shift ∧
  -(C*(g.F*g.T) : ℕ) < primitiveBasisRivalA g p P Q-(g.F*g.T : ℕ)+min (primitiveBasisRivalJ g p r q) 0*g.W ∧
  -(C*(g.F*g.T) : ℕ) ≤ primitiveBasisRivalB g p ∧
  primitiveBasisRivalA g p P Q+max (primitiveBasisRivalJ g p r q) 0*g.W ≤ 0 ∧
  primitiveBasisRivalB g p ≤ 0

instance (g : PrimitiveBasisGeometry) (C n₀ : ℕ) (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) :
    Decidable (PrimitiveBasisBelowIntegralCertificate g C n₀ P Q r q p) := by
  unfold PrimitiveBasisBelowIntegralCertificate
  infer_instance

/-- A certificate below an integral boundary yields an actual group
rival at every larger length, with the entire borrowed block budgeted. -/
theorem exists_rival_of_primitive_basis_below_integral_certificate
    (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    {C n₀ n N L M E H c V α z : ℕ} {P Q r q : ℤ}
    (hn : n₀ ≤ n) (hL : L+g.a+g.b=n)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=g.w*2^L) (hE : E ≤ g.W*H)
    (hap : (g.F*g.T : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+(g.t : ℤ)*c+r*M)
    (hzp : (g.T : ℤ)*z=Q*(2 : ℤ)^L+((g.T : ℤ)-Q)*H+((g.T : ℤ)-g.v)*c-g.T+q*M)
    (x a b : ZMod N) (hα : α • x=g.D • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0)
    (hp : PrimitiveBasisBelowIntegralCertificate g C n₀ P Q r q p) :
    ∃ s, n ≤ s ∧ (p.ta ≠ 2^g.a-1 ∨ p.tb ≠ 2^g.b-1) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤ n ∧
      s • x+p.ta • a+p.tb • b=V • x := by
  rcases hp with ⟨⟨hta,hne,hR⟩,hS,hn₀,hshift,hreserved,hC,hsmall₀,hbp,hb,hcost,hA0,hB0,hA1,hB1⟩
  let A := primitiveBasisRivalA g p P Q
  let B := primitiveBasisRivalB g p
  let J := primitiveBasisRivalJ g p r q
  let Z := primitiveBasisRivalZ p α z V M
  let e := L-p.shift
  have he : e+(p.shift-1+1)=L := by dsimp [e]; omega
  have hpow : 2^L=2^p.shift*2^e := by
    rw [← pow_add,show p.shift+e=L by dsimp [e]; omega]
  have hboundaryeq : (g.F*g.T : ℕ)*(p.boundary*2^e : ℕ)=(p.R : ℤ)*2^L := by
    have hh : (g.F*g.T)*(p.boundary*2^e)=p.R*2^L := by
      rw [← Nat.mul_assoc,hb,hpow]
      ring
    exact_mod_cast hh
  have herr := primitive_basis_rival_error g p hbase hM
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp) hR
  have herr' : (g.F*g.T : ℕ)*(Z-(p.boundary*2^e : ℕ))=A*H+B*c-(g.F*g.T : ℕ)+J*E := by
    dsimp [Z,A,B,J]
    push_cast at herr hboundaryeq ⊢
    linear_combination herr-hboundaryeq
  have hw := signed_rival_linear_error_window
    (S:=g.F*g.T) (W:=g.W) (A:=A) (B:=B) (J:=J) (C:=(C*(g.F*g.T) : ℕ))
    hH hnc hE hS (by positivity) hA0 hB0
    (le_trans hA1 (by positivity)) (le_trans hB1 (by positivity))
  have hJhi : J*E ≤ max J 0*(g.W : ℤ)*H := by
    by_cases hJ : 0 ≤ J
    · rw [max_eq_left hJ]
      have hEZ : (E : ℤ) ≤ (g.W : ℤ)*H := by exact_mod_cast hE
      nlinarith only [mul_le_mul_of_nonneg_left hEZ hJ]
    · rw [max_eq_right (by omega : J ≤ 0),zero_mul,zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
  have hnonpos : A*H+B*c+J*E ≤ 0 := by
    have ha := mul_nonpos_of_nonpos_of_nonneg hA1 (show (0 : ℤ) ≤ H by positivity)
    have hb' := mul_nonpos_of_nonpos_of_nonneg hB1 (show (0 : ℤ) ≤ c by positivity)
    change (primitiveBasisRivalA g p P Q+max (primitiveBasisRivalJ g p r q) 0*g.W)*(H : ℤ) ≤ 0 at ha
    dsimp only [A,B,J] at hJhi ⊢
    nlinarith only [ha,hb',hJhi]
  have hSZ : (0 : ℤ) < (g.F*g.T : ℕ) := by exact_mod_cast hS
  have hnegative : Z < (p.boundary*2^e : ℕ) := by
    by_contra hh
    have hm := mul_nonneg (le_of_lt hSZ) (sub_nonneg.mpr (le_of_not_gt hh))
    linarith only [hm,herr',hnonpos,hSZ]
  have hsmall : C*n < 2^e := by
    dsimp [e]
    rw [show L-p.shift=n-(g.a+g.b+p.shift) by omega]
    exact linear_error_lt_two_pow_sub_of_base hn₀ hn hreserved hsmall₀
  have hsmallZ : (C*(g.F*g.T) : ℕ)*(n : ℤ) < (g.F*g.T : ℕ)*(2 : ℤ)^e := by
    have hh := Nat.mul_lt_mul_of_pos_left hsmall hS
    push_cast
    exact_mod_cast (show C*(g.F*g.T)*n < (g.F*g.T)*2^e by nlinarith only [hh])
  have hlow : ((p.boundary-1)*2^e : ℕ) < Z := by
    have hpcast : ((p.boundary-1 : ℕ) : ℤ)=(p.boundary : ℤ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    by_contra hh
    have hh' : Z ≤ ((p.boundary-1)*2^e : ℕ) := le_of_not_gt hh
    have hm := mul_le_mul_of_nonneg_left hh' (le_of_lt hSZ)
    push_cast at hm herr' hw hsmallZ
    rw [hpcast] at hm
    nlinarith only [hm,herr',hw.1,hsmallZ]
  have hZ : 0 ≤ Z := by
    have hh : (0 : ℤ) ≤ ((p.boundary-1)*2^e : ℕ) := by positivity
    omega
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hlo : (p.boundary-1)*2^e ≤ Z.toNat := by
    exact_mod_cast (show ((p.boundary-1)*2^e : ℕ) ≤ (Z.toNat : ℤ) by rw [hcast]; exact le_of_lt hlow)
  have hhi : Z.toNat < p.boundary*2^e := by
    exact_mod_cast (show (Z.toNat : ℤ) < (p.boundary*2^e : ℕ) by rw [hcast]; exact hnegative)
  have hrem : Z.toNat-(p.boundary-1)*2^e < 2^e := by
    have hh : p.boundary*2^e=(p.boundary-1)*2^e+2^e := by
      have hh : p.boundary-1+1=p.boundary := by omega
      calc
        p.boundary*2^e=(p.boundary-1+1)*2^e := by rw [hh]
        _=(p.boundary-1)*2^e+2^e := by ring
    omega
  obtain ⟨u,hu,hcu⟩ := exists_rep_binary_block_tail (p.shift-1) e (p.boundary-1)
    (Z.toNat-(p.boundary-1)*2^e) hrem
  rw [he,Nat.add_sub_of_le hlo] at hu
  rw [he] at hcu
  have hnZ : n ≤ Z.toNat := by
    have hh := Nat.mul_le_mul_right n hC
    have hp := Nat.mul_le_mul_right (2^e) (show 1 ≤ p.boundary-1 by omega)
    omega
  refine ⟨Z.toNat,hnZ,hne,u,hu,by dsimp [e] at hcu; omega,?_⟩
  exact signed_axis_basis_rival_eq x a b p.κ p.ν hta hz hα hmx hZ


end MinModulus
