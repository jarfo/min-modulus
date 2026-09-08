import MinModulus.ChainForestProfileTwoSeven

/-! Uniform certificates for signed primitive-basis rivals. The same
scalar identity handles arbitrary companion lengths and both equal and
unequal phase formulas. Nonintegral prefixes and integral sparse boundaries
have separate certificates, each producing an actual group rival and an
affordable full-length representation. Choosing certificates uniformly is
still an independent obligation. -/

namespace MinModulus

def boundedPrimitivePhase (T m r : ℕ) : ℕ := ((-(m : ℤ)*r)%(T : ℤ)).toNat

def positivePrimitivePhase (T m r : ℕ) : ℕ :=
  if boundedPrimitivePhase T m r=0 then T else boundedPrimitivePhase T m r

/-- The exact phase link determines the bounded endpoint convention,
without any coprimality hypothesis on the primitive denominator. -/
theorem bounded_primitive_phase_eq_of_link
    {T m r q : ℕ} (_hT : 0 < T) (hq : q < T) (hlink : T ∣ m*r+q) :
    q=boundedPrimitivePhase T m r := by
  have hlinkZ : (T : ℤ) ∣ (m : ℤ)*r+q := by exact_mod_cast hlink
  have hh : (q : ℤ)%(T : ℤ)=(-(m : ℤ)*r)%(T : ℤ) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    have he : (q : ℤ)-(-(m : ℤ)*r)=(m : ℤ)*r+q := by ring
    rw [he]
    exact Int.emod_eq_zero_of_dvd hlinkZ
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hq)] at hh
  have he := congrArg Int.toNat hh
  simpa only [Int.toNat_natCast,boundedPrimitivePhase] using he

/-- The positive endpoint convention sends a zero reduced phase to the
full denominator. All other phases agree with the bounded convention. -/
theorem positive_primitive_phase_eq_of_link
    {T m r q : ℕ} (hT : 0 < T) (hlo : 1 ≤ q) (hhi : q ≤ T) (hlink : T ∣ m*r+q) :
    q=positivePrimitivePhase T m r := by
  have hlink' : T ∣ m*r+q%T := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod,Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hlink
  have hh := bounded_primitive_phase_eq_of_link hT (Nat.mod_lt q hT) hlink'
  by_cases he : q=T
  · subst q
    simp only [Nat.mod_self] at hh
    simp only [positivePrimitivePhase,← hh,if_true]
  · have hq : q < T := by omega
    rw [Nat.mod_eq_of_lt hq] at hh
    simp only [positivePrimitivePhase,← hh,show q ≠ 0 by omega,if_false]



/-- Companion lengths and coefficients of the two primitive phase
relations. `w` is the full period width and `W` bounds its deficit per
unit height; `t` and `v` are the respective drop coefficients. -/
structure PrimitiveBasisGeometry where
  a : ℕ
  b : ℕ
  D : ℕ
  F : ℕ
  T : ℕ
  w : ℕ
  W : ℕ
  t : ℕ
  v : ℕ
  deriving DecidableEq

/-- Signed basis multiples and nonnegative companion weights. Integral
certificates also use the last two fields for their sparse boundary. -/
structure PrimitiveBasisRivalPlan where
  κ : ℤ
  ν : ℤ
  ta : ℕ
  tb : ℕ
  R : ℕ
  boundary : ℕ
  shift : ℕ
  deriving DecidableEq

def primitiveBasisRivalZ (p : PrimitiveBasisRivalPlan) (α z V M : ℕ) : ℤ :=
  (p.tb : ℤ)*z-p.κ*α+(1-(p.tb : ℤ))*V-p.ν*M

def primitiveBasisRivalA (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    (P Q : ℤ) : ℤ := (g.F*g.T : ℕ)-(g.F : ℤ)*p.tb*Q+p.κ*P

def primitiveBasisRivalB (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan) : ℤ :=
  (g.F*g.T : ℕ)-(g.F : ℤ)*p.tb*g.v-p.κ*g.t

def primitiveBasisRivalJ (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    (r q : ℤ) : ℤ := (g.F*g.T : ℕ)*p.ν-(g.F : ℤ)*p.tb*q+p.κ*r

def PrimitiveBasisPlanRelation (g : PrimitiveBasisGeometry)
    (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) : Prop :=
  (p.ta : ℤ)=p.tb+(g.D : ℤ)*p.κ ∧
  (p.ta ≠ 2^g.a-1 ∨ p.tb ≠ 2^g.b-1) ∧
  (p.R : ℤ)=(g.F : ℤ)*p.tb*(Q+(g.w : ℤ)*q)-p.κ*(P+(g.w : ℤ)*r)-
    (g.F*g.T : ℕ)*p.ν*g.w

instance (g : PrimitiveBasisGeometry) (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) :
    Decidable (PrimitiveBasisPlanRelation g P Q r q p) := by
  unfold PrimitiveBasisPlanRelation
  infer_instance

/-- A nonintegral rational prefix, companion cost, and signed coefficient
window are certified once at a starting length. -/
def PrimitiveBasisNonintegralCertificate (g : PrimitiveBasisGeometry)
    (bits U n₀ : ℕ) (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) : Prop :=
  PrimitiveBasisPlanRelation g P Q r q p ∧
  0 < g.F*g.T ∧ 1 ≤ n₀ ∧ 1 ≤ bits ∧ g.a+g.b+bits ≤ n₀ ∧ 0 < U ∧
  U*n₀ < 2^(n₀-(g.a+g.b+bits)) ∧ g.F*g.T ≤ 2^bits ∧ 0 < p.R ∧
  0 < (p.R*2^bits)%(g.F*g.T) ∧
  gmin (bits-1) ((p.R*2^bits)/(g.F*g.T))+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤
    bits+g.a+g.b ∧
  -(U : ℤ) < primitiveBasisRivalA g p P Q-(g.F*g.T : ℕ)+min (primitiveBasisRivalJ g p r q) 0*g.W ∧
  -(U : ℤ) ≤ primitiveBasisRivalB g p ∧
  primitiveBasisRivalA g p P Q+max (primitiveBasisRivalJ g p r q) 0*g.W ≤ U ∧
  primitiveBasisRivalB g p ≤ U

instance (g : PrimitiveBasisGeometry) (bits U n₀ : ℕ) (P Q r q : ℤ)
    (p : PrimitiveBasisRivalPlan) : Decidable (PrimitiveBasisNonintegralCertificate g bits U n₀ P Q r q p) := by
  unfold PrimitiveBasisNonintegralCertificate
  infer_instance

/-- An integral boundary, positive error cone and reserved tail budget
are certified at one starting length. The upper error is at most `C`
denominators per position. -/
def PrimitiveBasisIntegralCertificate (g : PrimitiveBasisGeometry)
    (reserve C n₀ : ℕ) (P Q r q : ℤ) (p : PrimitiveBasisRivalPlan) : Prop :=
  PrimitiveBasisPlanRelation g P Q r q p ∧
  0 < g.F*g.T ∧ 1 ≤ n₀ ∧ 1 ≤ p.shift ∧ g.a+g.b+p.shift ≤ reserve ∧ reserve ≤ n₀ ∧
  0 < C ∧ C*n₀ < 2^(n₀-reserve) ∧ 1 ≤ p.boundary ∧
  (g.F*g.T)*p.boundary=2^p.shift*p.R ∧
  gmin (p.shift-1) p.boundary+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤ reserve ∧
  0 ≤ primitiveBasisRivalA g p P Q+min (primitiveBasisRivalJ g p r q) 0*g.W ∧
  0 ≤ primitiveBasisRivalB g p ∧
  0 < primitiveBasisRivalA g p P Q+min (primitiveBasisRivalJ g p r q) 0*g.W+primitiveBasisRivalB g p ∧
  primitiveBasisRivalA g p P Q+max (primitiveBasisRivalJ g p r q) 0*g.W ≤ (C*(g.F*g.T) : ℕ) ∧
  primitiveBasisRivalB g p ≤ (C*(g.F*g.T) : ℕ)

instance (g : PrimitiveBasisGeometry) (reserve C n₀ : ℕ) (P Q r q : ℤ)
    (p : PrimitiveBasisRivalPlan) : Decidable (PrimitiveBasisIntegralCertificate g reserve C n₀ P Q r q p) := by
  unfold PrimitiveBasisIntegralCertificate
  infer_instance

/-- The exact signed-basis error formula is independent of companion
lengths and the particular orientation of the primitive phases. -/
theorem primitive_basis_rival_error
    (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    {M E K H c V α z : ℕ} {P Q r q : ℤ}
    (hbase : H+c=V+1) (hM : M+E=g.w*K)
    (hap : (g.F*g.T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(g.t : ℤ)*c+r*M)
    (hzp : (g.T : ℤ)*z=Q*K+((g.T : ℤ)-Q)*H+((g.T : ℤ)-g.v)*c-g.T+q*M)
    (hR : (p.R : ℤ)=(g.F : ℤ)*p.tb*(Q+(g.w : ℤ)*q)-p.κ*(P+(g.w : ℤ)*r)-
      (g.F*g.T : ℕ)*p.ν*g.w) :
    (g.F*g.T : ℕ)*primitiveBasisRivalZ p α z V M-(p.R : ℤ)*K=
      primitiveBasisRivalA g p P Q*H+primitiveBasisRivalB g p*c-(g.F*g.T : ℕ)+
        primitiveBasisRivalJ g p r q*E := by
  have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hm : (M : ℤ)+E=(g.w : ℤ)*K := by exact_mod_cast hM
  dsimp [primitiveBasisRivalZ,primitiveBasisRivalA,primitiveBasisRivalB,primitiveBasisRivalJ]
  push_cast at hap hR ⊢
  linear_combination (g.F : ℤ)*p.tb*hzp-p.κ*hap-
    (g.F : ℤ)*g.T*(1-(p.tb : ℤ))*hb-
    ((g.F : ℤ)*g.T*p.ν-(g.F : ℤ)*p.tb*q+p.κ*r)*hm-hR*(K : ℤ)

/-- A nonintegral certificate yields an actual affordable group rival
at every length beyond its certified starting length. -/
theorem exists_rival_of_primitive_basis_nonintegral_certificate
    (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    {bits U n₀ n N L M E H c V α z : ℕ} {P Q r q : ℤ}
    (hn : n₀ ≤ n) (hL : L+g.a+g.b=n)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=g.w*2^L) (hE : E ≤ g.W*H)
    (hap : (g.F*g.T : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+(g.t : ℤ)*c+r*M)
    (hzp : (g.T : ℤ)*z=Q*(2 : ℤ)^L+((g.T : ℤ)-Q)*H+((g.T : ℤ)-g.v)*c-g.T+q*M)
    (x a b : ZMod N) (hα : α • x=g.D • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0)
    (hp : PrimitiveBasisNonintegralCertificate g bits U n₀ P Q r q p) :
    ∃ s, n ≤ s ∧ (p.ta ≠ 2^g.a-1 ∨ p.tb ≠ 2^g.b-1) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤ n ∧
      s • x+p.ta • a+p.tb • b=V • x := by
  rcases hp with ⟨⟨hta,hne,hR⟩,hS,hn₀,hbits,hreserved,hU,hsmall₀,hThi,hRpos,hrem,hcost,
    hA0,hB0,hA1,hB1⟩
  have herr := primitive_basis_rival_error g p hbase hM
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp) hR
  have hw := signed_rival_linear_error_window hH hnc hE hS (show (0 : ℤ) ≤ U by positivity)
    hA0 hB0 hA1 hB1
  have hwindow : (p.R : ℤ)*2^L < (g.F*g.T : ℕ)*primitiveBasisRivalZ p α z V M+(U*n : ℕ) ∧
      (g.F*g.T : ℕ)*primitiveBasisRivalZ p α z V M < (p.R : ℤ)*2^L+(U*n : ℕ) := by
    push_cast at herr hw ⊢
    constructor <;> linarith only [herr,hw.1,hw.2]
  have hsmall : U*n < 2^(L-bits) := by
    rw [show L-bits=n-(g.a+g.b+bits) by omega]
    exact linear_error_lt_two_pow_sub_of_base hn₀ hn hreserved hsmall₀
  have hlarge : n ≤ 2^(L-bits) := by
    have hh := Nat.mul_le_mul_right n hU
    omega
  have hbudget : gmin (bits-1) ((p.R*2^bits)/(g.F*g.T))+(L-bits)+
      (gmin (g.a-1) p.ta+gmin (g.b-1) p.tb) ≤ n := by omega
  obtain ⟨hZ,hnZ,_,u,hu,hcu⟩ := exists_rep_of_int_binary_prefix_fraction
    (n:=n) (L:=L) (w:=bits-1) (e:=L-bits) (primitiveBasisRivalZ p α z V M) (by omega)
    hS (by simpa only [Nat.sub_add_cancel hbits] using hThi) hRpos
    (by simpa only [Nat.sub_add_cancel hbits] using hrem)
    (by simpa only [Nat.sub_add_cancel hbits] using hbudget) hsmall hlarge hwindow
  refine ⟨_,hnZ,hne,u,hu,by omega,?_⟩
  exact signed_axis_basis_rival_eq x a b p.κ p.ν hta hz hα hmx hZ

/-- An integral certificate yields an actual sparse group rival at every
larger length, with no fixed companion lengths or fixed tail reserve. -/
theorem exists_rival_of_primitive_basis_integral_certificate
    (g : PrimitiveBasisGeometry) (p : PrimitiveBasisRivalPlan)
    {reserve C n₀ n N L M E H c V α z : ℕ} {P Q r q : ℤ}
    (hn : n₀ ≤ n) (hL : L+g.a+g.b=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=g.w*2^L) (hE : E ≤ g.W*H)
    (hap : (g.F*g.T : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+(g.t : ℤ)*c+r*M)
    (hzp : (g.T : ℤ)*z=Q*(2 : ℤ)^L+((g.T : ℤ)-Q)*H+((g.T : ℤ)-g.v)*c-g.T+q*M)
    (x a b : ZMod N) (hα : α • x=g.D • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0)
    (hp : PrimitiveBasisIntegralCertificate g reserve C n₀ P Q r q p) :
    ∃ s, n ≤ s ∧ (p.ta ≠ 2^g.a-1 ∨ p.tb ≠ 2^g.b-1) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin (g.a-1) p.ta+gmin (g.b-1) p.tb ≤ n ∧
      s • x+p.ta • a+p.tb • b=V • x := by
  rcases hp with ⟨⟨hta,hne,hR⟩,hS,hn₀,hshift,hreserved,hres,hC,hsmall₀,hbp,hb,hcost,
    hA0,hB0,hpos,hA1,hB1⟩
  have herr := primitive_basis_rival_error g p hbase hM
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp) hR
  have he : L-p.shift+(p.shift-1+1)=L := by omega
  have hpow : 2^L=2^p.shift*2^(L-p.shift) := by
    rw [← pow_add,show p.shift+(L-p.shift)=L by omega]
  have hboundaryeq : (g.F*g.T : ℕ)*(p.boundary*2^(L-p.shift) : ℕ)=(p.R : ℤ)*2^L := by
    have hh : (g.F*g.T)*(p.boundary*2^(L-p.shift))=p.R*2^L := by
      rw [← Nat.mul_assoc,hb,hpow]
      ring
    exact_mod_cast hh
  have htail : C*n < 2^(n-reserve) := linear_error_lt_two_pow_sub_of_base hn₀ hn hres hsmall₀
  have hboundary : n ≤ p.boundary*2^(L-p.shift) := by
    have hwide := Nat.pow_le_pow_right (by decide : 0 < 2) (show n-reserve ≤ L-p.shift by omega)
    have hh := Nat.mul_le_mul_right (2^(L-p.shift)) hbp
    have hh' := Nat.mul_le_mul_right n hC
    omega
  have hsmall : (C*(g.F*g.T))*n ≤ (g.F*g.T)*2^(n-reserve) := by
    have hh := Nat.mul_le_mul_left (g.F*g.T) (le_of_lt htail)
    nlinarith only [hh]
  have hcost' : gmin (p.shift-1) p.boundary+(n-reserve)+
      (gmin (g.a-1) p.ta+gmin (g.b-1) p.tb) ≤ n := by omega
  have herr' : (g.F*g.T : ℕ)*(primitiveBasisRivalZ p α z V M-(p.boundary*2^(L-p.shift) : ℕ))=
      primitiveBasisRivalA g p P Q*H+primitiveBasisRivalB g p*c-(g.F*g.T : ℕ)+
        primitiveBasisRivalJ g p r q*E := by
    push_cast at herr
    push_cast
    push_cast at hboundaryeq
    linear_combination herr-hboundaryeq
  obtain ⟨hZ,hnZ,u,hu,hcu⟩ := exists_rep_of_integral_rival_error_certificate
    (L:=L) (w:=p.shift-1) (e:=L-p.shift) (k:=n-reserve) (primitiveBasisRivalZ p α z V M)
    he (by omega) hS hboundary hcost' hsmall hH hc hnc hE hA0 hB0 hpos hA1 hB1 herr'
  refine ⟨_,hnZ,hne,u,hu,by omega,?_⟩
  exact signed_axis_basis_rival_eq x a b p.κ p.ν hta hz hα hmx hZ

end MinModulus
