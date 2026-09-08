import MinModulus.ChainForestProfileUnequalRival

/-! Binary-prefix representations with arbitrary prefix and tail
lengths, phase denominators, error allowances and companion budgets.
Natural and signed windows produce exact prefixes and actual affordable
representations. The uniform signed-rival coefficient certificate feeds
directly into the representation theorem. Choosing affordable coins for
all larger primitive phases and the unrestricted conjecture remain open. -/

namespace MinModulus

/-- A rational window fixes an arbitrary binary prefix and gives an
actual representation. The tail length, error, companion budget and
phase denominator are all parameters. -/
theorem exists_rep_near_binary_prefix_fraction
    {n L w e T R z C Δ : ℕ} (hL : e+(w+1)=L)
    (hT : 0 < T) (hThi : T ≤ 2^(w+1)) (hR : 0 < R)
    (hrem : 0 < (R*2^(w+1))%T)
    (hcost : gmin w ((R*2^(w+1))/T)+e+C ≤ n)
    (hsmall : Δ < 2^e) (hnQ : n ≤ 2^e)
    (hwindow : R*2^L < T*z+Δ ∧ T*z < R*2^L+Δ) :
    n ≤ z ∧ z/2^e=(R*2^(w+1))/T ∧
      ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let Q := 2^e
  let p := (R*2^(w+1))/T
  let r := (R*2^(w+1))%T
  have hQ : Δ < Q := hsmall
  have hK : 2^L=2^(w+1)*Q := by rw [← hL,pow_add]; exact Nat.mul_comm _ _
  have hrp : 1 ≤ r := hrem
  have hrhi : r+1 ≤ T := by
    have := Nat.mod_lt (R*2^(w+1)) hT
    dsimp [r]
    omega
  have hdecomp : R*2^(w+1)=T*p+r := by
    have hh := Nat.mod_add_div (R*2^(w+1)) T
    dsimp [p,r]
    omega
  have hKR : R*2^L=T*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q+Q ≤ T*Q := by
    have hh := Nat.mul_le_mul_right Q hrhi
    simpa only [add_mul,one_mul] using hh
  have hpref : p*Q ≤ z ∧ z < (p+1)*Q := by
    constructor
    · have hh : T*(p*Q) ≤ T*z := by omega
      by_contra hlo
      have hlt := Nat.mul_lt_mul_of_pos_left (by omega : z < p*Q) hT
      omega
    · have hh : T*z < T*((p+1)*Q) := by nlinarith only [hwindow.2,hKR,hremhi,hQ]
      exact Nat.lt_of_mul_lt_mul_left hh
  have hpref' : z/Q=p := Nat.div_eq_of_lt_le hpref.1 hpref.2
  have hp : 1 ≤ p := by
    dsimp [p]
    apply Nat.div_pos
    · have hh := Nat.mul_le_mul_right (2^(w+1)) (show 1 ≤ R by omega)
      omega
    · exact hT
  have hpQ := Nat.mul_le_mul_right Q hp
  have hnz : n ≤ z := by change n ≤ Q at hnQ; omega
  have hzrem : z%Q < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
  obtain ⟨u,hu,hc⟩ := exists_rep_binary_block_tail w e p (z%Q) hzrem
  refine ⟨hnz,hpref',u,?_,?_⟩
  · rw [hL] at hu
    have hh := Nat.mod_add_div z Q
    rw [hpref'] at hh
    have hz : p*2^e+z%Q=z := by
      dsimp [Q] at hh
      simpa only [Nat.mul_comm,Nat.add_comm] using hh
    exact hu.trans hz
  · rw [hL] at hc
    change gmin w p+e+C ≤ n at hcost
    omega

/-- The general signed rational window gives a nonnegative coefficient,
an exact binary prefix and an actual representation within the budget. -/
theorem exists_rep_of_int_binary_prefix_fraction
    {n L w e T R C Δ : ℕ} (Z : ℤ) (hL : e+(w+1)=L)
    (hT : 0 < T) (hThi : T ≤ 2^(w+1)) (hR : 0 < R)
    (hrem : 0 < (R*2^(w+1))%T)
    (hcost : gmin w ((R*2^(w+1))/T)+e+C ≤ n)
    (hsmall : Δ < 2^e) (hnQ : n ≤ 2^e)
    (hwindow : (R : ℤ)*2^L < T*Z+Δ ∧ T*Z < (R : ℤ)*2^L+Δ) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ Z.toNat/2^e=(R*2^(w+1))/T ∧
      ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmallK : Δ < 2^L :=
    lt_of_lt_of_le hsmall (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : e ≤ L))
  have hsmallZ : (Δ : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmallK
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hTZ : 0 < (T : ℤ) := by exact_mod_cast hT
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < T*Z.toNat+Δ ∧ T*Z.toNat < R*2^L+Δ := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < (T : ℤ)*(Z.toNat : ℤ)+Δ ∧
      (T : ℤ)*(Z.toNat : ℤ) < (R : ℤ)*2^L+Δ by simpa only [hcast] using hwindow)
  obtain ⟨hz,hprefix,u,hu,hc⟩ := exists_rep_near_binary_prefix_fraction hL hT hThi hR hrem hcost
    hsmall hnQ hwindowNat
  exact ⟨hZ,hz,hprefix,u,hu,hc⟩

/-- A uniform signed-rival error certificate and an affordable
binary prefix produce the actual dominant-chain representation. -/
theorem exists_rep_of_signed_rival_error_certificate
    {n L w e T R C U H c E W : ℕ} {A B J : ℤ} (Z : ℤ)
    (hL : e+(w+1)=L) (hT : 0 < T) (hThi : T ≤ 2^(w+1)) (hR : 0 < R)
    (hrem : 0 < (R*2^(w+1))%T)
    (hcost : gmin w ((R*2^(w+1))/T)+e+C ≤ n)
    (hsmall : U*n < 2^e) (hnQ : n ≤ 2^e)
    (hH : 1 ≤ H) (hn : H+c ≤ n) (hE : E ≤ W*H)
    (hloA : -(U : ℤ) < A-T+min J 0*W) (hloB : -(U : ℤ) ≤ B)
    (hhiA : A+max J 0*W ≤ U) (hhiB : B ≤ U)
    (herror : (T : ℤ)*Z-(R : ℤ)*2^L=A*H+B*c-T+J*E) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ Z.toNat/2^e=(R*2^(w+1))/T ∧
      ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hw := signed_rival_linear_error_window hH hn hE hT (Nat.cast_nonneg U)
    hloA hloB hhiA hhiB
  rw [← herror] at hw
  have hwindow : (R : ℤ)*2^L < (T : ℤ)*Z+(U*n : ℕ) ∧
      (T : ℤ)*Z < (R : ℤ)*2^L+(U*n : ℕ) := by
    push_cast
    constructor <;> linarith [hw.1,hw.2]
  exact exists_rep_of_int_binary_prefix_fraction Z hL hT hThi hR hrem hcost hsmall hnQ hwindow

end MinModulus
