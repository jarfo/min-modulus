import MinModulus.ChainForestProfileUnequalTerminal

/-! Uniform arithmetic for unequal companion rivals. Quotient and remainder
normalize primitive multipliers into affordable companion weights. Signed
unit phases have bounded leading numerators; actual profile reflections
preserve their target offset. Four rational blocks absorb the uniform
quadratic error whenever the leading phase is nonintegral. The genuine
forest consumer and the integral/nonunit residuals are separate obligations. -/

namespace MinModulus

/-- Adding any number of top-width coins has exactly that greedy cost. -/
theorem gmin_add_top_multiple (w m x : ℕ) :
    gmin w (x+m*2^w)=gmin w x+m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show x+(m+1)*2^w=(x+m*2^w)+2^w by ring,gmin_add_pow,ih]
    omega

/-- A rational first block pays for its bounded integer part and saves
one coin in its proper fractional block. -/
theorem rational_first_binary_block_general_coin_bound {S R B q : ℕ}
    (hS : 0 < S) (hSB : S < 2^B) (hR : R < q*S) (hB : 1 ≤ B) (hq : 1 ≤ q) :
    gmin (B-1) (R*2^B/S)+1 ≤ B+2*(q-1) := by
  have hd := rational_binary_block_lt_ones hS hSB (Nat.mod_lt R hS)
  have hc : gmin (B-1) ((R%S)*2^B/S) ≤ B-1 :=
    gmin_le_of_lt_binary_ones (by simpa only [Nat.sub_add_cancel hB] using hd)
  have hquot : R/S < q := (Nat.div_lt_iff_lt_mul hS).mpr hR
  let d := (R%S)*2^B/S
  change gmin (B-1) d ≤ B-1 at hc
  rw [mul_div_block_decomposition R (2^B) hS]
  change gmin (B-1) ((R/S)*2^B+d)+1 ≤ B+2*(q-1)
  have hp : 2^B=2*2^(B-1) := by rw [← pow_succ']; congr 1; omega
  rw [show (R/S)*2^B+d=d+(2*(R/S))*2^(B-1) by rw [hp]; ring,gmin_add_top_multiple]
  omega

/-- Every additional rational binary block saves another coin, uniformly
in the number of blocks and the bound on the leading integer part. -/
theorem rational_binary_blocks_general_coin_bound {S R B q k : ℕ}
    (hS : 0 < S) (hSB : S < 2^B) (hR : R < q*S) (hB : 1 ≤ B) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    gmin (k*B-1) (R*2^(k*B)/S)+k ≤ k*B+2*(q-1) := by
  induction k,hk using Nat.le_induction with
  | base => simpa only [one_mul] using rational_first_binary_block_general_coin_bound hS hSB hR hB hq
  | succ k hk ih =>
    have hkB : 1 ≤ k*B := by
      have hh := Nat.mul_le_mul hk hB
      simpa only [one_mul] using hh
    let d := ((R*2^(k*B))%S)*2^B/S
    have hd : d < 2^B-1 := rational_binary_block_lt_ones hS hSB (Nat.mod_lt (R*2^(k*B)) hS)
    have hc := gmin_binary_low_lt_ones hB hd
    have hdecomp : R*2^((k+1)*B)/S=(R*2^(k*B)/S)*2^B+d := by
      rw [Nat.add_mul,one_mul,pow_add,← Nat.mul_assoc]
      exact mul_div_block_decomposition (R*2^(k*B)) (2^B) hS
    have hg := gmin_binary_block B (k*B-1) (R*2^(k*B)/S) d (by omega)
    have hlen : B+(k*B-1)=(k+1)*B-1 := by rw [Nat.add_mul,one_mul]; omega
    rw [hlen] at hg
    rw [hdecomp,hg]
    rw [Nat.add_mul,one_mul]
    omega

/-- From dimension sixty-four onward, an eighth of the dimension's bits
already dominates twice its length. -/
theorem twice_length_lt_eighth_budget_pow {n : ℕ} (hn : 64 ≤ n) :
    2*n < 2^(n/8) := by
  have hp : ∀ k, 8 ≤ k → 16*k+14 < 2^k := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; nlinarith
  have hh := hp (n/8) (by omega)
  omega

/-- The actual unequal half-profile cost pays for four variable rational
blocks and a quadratic companion-width error at every remaining length. -/
theorem unequal_uniform_four_block_error_bound {a b f n : ℕ}
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hcost : 3*2^(a-1)+2^(b-1) ≤ n+1) :
    (128*2^f*(2^(b-1))^2)*n < 2^(n-(a+b+4*(b+f+1))) := by
  have hmargin : a+7*b+5*f+8+n/8 ≤ n := by
    by_cases hb : 9 ≤ b
    · have hp : ∀ k, 9 ≤ k → 16*k+1 ≤ 2^(k-1) := by
        intro k hk
        induction k,hk using Nat.le_induction with
        | base => norm_num
        | succ k hk ih =>
          have hh : 2^((k+1)-1)=2*2^(k-1) := by rw [← pow_succ']; congr 1; omega
          rw [hh]
          nlinarith
      have hh := hp b hb
      omega
    · have hb6 : 6 ≤ b := by omega
      interval_cases b <;> interval_cases a <;> norm_num at hcost <;> omega
  have hsmall := twice_length_lt_eighth_budget_pow (by omega : 64 ≤ n)
  have hU : 128*2^f*(2^(b-1))^2=2^(f+2*b+5) := by
    calc
      _ = 2^7*2^f*2^((b-1)*2) := by rw [pow_mul]; norm_num
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  calc
    _ = 2^(f+2*b+4)*(2*n) := by rw [hU,show f+2*b+5=(f+2*b+4)+1 by omega,pow_succ]; ring
    _ < 2^(f+2*b+4)*2^(n/8) := Nat.mul_lt_mul_of_pos_left hsmall (Nat.two_pow_pos _)
    _ = 2^(f+2*b+4+n/8) := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

def unequalNormalizedShortWeight (D C m : ℕ) : ℕ := D*m%C

def unequalNormalizedLongWeight (D C m : ℕ) : ℕ := D*m/C

/-- Quotient and remainder normalize every bounded primitive multiplier
into the original index lattice and bounded companion widths. -/
theorem unequal_normalized_companion_weight_bounds
    {D F s t u C T m : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (_hu : 2 ≤ u)
    (hC : C+1=4*s) (hT : T+u+1=4*t) (hmpos : 1 ≤ m) (hm : m < F*T) :
    unequalNormalizedShortWeight D C m < C ∧
    unequalNormalizedLongWeight D C m < t ∧
    unequalNormalizedShortWeight D C m+C*unequalNormalizedLongWeight D C m=D*m ∧
    0 < unequalNormalizedShortWeight D C m+unequalNormalizedLongWeight D C m := by
  have hCpos : 0 < C := by omega
  have hCT : s*T+s=C*t := by
    have hh := congrArg (fun z : ℕ ↦ s*z) hT
    have hc := congrArg (fun z : ℕ ↦ z*t) hC
    nlinarith only [hh,hc,htu]
  have hbound := Nat.mul_lt_mul_of_pos_left hm hD
  rw [← Nat.mul_assoc,hDF] at hbound
  have hlt : D*m < C*t := by omega
  have hdecomp : unequalNormalizedShortWeight D C m+C*unequalNormalizedLongWeight D C m=D*m :=
    Nat.mod_add_div (D*m) C
  have hprod : 0 < D*m := Nat.mul_pos hD (by omega)
  refine ⟨Nat.mod_lt _ hCpos,(Nat.div_lt_iff_lt_mul hCpos).mpr (by simpa only [Nat.mul_comm] using hlt),hdecomp,?_⟩
  by_contra hh
  have hzero : unequalNormalizedShortWeight D C m=0 ∧ unequalNormalizedLongWeight D C m=0 := by omega
  rw [hzero.1,hzero.2] at hdecomp
  omega

/-- The normalized signed index step has two small nonnegative
remainders; these control all leading numerator bounds. -/
theorem unequal_normalized_index_step_delta_bounds
    {D F s t u C m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s)
    (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb) :
    0 < (m : ℤ)-(F : ℤ)*tb ∧ (m : ℤ)-(F : ℤ)*tb < 3*(F : ℤ)*t ∧
    0 ≤ (m : ℤ)-3*(F : ℤ)*tb ∧ (m : ℤ)-3*(F : ℤ)*tb < 2*(F : ℤ)*t := by
  have hDZ : (0 : ℤ) < D := by exact_mod_cast hD
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hDFZ : (D : ℤ)*F=s := by exact_mod_cast hDF
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hdec : (ta : ℤ)+(C : ℤ)*tb=(D : ℤ)*m := by exact_mod_cast hdecomp
  have htaZ : (ta : ℤ) ≤ 4*(s : ℤ)-2 := by
    have hh : (ta : ℤ) < C := by exact_mod_cast hta
    omega
  have htbZ : (tb : ℤ)+1 ≤ t := by exact_mod_cast (show tb+1 ≤ t by omega)
  have htotZ : (0 : ℤ) < (ta : ℤ)+tb := by exact_mod_cast hpos
  have hta0 : (0 : ℤ) ≤ ta := by positivity
  have htb0 : (0 : ℤ) ≤ tb := by positivity
  have hts : 2*(s : ℤ) ≤ t := by
    have hh := Nat.mul_le_mul_left s hu
    exact_mod_cast (show 2*s ≤ t by nlinarith only [hh,htu])
  let δ1 : ℤ := (m : ℤ)-(F : ℤ)*tb
  let δ3 : ℤ := (m : ℤ)-3*(F : ℤ)*tb
  have hδ1 : (D : ℤ)*δ1+tb=ta+3*(s : ℤ)*tb := by
    dsimp [δ1]
    linear_combination -hdec+(tb : ℤ)*hCZ-(tb : ℤ)*hDFZ
  have hδ3 : (D : ℤ)*δ3+tb=ta+(s : ℤ)*tb := by
    dsimp [δ3]
    linear_combination -hdec+(tb : ℤ)*hCZ-3*(tb : ℤ)*hDFZ
  have hlow1 : 0 < δ1 := by
    apply (mul_lt_mul_iff_right₀ hDZ).mp
    have hh := mul_nonneg (show 0 ≤ 3*(s : ℤ)-2 by omega) htb0
    nlinarith only [hδ1,htotZ,hh]
  have hlow3 : 0 ≤ δ3 := by
    apply (mul_le_mul_iff_right₀ hDZ).mp
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-1 by omega) htb0
    nlinarith only [hδ3,hta0,hh]
  have hprod1 : (D : ℤ)*(3*(F : ℤ)*t)=3*(s : ℤ)*t := by
    linear_combination 3*(t : ℤ)*hDFZ
  have hprod3 : (D : ℤ)*(2*(F : ℤ)*t)=2*(s : ℤ)*t := by
    linear_combination 2*(t : ℤ)*hDFZ
  have hhi1 : δ1 < 3*(F : ℤ)*t := by
    apply (mul_lt_mul_iff_right₀ hDZ).mp
    rw [hprod1]
    have hh := mul_le_mul_of_nonneg_left htbZ (show 0 ≤ 3*(s : ℤ)-1 by omega)
    nlinarith only [hδ1,hh,htaZ,hts,hsZ]
  have hhi3 : δ3 < 2*(F : ℤ)*t := by
    apply (mul_lt_mul_iff_right₀ hDZ).mp
    rw [hprod3]
    have hh := mul_le_mul_of_nonneg_left htbZ (show 0 ≤ (s : ℤ)-1 by omega)
    have hh' := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ t by omega) (show (0 : ℤ) ≤ s by positivity)
    nlinarith only [hδ3,hh,hh',htaZ,hts]
  exact ⟨hlow1,hhi1,hlow3,hhi3⟩

/-- A normalized short weight avoids the all-ones endpoint above two
full short widths, saving one coin from the crude quotient bound. -/
theorem gmin_normalized_short_weight_bound {a s ta : ℕ}
    (ha : 1 ≤ a) (hs : s=2^(a-1)) (hta : ta < 4*s-1) :
    gmin (a-1) ta ≤ a+1 := by
  have hsp : 1 ≤ s := by rw [hs]; exact Nat.one_le_two_pow
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  by_cases hlow : ta < 2*s
  · have hh := gmin_le_of_lt_binary_width (w:=a-1) (t:=ta) (by
      rw [Nat.sub_add_cancel ha,hp]
      exact hlow)
    omega
  · have htail : ta-2*s < 2^a-1 := by rw [hp]; omega
    have hc : gmin (a-1) (ta-2*s) ≤ a-1 := gmin_le_of_lt_binary_ones (by
      simpa only [Nat.sub_add_cancel ha] using htail)
    have heq : ta=(ta-2*s)+s+s := by omega
    rw [heq,hs,gmin_add_pow,gmin_add_pow]
    rw [hs] at hc
    omega

/-- Both normalized companion weights fit their total length budget. -/
theorem unequal_normalized_companion_coin_bound {a b s t C ta tb : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hs : s=2^(a-1)) (ht : t=2^(b-1))
    (hC : C+1=4*s) (hta : ta < C) (htb : tb < t) :
    gmin (a-1) ta+gmin (b-1) tb ≤ a+b := by
  have hca := gmin_normalized_short_weight_bound ha hs (by omega : ta < 4*s-1)
  have htp : 1 ≤ t := by rw [ht]; exact Nat.one_le_two_pow
  have hp : 2^b=2*t := by rw [ht,← pow_succ']; congr 1; omega
  have hcb : gmin (b-1) tb ≤ b-1 := gmin_le_of_lt_binary_ones (by
    rw [Nat.sub_add_cancel hb,hp]
    omega)
  omega

/-- Normalization gives the exact signed index relation required by the
actual primitive basis, independently of the chosen phase. -/
theorem unequal_normalized_signed_index_relation {D F s C m ta tb : ℕ}
    (hDF : D*F=s) (hC : C+1=4*s) (hdecomp : ta+C*tb=D*m) :
    (ta : ℤ)=tb+(D : ℤ)*((m : ℤ)-4*(F : ℤ)*tb) := by
  have hd : (ta : ℤ)+(C : ℤ)*tb=(D : ℤ)*m := by exact_mod_cast hdecomp
  have hf : (D : ℤ)*F=s := by exact_mod_cast hDF
  have hc : (C : ℤ)+1=4*s := by exact_mod_cast hC
  linear_combination hd-(tb : ℤ)*hc+4*(tb : ℤ)*hf

/-- The quotient of the compatible phase link and the multiplier's phase
congruence give the exact signed period coefficient of the normalized plan. -/
theorem unequal_normalized_phase_relation
    {F T m tb r q p : ℕ} {l ε : ℤ}
    (hlink : T*p=4*r+q) (hm : (m : ℤ)*r=(F*T : ℕ)*l+ε) :
    (F : ℤ)*tb*q-((m : ℤ)-4*(F : ℤ)*tb)*r=
      (F*T : ℕ)*((tb : ℤ)*p-l)-ε := by
  have hh : (T : ℤ)*p=4*(r : ℤ)+q := by exact_mod_cast hlink
  push_cast at hm ⊢
  linear_combination -(F : ℤ)*tb*hh-hm

/-- The short normalized unit step has a positive leading numerator
below twice the full primitive denominator, uniformly in both widths. -/
theorem unequal_normalized_short_leading_bounds
    {D F s t u C T m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb) :
    0 < 4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb ∧
    4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb < 2*(F*T : ℕ) := by
  have hd := unequal_normalized_index_step_delta_bounds hD hs hDF htu hu hC hta htb hdecomp hpos
  have hFp : 0 < F := by nlinarith only [hDF,hs]
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
  have hDZ : (0 : ℤ) < D := by exact_mod_cast hD
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have hDFZ : (D : ℤ)*F=s := by exact_mod_cast hDF
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have htaZ : (ta : ℤ) ≤ 4*(s : ℤ)-2 := by
    have hh : (ta : ℤ) < C := by exact_mod_cast hta
    omega
  have htbZ : (tb : ℤ) < t := by exact_mod_cast htb
  have hdec : (ta : ℤ)+(C : ℤ)*tb=(D : ℤ)*m := by exact_mod_cast hdecomp
  have hFU : (0 : ℤ) < (F : ℤ)*u := by positivity
  have hFt : (F : ℤ)*t=(F : ℤ)*u*s := by linear_combination (F : ℤ)*htuZ
  have hST : (F : ℤ)*T+(F : ℤ)*u+F=4*(F : ℤ)*t := by linear_combination (F : ℤ)*hTZ
  have htu2 : (u : ℤ)+2 ≤ t := by
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have hupper : 7*(F : ℤ)*t-(F : ℤ)*u ≤ 2*(F : ℤ)*T := by
    have hh := mul_nonneg (le_of_lt hFZ) (show 0 ≤ (t : ℤ)-u-2 by omega)
    nlinarith only [hST,hh]
  constructor
  · have hh := mul_pos hFU (show 0 < 4*(s : ℤ)-ta by omega)
    nlinarith only [hd.1,hh,hFt]
  · have hh : 4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb < 7*(F : ℤ)*t-(F : ℤ)*u := by
      by_cases hzero : ta=0
      · have hδ : (D : ℤ)*((m : ℤ)-(F : ℤ)*tb)=(3*(s : ℤ)-1)*tb := by
          have hz : (ta : ℤ)=0 := by exact_mod_cast hzero
          linear_combination -hdec+(tb : ℤ)*hCZ-(tb : ℤ)*hDFZ+hz
        have heq : (D : ℤ)*(3*(F : ℤ)*t-(F : ℤ)*u)=(3*(s : ℤ)-1)*t := by
          linear_combination (3*(t : ℤ)-u)*hDFZ+htuZ
        have hδbound : (m : ℤ)-(F : ℤ)*tb < 3*(F : ℤ)*t-(F : ℤ)*u := by
          apply (mul_lt_mul_iff_right₀ hDZ).mp
          rw [hδ,heq]
          exact mul_lt_mul_of_pos_left htbZ (by omega)
        rw [hzero,Nat.cast_zero,mul_zero,sub_zero]
        linarith only [hδbound]
      · have htapos : (1 : ℤ) ≤ ta := by exact_mod_cast (show 1 ≤ ta by omega)
        have hmul := mul_le_mul_of_nonneg_left htapos (le_of_lt hFU)
        nlinarith only [hd.2.1,hmul]
    push_cast
    nlinarith only [hh,hupper]

/-- The long normalized unit step lies between minus two and two
primitive denominators. A nonpositive numerator has short weight below
its original top, allowing an actual top-profile reflection. -/
theorem unequal_normalized_long_leading_bounds
    {D F s t u C T m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb) :
    -2*(F*T : ℕ) < -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb ∧
    -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb < 2*(F*T : ℕ) ∧
    (-4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb ≤ 0 → ta < 2*s) := by
  have hd := unequal_normalized_index_step_delta_bounds hD hs hDF htu hu hC hta htb hdecomp hpos
  have hFp : 0 < F := by nlinarith only [hDF,hs]
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have htaZ : (ta : ℤ) ≤ 4*(s : ℤ)-2 := by
    have hh : (ta : ℤ) < C := by exact_mod_cast hta
    omega
  have hFU : (0 : ℤ) < (F : ℤ)*u := by positivity
  have hFt : (F : ℤ)*t=(F : ℤ)*u*s := by linear_combination (F : ℤ)*htuZ
  have hST : (F : ℤ)*T+(F : ℤ)*u+F=4*(F : ℤ)*t := by linear_combination (F : ℤ)*hTZ
  have htu2 : (u : ℤ)+2 ≤ t := by
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have hwide : 6*(F : ℤ)*t < 2*(F : ℤ)*T := by
    have hh := mul_pos hFZ (show 0 < (t : ℤ)-u-1 by omega)
    nlinarith only [hST,hh]
  have hta0 : (0 : ℤ) ≤ (F : ℤ)*u*ta := by positivity
  have hupper : -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb < 2*(F : ℤ)*T := by
    have hh := mul_le_mul_of_nonneg_left htaZ (show 0 ≤ 3*((F : ℤ)*u) by positivity)
    have hh' := mul_pos hFZ (show 0 < 2*(u : ℤ)-1 by omega)
    nlinarith only [hd.2.2.1,hh,hh',hFt,hST]
  refine ⟨?_,by push_cast; nlinarith only [hupper],?_⟩
  · push_cast
    nlinarith only [hd.2.2.2,hwide,hta0]
  · intro hneg
    have hh : (ta : ℤ) < 2*(s : ℤ) := by
      apply (mul_lt_mul_iff_right₀ hFU).mp
      nlinarith only [hneg,hd.2.2.2,hFt]
    exact_mod_cast hh

/-- A unit modulo the full primitive denominator supplies either signed
unit phase, with a multiplier strictly between zero and the denominator. -/
theorem exists_strict_signed_unit_multiplier {S r : ℕ} {ε : ℤ}
    (hS : 2 ≤ S) (hr : Nat.Coprime r S) (hε : ε=-1 ∨ ε=1) :
    ∃ m : ℕ, 1 ≤ m ∧ m < S ∧ ∃ l : ℤ, (m : ℤ)*r=(S : ℤ)*l+ε := by
  obtain ⟨k,hkpos,hk,j,hj⟩ := exists_strict_unit_index_step hS hr
  have hjZ : (k : ℤ)*r+1=(S : ℤ)*j := by exact_mod_cast hj
  rcases hε with rfl | rfl
  · exact ⟨k,hkpos,hk,j,by linarith only [hjZ]⟩
  · refine ⟨S-k,by omega,by omega,(r : ℤ)-j,?_⟩
    rw [Nat.cast_sub (by omega : k ≤ S)]
    linear_combination -hjZ

/-- The short leading numerator is the exact primitive-basis numerator
for the negative unit phase after normalization. -/
theorem unequal_normalized_short_leading_identity
    {D F s t u C m ta tb : ℕ} (_hD : 0 < D) (hDF : D*F=s)
    (htu : t=s*u) (hC : C+1=4*s) (hdecomp : ta+C*tb=D*m) :
    (F : ℤ)*tb*(3-(u : ℤ))-((m : ℤ)-4*(F : ℤ)*tb)*((t : ℤ)-1)+4*(F : ℤ)*t=
      4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb := by
  have hi := unequal_normalized_signed_index_relation hDF hC hdecomp
  have hf : (D : ℤ)*F=s := by exact_mod_cast hDF
  have ht : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hh : (F : ℤ)*u*(ta : ℤ)=(t : ℤ)*m+(F : ℤ)*u*tb-4*(F : ℤ)*t*tb := by
    linear_combination (F : ℤ)*u*hi+((m : ℤ)-4*(F : ℤ)*tb)*(u : ℤ)*hf-
      ((m : ℤ)-4*(F : ℤ)*tb)*ht
  linear_combination hh

/-- The long leading numerator is the exact primitive-basis numerator
for the positive unit phase after normalization. -/
theorem unequal_normalized_long_leading_identity
    {D F s t u C m ta tb : ℕ} (hD : 0 < D) (hDF : D*F=s)
    (htu : t=s*u) (hC : C+1=4*s) (hdecomp : ta+C*tb=D*m) :
    (F : ℤ)*tb*(3*(u : ℤ)-1)-((m : ℤ)-4*(F : ℤ)*tb)*(1-3*(t : ℤ))-4*(F : ℤ)*t=
      -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb := by
  have hh := unequal_normalized_short_leading_identity hD hDF htu hC hdecomp
  linear_combination -3*hh

/-- A normalized signed index step stays within four period half-widths. -/
theorem unequal_normalized_signed_index_bound {F T t m tb : ℕ}
    (hF : 0 < F) (hT : T < 4*t) (hm : m < F*T) (htb : tb < t) :
    |(m : ℤ)-4*(F : ℤ)*tb| ≤ 4*(F : ℤ)*t := by
  have hm' : (m : ℤ) < (F : ℤ)*T := by exact_mod_cast hm
  have ht' : (tb : ℤ) < t := by exact_mod_cast htb
  have hT' : (T : ℤ) < 4*(t : ℤ) := by exact_mod_cast hT
  have hF' : (0 : ℤ) < F := by exact_mod_cast hF
  have hh := mul_lt_mul_of_pos_left hT' hF'
  have hh' := mul_lt_mul_of_pos_left ht' (show 0 < 4*(F : ℤ) by positivity)
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hb0 : (0 : ℤ) ≤ (F : ℤ)*tb := by positivity
  rw [abs_le]
  constructor <;> nlinarith only [hm',hh,hh',hm0,hb0]

/-- A nonintegral unit phase stays nonintegral after any normalized
multiplier; the period-width term is essential in this condition. -/
theorem unequal_normalized_unit_phase_not_dvd
    {F T t m tb r : ℕ} {P Q κ R l ε : ℤ}
    (hε : ε=-1 ∨ ε=1) (hm : (m : ℤ)*r=(F*T : ℕ)*l+ε)
    (hκ : κ=(m : ℤ)-4*(F : ℤ)*tb)
    (hR : R=(F : ℤ)*tb*Q-κ*P-4*(F : ℤ)*t*ε)
    (hcancel : (T : ℤ) ∣ (F : ℤ)*tb*(Q+4*P))
    (hphase : ¬ (T : ℤ) ∣ P+4*(F : ℤ)*t*r) :
    ¬ (T : ℤ) ∣ R := by
  intro hd
  have hd' : (T : ℤ) ∣ (m : ℤ)*P+4*(F : ℤ)*t*ε := by
    have hh := dvd_sub hcancel hd
    have heq : (F : ℤ)*tb*(Q+4*P)-R=(m : ℤ)*P+4*(F : ℤ)*t*ε := by
      rw [hR,hκ]
      ring
    rwa [heq] at hh
  have hr := dvd_mul_of_dvd_right hd' (r : ℤ)
  have hbase : (T : ℤ) ∣ (F*T : ℕ)*l*P := by
    push_cast
    exact ⟨(F : ℤ)*l*P,by ring⟩
  have he : (T : ℤ) ∣ ε*(P+4*(F : ℤ)*t*r) := by
    have hh := dvd_sub hr hbase
    have heq : (r : ℤ)*((m : ℤ)*P+4*(F : ℤ)*t*ε)-(F*T : ℕ)*l*P=ε*(P+4*(F : ℤ)*t*r) := by
      push_cast at hm ⊢
      linear_combination P*hm
    rwa [heq] at hh
  apply hphase
  rcases hε with rfl | rfl
  · simpa only [neg_one_mul, dvd_neg] using he
  · simpa only [one_mul] using he

/-- Primitive-basis evaluation holds for the signed axis coefficient
before its nonnegativity is established. -/
theorem signed_axis_basis_rival_cast_eq
    {N M z α V D ta tb : ℕ} (x a b : ZMod N) (κ ν : ℤ)
    (hta : (ta : ℤ)=tb+(D : ℤ)*κ)
    (hz : z • x+a+b=V • x) (hα : α • x=D • a) (hM : M • x=0) :
    (((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M : ℤ) : ZMod N)*x+ta • a+tb • b=V • x := by
  have htaZ : (ta : ZMod N)=(tb : ZMod N)+(D : ZMod N)*(κ : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul] at hz hα hM ⊢
  push_cast
  rw [htaZ]
  linear_combination (tb : ZMod N)*hz-(κ : ZMod N)*hα-(ν : ZMod N)*hM

/-- Reflecting about any actual profile preserves the target and adds
its target offset to the new signed axis coefficient. -/
theorem signed_axis_rival_profile_reflection
    {N K V A B ta tb : ℕ} {Z : ℤ} (x a b : ZMod N)
    (hta : ta ≤ A) (htb : tb ≤ B)
    (hprofile : K • x+A • a+B • b=V • x)
    (hrival : (Z : ZMod N)*x+ta • a+tb • b=V • x) :
    (((K : ℤ)+V-Z : ℤ) : ZMod N)*x+(A-ta) • a+(B-tb) • b=V • x := by
  simp only [nsmul_eq_mul] at hprofile hrival ⊢
  rw [Nat.cast_sub hta,Nat.cast_sub htb]
  push_cast
  linear_combination hprofile-hrival

/-- The top reflection has leading numerator `S-R`; both reflected
height coefficients retain the same constant minus the denominator. -/
theorem signed_axis_rival_top_error_reflection
    {S K H c V E : ℕ} {Z R A B J : ℤ} (hbase : H+c=V+1)
    (herr : (S : ℤ)*Z-R*K=A*H+B*c-S+J*E) :
    (S : ℤ)*((K : ℤ)-1+V-Z)-((S : ℤ)-R)*K=
      ((S : ℤ)-A)*H+((S : ℤ)-B)*c-S-J*E := by
  have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  linear_combination -herr-(S : ℤ)*hb

/-- The actual half-profile reflection negates the leading numerator
and has two denominators in its reflected height coefficient. -/
theorem signed_axis_rival_half_error_reflection
    {S K H c V E : ℕ} {Z R A B J : ℤ} (hbase : H+c=V+1)
    (herr : (S : ℤ)*Z-R*K=A*H+B*c-S+J*E) :
    (S : ℤ)*((H : ℤ)-1+V-Z)-(-R)*K=
      (2*(S : ℤ)-A)*H+((S : ℤ)-B)*c-S-J*E := by
  have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  linear_combination -herr-(S : ℤ)*hb

/-- The normalized basis coefficients have a uniform quadratic bound
in the long companion half-width. -/
theorem unequal_normalized_error_coefficient_bounds
    {F T t v tb : ℕ} {κ P Q : ℤ}
    (ht : 1 ≤ t) (hT : T ≤ 4*t) (hv : v ≤ 2*t) (htb : tb ≤ t)
    (hκ : |κ| ≤ 4*(F : ℤ)*t) (hP : |P| ≤ 3*(t : ℤ)) (hQ : |Q| ≤ 3*(t : ℤ)) :
    |(F*T : ℕ)-(F : ℤ)*tb*Q+κ*P| ≤ 32*(F : ℤ)*t^2 ∧
    |(F*T : ℕ)-(F : ℤ)*tb*v-κ*t| ≤ 32*(F : ℤ)*t^2 := by
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hTz : (T : ℤ) ≤ 4*(t : ℤ) := by exact_mod_cast hT
  have hvz : (v : ℤ) ≤ 2*(t : ℤ) := by exact_mod_cast hv
  have htbz : (tb : ℤ) ≤ t := by exact_mod_cast htb
  have hF0 : (0 : ℤ) ≤ F := by positivity
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hFt : (F : ℤ)*t ≤ (F : ℤ)*t^2 := by
    have hh := mul_nonneg (show 0 ≤ (t : ℤ)-1 by omega) ht0
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hh]) hF0
  have hS : |((F*T : ℕ) : ℤ)| ≤ 4*(F : ℤ)*t^2 := by
    rw [abs_of_nonneg (by positivity)]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hTz hF0
    nlinarith only [hh,hFt]
  have hAQ : |(F : ℤ)*tb*Q| ≤ 3*(F : ℤ)*t^2 := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ) ≤ (F : ℤ)*tb)]
    have hh := mul_le_mul_of_nonneg_left hQ (show (0 : ℤ) ≤ (F : ℤ)*tb by positivity)
    have hh' := mul_le_mul_of_nonneg_left htbz (show (0 : ℤ) ≤ 3*(F : ℤ)*t by positivity)
    nlinarith only [hh,hh']
  have hkP : |κ*P| ≤ 12*(F : ℤ)*t^2 := by
    rw [abs_mul]
    have hh := mul_le_mul hκ hP (abs_nonneg P) (show (0 : ℤ) ≤ 4*(F : ℤ)*t by positivity)
    nlinarith only [hh]
  have hBv : |(F : ℤ)*tb*v| ≤ 2*(F : ℤ)*t^2 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul htbz hvz (show (0 : ℤ) ≤ v by positivity) ht0
    have hh' := mul_le_mul_of_nonneg_left hh hF0
    nlinarith only [hh']
  have hkt : |κ*(t : ℤ)| ≤ 4*(F : ℤ)*t^2 := by
    rw [abs_mul,abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_right hκ ht0
    nlinarith only [hh]
  constructor
  · have hh := abs_add_le ((F*T : ℕ)-(F : ℤ)*tb*Q) (κ*P)
    have hh' := abs_sub ((F*T : ℕ) : ℤ) ((F : ℤ)*tb*Q)
    have hpos : (0 : ℤ) ≤ (F : ℤ)*t^2 := by positivity
    linarith only [hS,hAQ,hkP,hh,hh',hpos]
  · have hh := abs_sub ((F*T : ℕ)-(F : ℤ)*tb*v) (κ*(t : ℤ))
    have hh' := abs_sub ((F*T : ℕ) : ℤ) ((F : ℤ)*tb*v)
    have hpos : (0 : ℤ) ≤ (F : ℤ)*t^2 := by positivity
    linarith only [hS,hBv,hkt,hh,hh',hpos]

/-- Reflecting either coefficient about one or two primitive denominators
still leaves a uniform quadratic bound. -/
theorem unequal_reflected_error_coefficient_bound
    {F T t : ℕ} {A : ℤ} (ht : 1 ≤ t) (hT : T ≤ 4*t)
    (hA : |A| ≤ 32*(F : ℤ)*t^2) :
    |(F*T : ℕ)-A| ≤ 64*(F : ℤ)*t^2 ∧
    |2*(F*T : ℕ)-A| ≤ 64*(F : ℤ)*t^2 := by
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hTz : (T : ℤ) ≤ 4*(t : ℤ) := by exact_mod_cast hT
  have hFt : (F : ℤ)*t ≤ (F : ℤ)*t^2 := by
    have hh := mul_nonneg (show 0 ≤ (t : ℤ)-1 by omega) (show (0 : ℤ) ≤ t by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hh]) (by positivity)
  have hS : |((F*T : ℕ) : ℤ)| ≤ 4*(F : ℤ)*t^2 := by
    rw [abs_of_nonneg (by positivity)]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hTz (show (0 : ℤ) ≤ F by positivity)
    nlinarith only [hh,hFt]
  have hS2 : |2*((F*T : ℕ) : ℤ)| ≤ 8*(F : ℤ)*t^2 := by
    calc
      _ = 2*|((F*T : ℕ) : ℤ)| := by rw [abs_mul]; norm_num
      _ ≤ 2*(4*(F : ℤ)*t^2) := mul_le_mul_of_nonneg_left hS (by decide : (0 : ℤ) ≤ 2)
      _ = _ := by ring
  have hh := abs_sub ((F*T : ℕ) : ℤ) A
  have hh' := abs_sub (2*((F*T : ℕ) : ℤ)) A
  have hp : (0 : ℤ) ≤ (F : ℤ)*t^2 := by positivity
  constructor <;> linarith only [hA,hS,hS2,hh,hh',hp]

/-- Any direct or reflected normalized unit rival has an error window
small enough for four rational binary blocks. -/
theorem unequal_uniform_signed_error_window
    {F T t n H c E : ℕ} {A B J : ℤ}
    (hF : 0 < F) (hTpos : 0 < T) (ht : 1 ≤ t) (hT : T ≤ 4*t)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hE : E ≤ F*t*H)
    (hA : |A| ≤ 64*(F : ℤ)*t^2) (hB : |B| ≤ 64*(F : ℤ)*t^2)
    (hJ : J=-1 ∨ J=0 ∨ J=1) :
    -((128*F*t^2)*n : ℕ) < A*H+B*c-(F*T : ℕ)+J*E ∧
    A*H+B*c-(F*T : ℕ)+J*E < ((128*F*t^2)*n : ℕ) := by
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hF
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hTZ : (T : ℤ) ≤ 4*(t : ℤ) := by exact_mod_cast hT
  have hFt : (F : ℤ)*t ≤ (F : ℤ)*t^2 := by
    have hh := mul_nonneg (show 0 ≤ (t : ℤ)-1 by omega) (show (0 : ℤ) ≤ t by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hh]) (by positivity)
  have hS : (F*T : ℕ) ≤ 4*(F : ℤ)*t^2 := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hTZ (le_of_lt hFZ)
    nlinarith only [hh,hFt]
  have hW : (F*t : ℕ) ≤ (F : ℤ)*t^2 := by exact_mod_cast hFt
  push_cast at hS hW
  have hN : (0 : ℤ) < (F : ℤ)*t^2 := by positivity
  rcases abs_le.mp hA with ⟨hA0,hA1⟩
  rcases abs_le.mp hB with ⟨hB0,hB1⟩
  have hw := signed_rival_linear_error_window (S:=F*T) (W:=F*t)
    (C:=128*(F : ℤ)*t^2) (A:=A) (B:=B) (J:=J) hH hnc hE (by positivity) (by positivity)
    (by rcases hJ with rfl | rfl | rfl <;> norm_num <;> linarith only [hA0,hS,hW,hN])
    (by linarith only [hB0,hN])
    (by rcases hJ with rfl | rfl | rfl <;> norm_num <;> linarith only [hA1,hW,hN])
    (by linarith only [hB1,hN])
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,neg_mul] using hw

/-- A nonintegral numerator below three denominators has an affordable
axis representation throughout the remaining unequal length range. -/
theorem exists_rep_of_unequal_uniform_nonintegral_window
    {a b f n L F T t R ta tb : ℕ} (Z : ℤ)
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hL : L+a+b=n) (hF : F=2^f) (ht : t=2^(b-1))
    (hcost : 3*2^(a-1)+t ≤ n+1) (hT : T < 4*t) (hTodd : Odd T)
    (hR : 0 < R) (hRhi : R < 3*(F*T)) (hnonint : ¬ T ∣ R)
    (hcomp : gmin (a-1) ta+gmin (b-1) tb ≤ a+b)
    (hwindow : (R : ℤ)*2^L < (F*T : ℕ)*Z+((128*F*t^2)*n : ℕ) ∧
      (F*T : ℕ)*Z < (R : ℤ)*2^L+((128*F*t^2)*n : ℕ)) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ k,
      val L k=Z.toNat ∧ dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n := by
  let B := b+f+1
  let bits := 4*B
  let U := 128*F*t^2
  have hb : 1 ≤ b := by omega
  have htp : 0 < t := by rw [ht]; positivity
  have hFp : 0 < F := by rw [hF]; positivity
  have hTp : 0 < T := by obtain ⟨j,hj⟩ := hTodd; omega
  have hS : 0 < F*T := by positivity
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU : 1 ≤ U := by omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hbits : 1 ≤ bits := by dsimp [bits]; omega
  have hsmall : U*n < 2^(n-(a+b+bits)) := by
    dsimp [U,bits,B]
    rw [hF,ht]
    exact unequal_uniform_four_block_error_bound ha hab hsum hf hn (by simpa only [ht] using hcost)
  have hreserved : a+b+bits ≤ n := by
    by_contra hh
    have he : n-(a+b+bits)=0 := by omega
    rw [he,pow_zero] at hsmall
    have hm := Nat.mul_le_mul_right n hU
    omega
  have hSB : F*T < 2^B := by
    have hp : 4*t=2^(b+1) := by
      rw [ht,show b+1=2+(b-1) by omega,pow_add]
      norm_num
    calc
      F*T < F*(4*t) := Nat.mul_lt_mul_of_pos_left hT hFp
      _ = _ := by rw [hp,hF,← pow_add]; dsimp [B]; congr 1; omega
  have hThi : F*T ≤ 2^bits := by
    apply le_trans (Nat.le_of_lt hSB)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [bits]; omega)
  have hprefix : gmin (bits-1) (R*2^bits/(F*T)) ≤ bits := by
    have hh := rational_binary_blocks_general_coin_bound hS hSB hRhi hB (by decide : 1 ≤ 3) (by decide : 1 ≤ 4)
    dsimp [bits]
    omega
  have hrem : 0 < (R*2^bits)%(F*T) := by
    by_contra hh
    have hd : F*T ∣ R*2^bits := Nat.dvd_of_mod_eq_zero (by omega)
    have ht' : T ∣ 2^bits*R := by
      simpa only [Nat.mul_comm] using dvd_trans (dvd_mul_left T F) hd
    exact hnonint ((hTodd.coprime_two_right.pow_right bits).dvd_of_dvd_mul_left ht')
  have hsmall' : U*n < 2^(L-bits) := by
    rw [show L-bits=n-(a+b+bits) by omega]
    exact hsmall
  have hlarge : n ≤ 2^(L-bits) := by
    have hh := Nat.mul_le_mul_right n hU
    omega
  have hbudget : gmin (bits-1) (R*2^bits/(F*T))+(L-bits)+
      (gmin (a-1) ta+gmin (b-1) tb) ≤ n := by omega
  obtain ⟨hZ,hnZ,_,k,hk,hck⟩ := exists_rep_of_int_binary_prefix_fraction
    (n:=n) (L:=L) (w:=bits-1) (e:=L-bits) Z (by omega) hS
    (by simpa only [Nat.sub_add_cancel hbits] using hThi) hR
    (by simpa only [Nat.sub_add_cancel hbits] using hrem)
    (by simpa only [Nat.sub_add_cancel hbits] using hbudget) hsmall' hlarge hwindow
  exact ⟨hZ,hnZ,k,hk,by omega⟩

end MinModulus
