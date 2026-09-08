import MinModulus.ChainForestProfileBinaryPrefix

/-! Complementary rational prefixes have an exact combined greedy cost.
A uniform bound on the shared top multiple pays both companions and
ensures that one signed rival has an actual affordable representation.
No individual prefix-popcount budget is assumed. Constructing suitable
pairs uniformly, integral phases and the global conjecture remain open. -/

namespace MinModulus

/-- Complementary lower binary blocks have an exact combined greedy
cost, retaining arbitrary multiples of the top coin. -/
theorem gmin_pair_of_sum_add_one_eq_top_multiple
    (w p q m : ℕ) (hsum : p+q+1=m*2^w) :
    gmin w p+gmin w q+1=m+w := by
  induction w generalizing p q with
  | zero => simp only [gmin,pow_zero,mul_one,Nat.add_zero] at hsum ⊢; omega
  | succ w ih =>
    have hp : m*2^(w+1)=2*(m*2^w) := by rw [pow_succ]; ring
    rw [hp] at hsum
    have hpar : p%2+q%2=1 := by omega
    have hhalf : p/2+q/2+1=m*2^w := by omega
    have hh := ih (p/2) (q/2) hhalf
    simp only [gmin]
    omega

/-- A greedy cost is bounded by its top-coin quotient and the number
of lower binary positions. -/
theorem gmin_le_top_quotient_add_width (w z : ℕ) : gmin w z ≤ z/2^w+w := by
  induction w generalizing z with
  | zero => simp [gmin]
  | succ w ih =>
    have hh := ih (z/2)
    have hd : (z/2)/2^w=z/2^(w+1) := by rw [Nat.div_div_eq_div_mul,pow_succ'];
    simp only [gmin]
    rw [hd] at hh
    omega

/-- A bound on two targets' total value bounds their combined top
quotients; only the two lower binary blocks remain to pay for. -/
theorem gmin_pair_le_of_sum_le_top_multiple
    (w p q m : ℕ) (hsum : p+q ≤ m*2^w) :
    gmin w p+gmin w q ≤ m+2*w := by
  have hp := gmin_le_top_quotient_add_width w p
  have hq := gmin_le_top_quotient_add_width w q
  have hh := Nat.add_div_le_add_div p q (2^w)
  have hd : (p+q)/2^w ≤ m := by
    calc (p+q)/2^w ≤ (m*2^w)/2^w := Nat.div_le_div_right hsum
      _ = m := Nat.mul_div_cancel m (Nat.two_pow_pos w)
  omega

/-- Two companion weights whose sum is a multiple of the all-ones
weight have a uniform combined greedy-cost bound. -/
theorem gmin_pair_le_of_sum_eq_ones_multiple
    (a p q m : ℕ) (ha : 1 ≤ a) (hsum : p+q=m*(2^a-1)) :
    gmin (a-1) p+gmin (a-1) q ≤ 2*m+2*(a-1) := by
  apply gmin_pair_le_of_sum_le_top_multiple
  have hp : 2^a=2*2^(a-1) := by rw [← pow_succ']; congr 1; omega
  have hh := Nat.mul_le_mul_left m (Nat.sub_le (2^a) 1)
  rw [← hsum,hp] at hh
  nlinarith only [hh]

/-- One of two complementary prefixes pays for both companions and
its binary tail. A short explicit top-multiple bound replaces all
phase-specific prefix-popcount checks. -/
theorem one_complementary_prefix_fits_forest_budget
    {n e w a b m p q ta₁ ta₂ tb₁ tb₂ : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : e+(w+1)+a+b=n)
    (hpq : p+q+1=2*m*2^w)
    (hta : ta₁+ta₂=m*(2^a-1)) (htb : tb₁+tb₂=m*(2^b-1))
    (hsmall : 6*m ≤ w+7) :
    gmin w p+e+gmin (a-1) ta₁+gmin (b-1) tb₁ ≤ n ∨
      gmin w q+e+gmin (a-1) ta₂+gmin (b-1) tb₂ ≤ n := by
  have hp := gmin_pair_of_sum_add_one_eq_top_multiple w p q (2*m) hpq
  have hca := gmin_pair_le_of_sum_eq_ones_multiple a ta₁ ta₂ m ha hta
  have hcb := gmin_pair_le_of_sum_eq_ones_multiple b tb₁ tb₂ m hb htb
  omega

/-- Nonintegral complementary numerators have complementary
remainders, and their quotient sum misses the total quotient by one. -/
theorem quotient_pair_of_nonintegral_sum_eq_multiple
    {A B T m : ℕ} (hT : 0 < T) (hsum : A+B=m*T) (hrem : 0 < A%T) :
    0 < B%T ∧ A/T+B/T+1=m := by
  have hArem := Nat.mod_lt A hT
  have hBrem := Nat.mod_lt B hT
  have hAd := Nat.mod_add_div A T
  have hBd := Nat.mod_add_div B T
  have hquot : A/T < m := by
    have hh : (A/T)*T < m*T := by nlinarith only [hsum,hAd,hrem]
    exact Nat.lt_of_mul_lt_mul_right hh
  have hs : (m-A/T-1)+A/T+1=m := by omega
  have hbounds : (m-A/T-1)*T ≤ B ∧ B < ((m-A/T-1)+1)*T := by
    constructor <;> nlinarith only [hs,hsum,hAd,hArem,hrem]
  have hBq : B/T=m-A/T-1 := Nat.div_eq_of_lt_le hbounds.1 hbounds.2
  have hremainders : A%T+B%T=T := by
    rw [hBq] at hBd
    nlinarith only [hs,hsum,hAd,hBd]
  exact ⟨by omega,by omega⟩

/-- Complementary nonintegral rational windows produce an actual
representation for at least one of the two rival coefficients. The
uniform top-multiple bound supplies its prefix and companion budget. -/
theorem exists_one_complementary_rival_representation
    {n L e w a b m T R₁ R₂ Δ ta₁ ta₂ tb₁ tb₂ : ℕ} (Z₁ Z₂ : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hL : e+(w+1)=L) (hn : L+a+b=n)
    (hT : 0 < T) (hThi : T ≤ 2^(w+1)) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hRsum : R₁+R₂=m*T) (hrem : 0 < (R₁*2^(w+1))%T)
    (hta : ta₁+ta₂=m*(2^a-1)) (htb : tb₁+tb₂=m*(2^b-1))
    (hsmall : 6*m ≤ w+7) (herror : Δ < 2^e) (hnQ : n ≤ 2^e)
    (hw₁ : (R₁ : ℤ)*2^L < T*Z₁+Δ ∧ T*Z₁ < (R₁ : ℤ)*2^L+Δ)
    (hw₂ : (R₂ : ℤ)*2^L < T*Z₂+Δ ∧ T*Z₂ < (R₂ : ℤ)*2^L+Δ) :
    (0 ≤ Z₁ ∧ n ≤ Z₁.toNat ∧ ∃ u, val L u=Z₁.toNat ∧
      dsum L u+gmin (a-1) ta₁+gmin (b-1) tb₁ ≤ n) ∨
    (0 ≤ Z₂ ∧ n ≤ Z₂.toNat ∧ ∃ u, val L u=Z₂.toNat ∧
      dsum L u+gmin (a-1) ta₂+gmin (b-1) tb₂ ≤ n) := by
  have hsum : R₁*2^(w+1)+R₂*2^(w+1)=(2*m*2^w)*T := by
    calc R₁*2^(w+1)+R₂*2^(w+1)=(R₁+R₂)*2^(w+1) := by ring
      _ = (m*T)*2^(w+1) := by rw [hRsum]
      _ = (2*m*2^w)*T := by rw [pow_succ]; ring
  obtain ⟨hrem₂,hpair⟩ := quotient_pair_of_nonintegral_sum_eq_multiple hT hsum hrem
  have hbudget := one_complementary_prefix_fits_forest_budget (n := n) (e := e) ha hb (by omega) hpair hta htb hsmall
  rcases hbudget with hbudget | hbudget
  · obtain ⟨hpos,hnz,_,u,hu,hc⟩ := exists_rep_of_int_binary_prefix_fraction
      (C := gmin (a-1) ta₁+gmin (b-1) tb₁) Z₁ hL hT hThi hR₁ hrem
      (by omega) herror hnQ hw₁
    exact Or.inl ⟨hpos,hnz,u,hu,by omega⟩
  · obtain ⟨hpos,hnz,_,u,hu,hc⟩ := exists_rep_of_int_binary_prefix_fraction
      (C := gmin (a-1) ta₂+gmin (b-1) tb₂) Z₂ hL hT hThi hR₂ hrem₂
      (by omega) herror hnQ hw₂
    exact Or.inr ⟨hpos,hnz,u,hu,by omega⟩

end MinModulus
