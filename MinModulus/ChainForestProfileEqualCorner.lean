import MinModulus.ChainForestProfileTwoFive

/-! A uniform obstruction for equal-companion integral phases.
A saturated equal-height phase with denominator coprime to the height
forces that denominator to divide seven. Dyadic widths and heights leave
only companion lengths one and three. This classifies the arithmetic
corner; larger genuine-forest cases and the global conjecture remain open. -/

namespace MinModulus

/-- A saturated equal-height integral phase forces its odd denominator
to divide seven, provided that denominator is coprime to the height. -/
theorem equal_companion_integral_corner_denominator_dvd_seven
    {T K H E w z q : ℕ} (hT : 1 ≤ T) (hcop : Nat.Coprime T H)
    (hphase : T*z+q*E+T=(1+w*q)*K+(T-1)*(H+H))
    (hintegral : T ∣ 1+w*q) (hcorner : 4*E=w*H) : T ∣ 7 := by
  have hTz : (T : ZMod T)=0 := ZMod.natCast_self _
  have hlead : (1 : ZMod T)+(w : ZMod T)*q=0 := by
    have hh := (ZMod.natCast_eq_zero_iff (1+w*q) T).mpr hintegral
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] using hh
  have hp := congrArg (fun t : ℕ ↦ (t : ZMod T)) hphase
  have hc := congrArg (fun t : ℕ ↦ (t : ZMod T)) hcorner
  push_cast at hp hc
  rw [Nat.cast_sub hT,Nat.cast_one,hTz] at hp
  have h7 : (7 : ZMod T)*(H : ZMod T)=0 := by
    linear_combination 4*hp-(q : ZMod T)*hc-hlead*((H : ZMod T)-4*K)
  have hd : T ∣ 7*H := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h7
  exact hcop.dvd_of_dvd_mul_right hd

/-- With dyadic companion width and height, the saturated integral
corner can occur only at companion lengths one or three. -/
theorem equal_dyadic_companion_integral_corner_length_eq_one_or_three
    {a h K E w z q : ℕ} (ha : 1 ≤ a)
    (hphase : (2^a-1)*z+q*E+(2^a-1)=(1+w*q)*K+(2^a-2)*(2^h+2^h))
    (hintegral : 2^a-1 ∣ 1+w*q) (hcorner : 4*E=w*2^h) : a=1 ∨ a=3 := by
  have hpow : 2 ≤ 2^a := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ha
  have heven : Even (2^a) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : a ≠ 0))
  have hodd : Odd (2^a-1) := by
    rw [Nat.odd_iff]
    have hh := (Nat.even_iff.mp heven)
    omega
  have hcop : Nat.Coprime (2^a-1) (2^h) := hodd.coprime_two_right.pow_right h
  have hd : 2^a-1 ∣ 7 := equal_companion_integral_corner_denominator_dvd_seven
    (by omega) hcop (by simpa only [Nat.sub_sub,Nat.reduceAdd] using hphase) hintegral hcorner
  have hle := Nat.le_of_dvd (by decide : 0 < 7) hd
  have hale : a ≤ 3 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ a)
    norm_num at hp
    omega
  have hc : a=1 ∨ a=2 ∨ a=3 := by omega
  rcases hc with hh | hh | hh
  · exact Or.inl hh
  · rw [hh] at hd
    norm_num at hd
  · exact Or.inr hh

/-- Every equal dyadic companion length at least two other than three
excludes the saturated corner in an integral phase. -/
theorem equal_dyadic_companion_nonexceptional_integral_not_corner
    {a h K E w z q : ℕ} (ha : 2 ≤ a) (ha3 : a ≠ 3)
    (hphase : (2^a-1)*z+q*E+(2^a-1)=(1+w*q)*K+(2^a-2)*(2^h+2^h))
    (hintegral : 2^a-1 ∣ 1+w*q) : 4*E ≠ w*2^h := by
  intro hcorner
  have hh := equal_dyadic_companion_integral_corner_length_eq_one_or_three
    (by omega : 1 ≤ a) hphase hintegral hcorner
  omega

end MinModulus
