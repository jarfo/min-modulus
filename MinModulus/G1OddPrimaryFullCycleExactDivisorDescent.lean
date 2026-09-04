/-
# Exact-divisor descent below the sixth stratum

The bounded five-weight relation gives an exact quotient divisor

  `2^t * (q / addOrderOf y) | 2 * |e|`.

For every positive two-adic level, cancel the common factor two rather than
discarding the divisor information in favor of an inequality.  Oddness of
the odd-primary factor then passes to the quotient.  At the fifth stratum the
uniform bound `|e| <= 42` leaves only full odd order and coefficient magnitude
`16` or `32`.
-/
import MinModulus.G1OddPrimaryFullCycleRowPartition

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Exact positive-stratum form of bounded confinement.  The common factor
two in the quotient divisor and `2*|e|` is cancelled, and the remaining
odd-primary quotient is recorded as odd.  This is the reusable arithmetic
interface for the lower strata; it retains strictly more information than
the earlier bound `2^t <= 2*|e|`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_lowerStratum_exactFactor_dvd_natAbs
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t) (hq : Odd q)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      (Odd (q / addOrderOf y) ∧
        2 ^ (t - 1) * (q / addOrderOf y) ∣ e.natAbs) := by
  rcases hrows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_dvd
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    refine ⟨odd_oddFactorQuotient hq hyq, ?_⟩
    have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
      calc
        2 ^ t = 2 ^ (t - 1 + 1) := by congr 1; omega
        _ = 2 ^ (t - 1) * 2 := pow_succ 2 (t - 1)
        _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
    have htwice :
        2 * (2 ^ (t - 1) * (q / addOrderOf y)) ∣
          2 * e.natAbs := by
      simpa only [hpow, Nat.mul_assoc] using hfactor
    exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp htwice

/-- Fifth-stratum exact-divisor rigidity.  Unless confinement produces a
strictly smaller valid cyclic modulus, the cyclic kernel has the full odd
factor and the bounded coefficient has magnitude exactly `16` or `32`.
This statement is uniform in the tuple dimension and the odd modulus; no
finite modulus enumeration is used. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_fifthStratum_exactDivisor_rigidity
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ 5 * q ∧ M ∣ 2 ^ 5 * q ∧
        AdmitsValidTuple n M) ∨
      (q / addOrderOf y = 1 ∧
        (e.natAbs = 16 ∨ e.natAbs = 32)) := by
  rcases hrows.exists_smallerValidCyclicModulus_or_lowerStratum_exactFactor_dvd_natAbs
      (t := 5) (q := q) (by omega) hq g hg hunique hne y hyq B
        x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | ⟨hquotOdd, hfactor⟩
  · exact Or.inl hsmaller
  · right
    have habsPos : 0 < e.natAbs := Int.natAbs_pos.mpr he
    have habsLe : e.natAbs ≤ 42 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
    have hquotPos : 0 < q / addOrderOf y := by
      rcases hquotOdd with ⟨k, hk⟩
      omega
    have hfactorLe :
        16 * (q / addOrderOf y) ≤ e.natAbs := by
      norm_num at hfactor
      exact Nat.le_of_dvd habsPos hfactor
    have hquotLe : q / addOrderOf y ≤ 2 := by omega
    have hquotOne : q / addOrderOf y = 1 := by
      rcases hquotOdd with ⟨k, hk⟩
      omega
    refine ⟨hquotOne, ?_⟩
    rw [hquotOne] at hfactor
    norm_num at hfactor
    obtain ⟨k, hk⟩ := hfactor
    omega

/-- Minimal-counterexample projection of fifth-stratum rigidity. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_sixteen_or_thirtyTwo_of_fifthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    q / addOrderOf y = 1 ∧
      (e.natAbs = 16 ∨ e.natAbs = 32) := by
  rcases hrows.exists_smallerValidCyclicModulus_or_fifthStratum_exactDivisor_rigidity
      hq g hg hunique hne y hyq B x z hxB hzB hxz hcomplement
        e he helow hehigh heMem with
    ⟨M, hMpos, hMlt, hMdiv, hvalid⟩ | hrigid
  · exact (hminimal M hMpos hMlt hMdiv hvalid).elim
  · exact hrigid

/-- Uniform positive-stratum quotient-order split.  When the odd kernel has
full odd-primary order, minimality forces the retained difference to generate
either the unique index-two subgroup or the whole quotient of order `2^t`.
This is the reusable quotient phase for the descent through `t ≤ 5`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.retainedDifference_quotientOrder_eq_half_or_full_of_positiveStratum_minimal
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g x - g z)) = 2 ^ (t - 1) ∨
      addOrderOf (pi (g x - g z)) = 2 ^ t := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ t * q) := g x - g z
  let deltaQ : Q := pi delta
  let eNat : ℕ := addOrderOf deltaQ
  let e : ℤ := eNat
  have hquotientModulus : (2 ^ t * q) / addOrderOf y = 2 ^ t := by
    rw [Nat.mul_div_assoc (2 ^ t) hyq, hfullOdd]
    simp
  letI : Fintype Q := Fintype.ofFinite Q
  have hQcardNat : Nat.card Q = 2 ^ t := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ t * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ t * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hQcard : Fintype.card Q = 2 ^ t := by
    simpa only [Nat.card_eq_fintype_card] using hQcardNat
  have hePos : 0 < eNat := addOrderOf_pos deltaQ
  have he : e ≠ 0 := by
    change (eNat : ℤ) ≠ 0
    omega
  have heMem : e • delta ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff (e • delta)).mp
    change pi (e • delta) = 0
    rw [map_zsmul]
    change (eNat : ℤ) • deltaQ = 0
    simpa only [natCast_zsmul] using addOrderOf_nsmul_eq_zero deltaQ
  have hfactor : (2 ^ t * q) / addOrderOf y ∣ 2 * e.natAbs := by
    rcases hrows.exists_smallerValidCyclicModulus_or_quotientFactor_dvd
        g hg hunique hne y B x z hxB hzB hxz hcomplement e he heMem with
      ⟨M, hMpos, hMlt, hMdiv, hvalid⟩ | hfactor
    · exact (hminimal M hMpos hMlt hMdiv hvalid).elim
    · exact hfactor
  have hfactorPow : 2 ^ t ∣ 2 * eNat := by
    rw [hquotientModulus] at hfactor
    simpa [e] using hfactor
  have heDvdPow : eNat ∣ 2 ^ t := by
    rw [← hQcard]
    exact addOrderOf_dvd_card (x := deltaQ)
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := pow_succ 2 (t - 1)
      _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
  have hhalfDvd : 2 ^ (t - 1) ∣ eNat := by
    obtain ⟨k, hk⟩ := hfactorPow
    have hkCancel : 2 * eNat = 2 * (2 ^ (t - 1) * k) := by
      simpa only [hpow, Nat.mul_assoc] using hk
    exact ⟨k, Nat.eq_of_mul_eq_mul_left (by omega) hkCancel⟩
  have heLe : eNat ≤ 2 ^ t := Nat.le_of_dvd (pow_pos (by decide) t) heDvdPow
  obtain ⟨k, hk⟩ := hhalfDvd
  have hhalfPos : 0 < 2 ^ (t - 1) := pow_pos (by decide) _
  have hdoubleHalf : 2 ^ (t - 1) * 2 = 2 ^ t := by
    calc
      2 ^ (t - 1) * 2 = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
      _ = 2 ^ t := hpow.symm
  have hkPos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkZero
    subst k
    simp at hk
    omega
  have hkLe : k ≤ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (t - 1))
    · rw [← hk, hdoubleHalf]
      exact heLe
    · exact hhalfPos
  have hkCases : k = 1 ∨ k = 2 := by
    omega
  rcases hkCases with rfl | rfl
  · left
    simpa only [eNat, deltaQ, delta, pi, H, Q, Nat.mul_one] using hk
  · right
    simpa only [eNat, deltaQ, delta, pi, H, Q, hdoubleHalf] using hk

/-- Fifth-stratum specialization of the uniform quotient phase: the retained
difference has quotient order exactly `16` or `32`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.retainedDifference_quotientOrder_eq_sixteen_or_thirtyTwo_of_fifthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 5 * q) →+ ZMod (2 ^ 5 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g x - g z)) = 16 ∨
      addOrderOf (pi (g x - g z)) = 32 := by
  simpa using
    hrows.retainedDifference_quotientOrder_eq_half_or_full_of_positiveStratum_minimal
      (t := 5) (q := q) (by omega) g hg hunique hne y hyq hfullOdd B
        hminimal x z hxB hzB hxz hcomplement

end MinModulus
