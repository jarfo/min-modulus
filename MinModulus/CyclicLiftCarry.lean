import MinModulus.QuotientRivalParity

/-!
# Complete cyclic lift equations with all higher-even carries

Fix ANY actual base lift v of an arbitrary quotient q modulo M.
Every cyclic lift modulo 2M is v plus independent half-modulus kernel
bits b_i. For a nonstandard quotient rival c, its base sum is M*kappa(c),
with kappa in ZMod 2. The lifted tuple is valid exactly when
  kappa(c) + sum_i(c_i*b_i) = 1
for EVERY quotient rival. Both directions and actual bit extraction are
proved for all M>0, not only odd half-modulus or structured prefixes.

A finite family of rivals whose parity vectors sum to zero excludes
EVERY lift if its carry sum differs from the family size modulo two.
The family may be odd OR even. In particular two rivals of identical
parity and opposite carry already give an all-lift obstruction.

These are uniform criteria/certificates, not a proof that arbitrary
critical or exceptional quotients necessarily supply a certificate.
Unrestricted G1/G2/G3 and Conjecture 1 remain open.
-/

namespace MinModulus
open Finset

/-- The additive embedding of the two-element half-modulus kernel. -/
def zmodHalfHom (M : ℕ) : ZMod 2 →+ ZMod (2*M) :=
  (ZMod.ringEquivCongr (Nat.mul_comm M 2)).toAddMonoidHom.comp (zmodScaleHom M 2)

/-- The nonzero bit is the actual half-modulus element. -/
theorem zmodHalfHom_one (M : ℕ) : zmodHalfHom M 1=(M : ZMod (2*M)) := by
  change (ZMod.ringEquivCongr (Nat.mul_comm M 2)) (zmodScaleHom M 2 ((1 : ℕ) : ZMod 2))=_
  rw [zmodScaleHom_natCast, Nat.mul_one, map_natCast]

/-- Distinct lift bits give distinct kernel elements. -/
theorem zmodHalfHom_injective {M : ℕ} [NeZero M] : Function.Injective (zmodHalfHom M) := by
  haveI : NeZero (M*2) := ⟨Nat.mul_ne_zero (NeZero.ne M) (by decide)⟩
  exact (ZMod.ringEquivCongr (Nat.mul_comm M 2)).injective.comp
    (zmodScaleHom_injective (d := M) (M := 2))

/-- Changing a lift bit does not change the actual quotient. -/
theorem castHom_zmodHalfHom {M : ℕ} [NeZero M] (b : ZMod 2) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (zmodHalfHom M b)=0 := by
  fin_cases b
  · change ZMod.castHom (dvd_mul_left M 2) (ZMod M) (zmodHalfHom M 0)=0
    rw [map_zero,map_zero]
  · change ZMod.castHom (dvd_mul_left M 2) (ZMod M) (zmodHalfHom M 1)=0
    rw [zmodHalfHom_one,map_natCast,ZMod.natCast_self]

/-- Carry of a quotient rival in a chosen base lift. The zero case
has carry zero; a nonzero quotient-zero sum has carry one. -/
noncomputable def cyclicRivalCarry {n M : ℕ}
    (v : Fin n → ZMod (2*M)) (c : Fin n → ℤ) : ZMod 2 := by
  classical
  exact if (∑ i, c i • v i)=0 then 0 else 1

/-- The carry records the ACTUAL weighted sum of any quotient rival. -/
theorem quotient_rival_sum_eq_halfHom_carry
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (c : Fin n → ℤ) (hc : Witness q 0 c) :
    (∑ i, c i • v i)=zmodHalfHom M (cyclicRivalCarry v c) := by
  classical
  have hzero : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (∑ i, c i • v i)=0 := by
    simpa only [map_sum, map_zsmul, hquot] using hc.2.2.2
  by_cases hz : (∑ i, c i • v i)=0
  · rw [cyclicRivalCarry,if_pos hz,map_zero,hz]
  · rcases eq_or_eq_add_half_of_castHom_eq (∑ i, c i • v i) 0
      (by simpa only [map_zero] using hzero) with h | h
    · exact (hz h).elim
    · simpa only [cyclicRivalCarry,if_neg hz,zmodHalfHom_one,zero_add] using h

/-- Every lift of an arbitrary quotient is a base lift plus actual
kernel bits, including at higher-even half-modulus. -/
theorem exists_kernel_bits_of_same_quotient
    {n M : ℕ} [NeZero M] (v g : Fin n → ZMod (2*M))
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)) :
    ∃ b : Fin n → ZMod 2, ∀ i, g i=v i+zmodHalfHom M (b i) := by
  classical
  refine ⟨fun i ↦ if g i=v i then 0 else 1,?_⟩
  intro i
  by_cases h : g i=v i
  · simp [h]
  · rcases eq_or_eq_add_half_of_castHom_eq (g i) (v i) (hquot i) with heq | heq
    · exact (h heq).elim
    · simpa [h,zmodHalfHom_one] using heq

/-- Changing kernel bits adds the rival's parity dot product to its
base carry. This exact identity retains ALL higher-even carry data. -/
theorem quotient_rival_sum_after_kernel_bits
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (b : Fin n → ZMod 2) (c : Fin n → ℤ) (hc : Witness q 0 c) :
    (∑ i, c i • (v i+zmodHalfHom M (b i)))=
      zmodHalfHom M (cyclicRivalCarry v c+(∑ i, c i • b i)) := by
  simp only [smul_add, Finset.sum_add_distrib, map_add, map_sum, map_zsmul]
  rw [quotient_rival_sum_eq_halfHom_carry v q hquot c hc]

/-- COMPLETE all-stratum criterion for a specified bit lift:
every nonstandard quotient rival must have total carry one. -/
theorem validTuple_kernel_lift_iff_carry_equations
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (b : Fin n → ZMod 2) :
    ValidTuple (fun i ↦ v i+zmodHalfHom M (b i)) ↔
      ∀ c : Fin n → ℤ, Witness q 0 c → cyclicRivalCarry v c+(∑ i, c i • b i)=1 := by
  let g : Fin n → ZMod (2*M) := fun i ↦ v i+zmodHalfHom M (b i)
  have hgquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i := by
    intro i
    simp only [g,map_add,hquot,castHom_zmodHalfHom,add_zero]
  constructor
  · intro hg c hc
    apply zmodHalfHom_injective (M := M)
    rw [zmodHalfHom_one, ← quotient_rival_sum_after_kernel_bits v q hquot b c hc]
    exact (witness_half_of_valid_quotient_rival g hg q hgquot c hc).2.2.2
  · intro h
    apply (validTuple_iff_no_zero_witness g).mpr
    intro c hc
    have hq : Witness q 0 c := by
      refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
      simpa only [map_sum,map_zsmul,hgquot,map_zero] using
        congrArg (ZMod.castHom (dvd_mul_left M 2) (ZMod M)) hc.2.2.2
    have hs := quotient_rival_sum_after_kernel_bits v q hquot b c hq
    rw [h c hq,zmodHalfHom_one] at hs
    exact half_ne_zero rfl (Nat.pos_of_ne_zero (NeZero.ne M)) (hs.symm.trans hc.2.2.2)

/-- COMPLETE all-stratum lift feasibility for ANY quotient and any
chosen base lift. No lift bits, normal forms, or carry terms are omitted. -/
theorem exists_valid_cyclic_lift_iff_carry_equations
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i) :
    (∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ↔
    ∃ b : Fin n → ZMod 2, ∀ c : Fin n → ℤ, Witness q 0 c →
      cyclicRivalCarry v c+(∑ i, c i • b i)=1 := by
  constructor
  · rintro ⟨g,hg,hgquot⟩
    obtain ⟨b,hb⟩ := exists_kernel_bits_of_same_quotient v g
      (fun i ↦ (hgquot i).trans (hquot i).symm)
    refine ⟨b, (validTuple_kernel_lift_iff_carry_equations v q hquot b).mp ?_⟩
    simpa only [← hb] using hg
  · rintro ⟨b,hb⟩
    refine ⟨_, (validTuple_kernel_lift_iff_carry_equations v q hquot b).mpr hb,?_⟩
    intro i
    simp only [map_add,hquot,castHom_zmodHalfHom,add_zero]

/-- A finite zero-parity dependence with inconsistent carry sum
excludes EVERY cyclic lift. Family size may be odd OR even; this is the
general all-stratum certificate, including the exceptional G3 moduli. -/
theorem no_valid_cyclic_lift_of_rival_carry_dependence
    {n r M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (c : Fin r → Fin n → ℤ) (hc : ∀ j, Witness q 0 (c j))
    (hparity : ∀ i, (∑ j, (c j i : ZMod 2))=0)
    (hcarry : (∑ j, cyclicRivalCarry v (c j)) ≠ (r : ZMod 2)) :
    ¬(∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) := by
  intro hex
  obtain ⟨b,hb⟩ := (exists_valid_cyclic_lift_iff_carry_equations v q hquot).mp hex
  have hrows : ∀ j, cyclicRivalCarry v (c j)+(∑ i, c j i • b i)=1 := fun j ↦ hb (c j) (hc j)
  have hlinear : (∑ j, ∑ i, c j i • b i)=0 := by
    rw [Finset.sum_comm]
    simp only [zsmul_eq_mul, ← Finset.sum_mul, hparity, zero_mul, Finset.sum_const_zero]
  have hsum : (∑ j, (cyclicRivalCarry v (c j)+(∑ i, c j i • b i)))=
      ∑ _j : Fin r, (1 : ZMod 2) := Finset.sum_congr rfl (fun j _ ↦ hrows j)
  simp only [Finset.sum_add_distrib, hlinear, add_zero, Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hsum
  exact hcarry hsum

/-- Two quotient rivals with identical parity but opposite base carry
already exclude EVERY cyclic lift, with no prefix or dimension assumption. -/
theorem no_valid_cyclic_lift_of_same_parity_opposite_carry
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (c d : Fin n → ℤ) (hc : Witness q 0 c) (hd : Witness q 0 d)
    (hparity : ∀ i, (c i : ZMod 2)=(d i : ZMod 2))
    (hcarry : cyclicRivalCarry v c ≠ cyclicRivalCarry v d) :
    ¬(∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) := by
  intro hex
  obtain ⟨b,hb⟩ := (exists_valid_cyclic_lift_iff_carry_equations v q hquot).mp hex
  have hlin : (∑ i, c i • b i)=(∑ i, d i • b i) := by simp only [zsmul_eq_mul,hparity]
  have hce := hb c hc
  rw [hlin] at hce
  exact hcarry (add_right_cancel (hce.trans (hb d hd).symm))

/-- Changing the chosen base lift changes the carry by exactly the
corresponding parity dot product. The affine system retains the same
actual lift set; no canonical representative is silently assumed. -/
theorem cyclicRivalCarry_rebase
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i)
    (b : Fin n → ZMod 2) (c : Fin n → ℤ) (hc : Witness q 0 c) :
    cyclicRivalCarry (fun i ↦ v i+zmodHalfHom M (b i)) c=
      cyclicRivalCarry v c+(∑ i, c i • b i) := by
  apply zmodHalfHom_injective (M := M)
  rw [← quotient_rival_sum_eq_halfHom_carry (fun i ↦ v i+zmodHalfHom M (b i)) q
    (fun i ↦ by simp only [map_add,hquot,castHom_zmodHalfHom,add_zero]) c hc]
  exact quotient_rival_sum_after_kernel_bits v q hquot b c hc

end MinModulus
