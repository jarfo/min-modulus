import MinModulus.ActualFibreSidon

/-!
# General quotient-rival parity criteria for cyclic lifts

Every zero-target rival of a quotient of a valid even tuple lifts to
an actual half-target witness. At ODD half modulus, parent validity is
equivalent to the actual coordinate parity vector evaluating to one on
every quotient rival. Conversely a separating parity vector constructs
an actual valid lift by CRT. This gives a complete first-even feasibility
criterion with no SI, fibre-shape, dimension, or criticality premise.

An ODD family of quotient rivals with coordinatewise even total therefore
excludes every first-even lift. The general higher-even obstruction
retains the necessary carry condition: if the coefficient sum is 2*d,
the halved vector d must also evaluate to zero in the actual quotient.
This condition is automatic only at odd half modulus. It cannot be
dropped at even half modulus, as a genuine valid control demonstrates.

Criticality is NOT proved to supply such a dependence, or a valid
deletion, in arbitrary tuples. The unrestricted G1/G2/G3 inputs stay open.
-/

namespace MinModulus
open Finset

/-- A zero-target quotient rival of a valid even lift must be an
actual half-target witness upstairs. This holds at every even stratum. -/
theorem witness_half_of_valid_quotient_rival
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2*M)) (hg : ValidTuple g)
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i)
    (c : Fin n → ℤ) (hc : Witness q 0 c) : Witness g (M : ZMod (2*M)) c := by
  refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
  have hzero : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (∑ i, c i • g i)=0 := by
    simpa only [map_sum, map_zsmul, hquot] using hc.2.2.2
  rcases eq_or_eq_add_half_of_castHom_eq (∑ i, c i • g i) 0
    (by simpa only [map_zero] using hzero) with hz | hh
  · exact ((validTuple_iff_no_zero_witness g).mp hg c ⟨hc.1,hc.2.1,hc.2.2.1,hz⟩).elim
  · simpa only [zero_add] using hh

/-- Complete first-even validity criterion: the actual parity vector
must separate EVERY nonstandard quotient rival from zero. -/
theorem validTuple_iff_first_even_quotient_rival_parity
    {n M : ℕ} [NeZero M] (hM : Odd M) (g : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) :
    ValidTuple g ↔ ∀ c : Fin n → ℤ, Witness q 0 c →
      (∑ i, c i • ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i))=1 := by
  constructor
  · intro hg c hc
    have hw := (witness_half_of_valid_quotient_rival g hg q hquot c hc).2.2.2
    have h := congrArg (ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)) hw
    have hmone : (M : ZMod 2)=1 := by
      obtain ⟨k,hk⟩ := hM
      rw [hk]
      simp [Nat.cast_add, Nat.cast_mul, show (2 : ZMod 2)=0 from by decide]
    simpa only [map_sum, map_zsmul, map_natCast, hmone] using h
  · intro h
    apply (validTuple_iff_no_zero_witness g).mpr
    intro c hc
    have hq : Witness q 0 c := by
      refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
      simpa only [map_sum, map_zsmul, hquot, map_zero] using
        congrArg (ZMod.castHom (dvd_mul_left M 2) (ZMod M)) hc.2.2.2
    have hz : (∑ i, c i • ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i))=0 := by
      simpa only [map_sum, map_zsmul, map_zero] using
        congrArg (ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)) hc.2.2.2
    have hbad : (0 : ZMod 2)=1 := hz.symm.trans (h c hq)
    exact zero_ne_one hbad

/-- An odd family of quotient rivals with coordinate sum 2*d is an
obstruction to EVERY actual lift if the halved sum d is also quotient-zero.
The latter carry condition is retained when the half modulus is even. -/
theorem not_validTuple_of_odd_quotient_rival_dependence
    {n r M : ℕ} [NeZero M] (hr : Odd r)
    (q : Fin n → ZMod M) (c : Fin r → Fin n → ℤ)
    (hc : ∀ j, Witness q 0 (c j)) (d : Fin n → ℤ)
    (hd : ∀ i, (∑ j, c j i)=2*d i) (hdq : (∑ i, d i • q i)=0)
    (g : Fin n → ZMod (2*M))
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) :
    ¬ValidTuple g := by
  intro hg
  have hrows : ∀ j, (∑ i, c j i • g i)=(M : ZMod (2*M)) :=
    fun j ↦ (witness_half_of_valid_quotient_rival g hg q hquot (c j) (hc j)).2.2.2
  have hsum : (∑ j, ∑ i, c j i • g i)=(M : ZMod (2*M)) := by
    simp only [hrows, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    obtain ⟨k,hk⟩ := hr
    rw [hk, add_nsmul, one_nsmul]
    have heven : (2*k) • (M : ZMod (2*M))=0 := by
      have hh : (M : ZMod (2*M))+M=0 := half_add_half rfl
      calc
        (2*k) • (M : ZMod (2*M))=k • ((M : ZMod (2*M))+M) := by
          simp only [← two_nsmul, smul_smul]
          congr 1
          omega
        _=0 := by rw [hh,smul_zero]
    rw [heven, zero_add]
  have hdouble : (∑ j, ∑ i, c j i • g i)=2 • (∑ i, d i • g i) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul, hd, mul_smul]
    simp only [show (2 : ℤ)=((2 : ℕ) : ℤ) from rfl, natCast_zsmul]
  have hz : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (∑ i, d i • g i)=0 := by
    simpa only [map_sum, map_zsmul, hquot] using hdq
  have hzero : 2 • (∑ i, d i • g i)=0 := by
    rw [← zmodScaleHom_castHom, hz, map_zero]
  exact half_ne_zero rfl (Nat.pos_of_ne_zero (NeZero.ne M)) (hsum.symm.trans (hdouble.trans hzero))

/-- At odd half modulus, the halved relation is automatically
quotient-zero. Only an odd dependence of rival parity vectors is needed. -/
theorem not_validTuple_of_first_even_odd_quotient_rival_dependence
    {n r M : ℕ} [NeZero M] (hM : Odd M) (hr : Odd r)
    (q : Fin n → ZMod M) (c : Fin r → Fin n → ℤ)
    (hc : ∀ j, Witness q 0 (c j)) (d : Fin n → ℤ)
    (hd : ∀ i, (∑ j, c j i)=2*d i)
    (g : Fin n → ZMod (2*M))
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) :
    ¬ValidTuple g := by
  apply not_validTuple_of_odd_quotient_rival_dependence hr q c hc d hd ?_ g hquot
  have hzero : (2 : ZMod M)*(∑ i, d i • q i)=0 := by
    have hsum : (∑ j, ∑ i, c j i • q i)=0 := by simp only [fun j ↦ (hc j).2.2.2, Finset.sum_const_zero]
    rw [Finset.sum_comm] at hsum
    simp only [← Finset.sum_smul, hd, mul_smul, show (2 : ℤ)=((2 : ℕ) : ℤ) from rfl,
      natCast_zsmul, ← Finset.smul_sum] at hsum
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hsum
  apply ((ZMod.isUnit_iff_coprime 2 M).mpr hM.coprime_two_left).mul_left_cancel
  simpa only [Nat.cast_ofNat, mul_zero] using hzero

/-- Coordinatewise EVEN total coefficients give a directly checkable
odd-family obstruction to every first-even lift, in all dimensions. -/
theorem not_validTuple_of_first_even_odd_rival_parity_family
    {n r M : ℕ} [NeZero M] (hM : Odd M) (hr : Odd r)
    (q : Fin n → ZMod M) (c : Fin r → Fin n → ℤ)
    (hc : ∀ j, Witness q 0 (c j)) (heven : ∀ i, Even (∑ j, c j i))
    (g : Fin n → ZMod (2*M))
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) :
    ¬ValidTuple g := by
  choose d hd using heven
  exact not_validTuple_of_first_even_odd_quotient_rival_dependence hM hr q c hc d
    (fun i ↦ by rw [hd i]; ring) g hquot

/-- COMPLETE first-even lift feasibility: a quotient admits a valid
cyclic lift exactly when one parity vector evaluates to one on ALL its
nonstandard rivals. The reverse implication constructs the actual lift
by the Chinese remainder equivalence, not an assumed lift-validity step. -/
theorem exists_valid_first_even_lift_iff_rival_parity_separator
    {n M : ℕ} [NeZero M] (hM : Odd M) (q : Fin n → ZMod M) :
    (∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ↔
    ∃ b : Fin n → ZMod 2, ∀ c : Fin n → ℤ, Witness q 0 c → (∑ i, c i • b i)=1 := by
  constructor
  · rintro ⟨g,hg,hquot⟩
    exact ⟨_, (validTuple_iff_first_even_quotient_rival_parity hM g q hquot).mp hg⟩
  · rintro ⟨b,hb⟩
    let e := ZMod.chineseRemainder hM.coprime_two_left
    have hfirst (x : ZMod (2*M)) :
        (e x).1=ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) x := by
      obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
      simp only [map_natCast, Prod.fst_natCast]
    have hsecond (x : ZMod (2*M)) :
        (e x).2=ZMod.castHom (dvd_mul_left M 2) (ZMod M) x := by
      obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
      simp only [map_natCast, Prod.snd_natCast]
    let g : Fin n → ZMod (2*M) := fun i ↦ e.symm (b i,q i)
    have hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i := by
      intro i
      rw [← hsecond]
      simp only [g, RingEquiv.apply_symm_apply]
    refine ⟨g,?_,hquot⟩
    apply (validTuple_iff_first_even_quotient_rival_parity hM g q hquot).mpr
    intro c hc
    have hparity : ∀ i, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i)=b i := by
      intro i
      rw [← hfirst]
      simp only [g, RingEquiv.apply_symm_apply]
    simpa only [hparity] using hb c hc

end MinModulus
