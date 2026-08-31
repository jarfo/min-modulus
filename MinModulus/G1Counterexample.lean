/-
# A counterexample to unrestricted common touch

The global lower-bound induction originally isolated a universal G1 premise:
every nonempty half-witness family of a valid tuple modulo `2M` should have a
coordinate touched by every witness.  This file gives a small kernel-checked
certificate that the premise is false without a modulus-range restriction.

The valid seven-tuple modulo `1006` below has four witnesses at the involution
`503` whose supports have empty intersection.  Its modulus is much larger than
the conjectured seven-coordinate lower bound `124`, so the example does not
challenge the min-modulus conjecture.  It instead shows that the descent input
must be restricted to the critical range in which the global induction uses it.
-/
import MinModulus.G1Triangle
import MinModulus.GlobalRoadmap

namespace MinModulus

open Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The valid seven-tuple modulo `1006` refuting unrestricted common touch. -/
def g1CounterexampleTuple : Fin 7 → ZMod 1006 :=
  ![172, 41, 658, 861, 601, 286, 875]

/-- A small integer encoding of the tuple after reduction modulo `503`. -/
def g1CounterexampleReduced : Fin 7 → ℕ :=
  ![0, 58, 92, 29, 75, 34, 42]

/-- Direct reduction of `g1CounterexampleTuple` modulo `503`. -/
def g1CounterexampleMod503 : Fin 7 → ZMod 503 :=
  ![172, 41, 155, 358, 98, 286, 372]

/-- Direct reduction of `g1CounterexampleTuple` modulo `2`. -/
def g1CounterexampleMod2 : Fin 7 → ZMod 2 :=
  ![0, 1, 0, 1, 1, 0, 1]

/-- The bounded weight and parity constraints uniquely select the all-ones
composition.  The finite split is an ordinary kernel proof, not an external
decision procedure. -/
lemma g1_composition_unique_of_weight_and_parity
    (k0 k1 k2 k3 k4 k5 k6 : ℕ)
    (hsum : k0 + k1 + k2 + k3 + k4 + k5 + k6 = 7)
    (hweight : 58 * k1 + 92 * k2 + 29 * k3 + 75 * k4 +
      34 * k5 + 42 * k6 = 330)
    (hparity : (k1 + k3 + k4 + k6) % 2 = 0) :
    k0 = 1 ∧ k1 = 1 ∧ k2 = 1 ∧ k3 = 1 ∧ k4 = 1 ∧ k5 = 1 ∧ k6 = 1 := by
  have hk2 : k2 ≤ 3 := by omega
  have hk4 : k4 ≤ 4 := by omega
  interval_cases k2 <;> interval_cases k4 <;> try omega
  all_goals
    have hk5 : k5 ≤ 7 := by omega
    interval_cases k5 <;> omega

/-- Equality of tuple values modulo `1006` implies equality of the reduced
weights modulo `503`. -/
lemma g1_reduced_value_eq (k : Fin 7 → ℕ) (hksum : ∑ i, k i = 7)
    (hkval : ∑ i, k i • g1CounterexampleTuple i =
      ∑ i, g1CounterexampleTuple i) :
    ∑ i, k i • (g1CounterexampleReduced i : ZMod 503) =
      ∑ i, (g1CounterexampleReduced i : ZMod 503) := by
  let f : ZMod 1006 →+* ZMod 503 :=
    ZMod.castHom (show 503 ∣ 1006 by norm_num) (ZMod 503)
  have hmap := congrArg f hkval
  simp only [map_sum, map_nsmul] at hmap
  have hfg : ∀ i, f (g1CounterexampleTuple i) =
      g1CounterexampleMod503 i := by
    intro i
    fin_cases i <;> decide
  have hmap' : ∑ i, k i • g1CounterexampleMod503 i =
      ∑ i, g1CounterexampleMod503 i := by
    simpa only [hfg] using hmap
  have hsum503 : (∑ i, (k i : ZMod 503)) = 7 := by
    rw [← Nat.cast_sum]
    exact congrArg (fun m : ℕ => (m : ZMod 503)) hksum
  have hri : ∀ i, (g1CounterexampleReduced i : ZMod 503) =
      (468 : ZMod 503) * (g1CounterexampleMod503 i - 172) := by
    intro i
    fin_cases i <;> decide
  calc
    (∑ i, k i • (g1CounterexampleReduced i : ZMod 503)) =
        (468 : ZMod 503) * ((∑ i, k i • g1CounterexampleMod503 i) -
          (∑ i, (k i : ZMod 503)) * 172) := by
      rw [mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hri]
      simp only [nsmul_eq_mul]
      ring
    _ = (468 : ZMod 503) * ((∑ i, g1CounterexampleMod503 i) -
          7 * 172) := by rw [hmap', hsum503]
    _ = ∑ i, (g1CounterexampleReduced i : ZMod 503) := by
      decide

/-- The reduced congruence is an integer equality: its nonnegative left side
is at most `7 * 92`, leaving only the representative `330` modulo `503`. -/
lemma g1_reduced_weight_eq_nat (k : Fin 7 → ℕ)
    (hksum : ∑ i, k i = 7)
    (hred : ∑ i, k i • (g1CounterexampleReduced i : ZMod 503) =
      ∑ i, (g1CounterexampleReduced i : ZMod 503)) :
    ∑ i, k i * g1CounterexampleReduced i = 330 := by
  have htotal : ∑ i, (g1CounterexampleReduced i : ZMod 503) = 330 := by
    decide
  rw [htotal] at hred
  have hmod : (∑ i, k i * g1CounterexampleReduced i) ≡ 330 [MOD 503] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    simpa only [nsmul_eq_mul] using hred
  have hrle : ∀ i, g1CounterexampleReduced i ≤ 92 := by
    intro i
    fin_cases i <;> norm_num [g1CounterexampleReduced]
  have hwle : ∑ i, k i * g1CounterexampleReduced i ≤ 644 := by
    calc
      ∑ i, k i * g1CounterexampleReduced i ≤ ∑ i, k i * 92 := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul_left (k i) (hrle i)
      _ = (∑ i, k i) * 92 := by rw [Finset.sum_mul]
      _ = 644 := by norm_num [hksum]
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd.mp hmod)
  omega

/-- Reduction modulo `2` supplies the parity condition used by the bounded
composition certificate. -/
lemma g1_composition_parity (k : Fin 7 → ℕ)
    (hkval : ∑ i, k i • g1CounterexampleTuple i =
      ∑ i, g1CounterexampleTuple i) :
    (k 1 + k 3 + k 4 + k 6) % 2 = 0 := by
  let f : ZMod 1006 →+* ZMod 2 :=
    ZMod.castHom (show 2 ∣ 1006 by norm_num) (ZMod 2)
  have hmap := congrArg f hkval
  simp only [map_sum, map_nsmul] at hmap
  have hfg : ∀ i, f (g1CounterexampleTuple i) =
      g1CounterexampleMod2 i := by
    intro i
    fin_cases i <;> decide
  have hmap' : ∑ i, k i • g1CounterexampleMod2 i =
      ∑ i, g1CounterexampleMod2 i := by
    simpa only [hfg] using hmap
  have hleft : ∑ i, k i • g1CounterexampleMod2 i =
      ((k 1 + k 3 + k 4 + k 6 : ℕ) : ZMod 2) := by
    simp [g1CounterexampleMod2, Fin.sum_univ_succ, nsmul_eq_mul]
    ring
  have hright : ∑ i, g1CounterexampleMod2 i = 0 := by
    decide
  have hzero : ((k 1 + k 3 + k 4 + k 6 : ℕ) : ZMod 2) = 0 := by
    rw [← hleft, hmap', hright]
  rw [ZMod.natCast_eq_zero_iff] at hzero
  exact Nat.mod_eq_zero_of_dvd hzero

/-- The concrete seven-tuple is valid modulo `1006`. -/
theorem g1CounterexampleTuple_valid : ValidTuple g1CounterexampleTuple := by
  intro k hksum hkval i
  have hred := g1_reduced_value_eq k hksum hkval
  have hweightSum := g1_reduced_weight_eq_nat k hksum hred
  have hsum :
      k 0 + k 1 + k 2 + k 3 + k 4 + k 5 + k 6 = 7 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hksum
  have hweight :
      58 * k 1 + 92 * k 2 + 29 * k 3 + 75 * k 4 +
        34 * k 5 + 42 * k 6 = 330 := by
    simpa [g1CounterexampleReduced, Fin.sum_univ_succ, Nat.mul_comm,
      Nat.add_assoc] using hweightSum
  have hparity := g1_composition_parity k hkval
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
    g1_composition_unique_of_weight_and_parity
      (k 0) (k 1) (k 2) (k 3) (k 4) (k 5) (k 6)
      hsum hweight hparity
  fin_cases i <;> assumption

/-- First half-witness, omitting coordinates `0,1`. -/
def g1CounterexampleWitnessAB : Fin 7 → ℤ :=
  ![-1, -1, 0, 2, 0, 0, 0]

/-- Second half-witness, omitting coordinates `1,2`. -/
def g1CounterexampleWitnessBD : Fin 7 → ℤ :=
  ![0, -1, -1, 0, 2, 0, 0]

/-- Third half-witness, omitting coordinates `0,2`. -/
def g1CounterexampleWitnessDA : Fin 7 → ℤ :=
  ![-1, 1, -1, 0, 0, 1, 0]

/-- Fourth half-witness, omitting coordinates `0,2,5`. -/
def g1CounterexampleWitnessE : Fin 7 → ℤ :=
  ![-1, 0, -1, 0, 0, -1, 3]

theorem g1CounterexampleWitnessAB_isWitness :
    Witness g1CounterexampleTuple (503 : ZMod 1006)
      g1CounterexampleWitnessAB := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 7)
    norm_num [g1CounterexampleWitnessAB] at h0
  · intro i
    fin_cases i <;> norm_num [g1CounterexampleWitnessAB]
  · norm_num [g1CounterexampleWitnessAB, Fin.sum_univ_succ]
  · decide

theorem g1CounterexampleWitnessBD_isWitness :
    Witness g1CounterexampleTuple (503 : ZMod 1006)
      g1CounterexampleWitnessBD := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun h (1 : Fin 7)
    norm_num [g1CounterexampleWitnessBD] at h1
  · intro i
    fin_cases i <;> norm_num [g1CounterexampleWitnessBD]
  · norm_num [g1CounterexampleWitnessBD, Fin.sum_univ_succ]
  · decide

theorem g1CounterexampleWitnessDA_isWitness :
    Witness g1CounterexampleTuple (503 : ZMod 1006)
      g1CounterexampleWitnessDA := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 7)
    norm_num [g1CounterexampleWitnessDA] at h0
  · intro i
    fin_cases i <;> norm_num [g1CounterexampleWitnessDA]
  · norm_num [g1CounterexampleWitnessDA, Fin.sum_univ_succ]
  · decide

theorem g1CounterexampleWitnessE_isWitness :
    Witness g1CounterexampleTuple (503 : ZMod 1006)
      g1CounterexampleWitnessE := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 7)
    norm_num [g1CounterexampleWitnessE] at h0
  · intro i
    fin_cases i <;> norm_num [g1CounterexampleWitnessE]
  · norm_num [g1CounterexampleWitnessE, Fin.sum_univ_succ]
  · decide

/-- The four certified half-witnesses already have empty support
intersection, so the full witness family cannot have a common touched
coordinate. -/
theorem g1Counterexample_no_common_touched :
    ¬∃ j : Fin 7, ∀ c : Fin 7 → ℤ,
      Witness g1CounterexampleTuple (503 : ZMod 1006) c → c j ≠ 0 := by
  rintro ⟨j, hj⟩
  fin_cases j
  · exact (hj g1CounterexampleWitnessBD
      g1CounterexampleWitnessBD_isWitness) (by
        norm_num [g1CounterexampleWitnessBD])
  · exact (hj g1CounterexampleWitnessE
      g1CounterexampleWitnessE_isWitness) (by
        norm_num [g1CounterexampleWitnessE])
  · exact (hj g1CounterexampleWitnessAB
      g1CounterexampleWitnessAB_isWitness) (by
        norm_num [g1CounterexampleWitnessAB])
  · exact (hj g1CounterexampleWitnessBD
      g1CounterexampleWitnessBD_isWitness) (by
        norm_num [g1CounterexampleWitnessBD])
  · exact (hj g1CounterexampleWitnessAB
      g1CounterexampleWitnessAB_isWitness) (by
        norm_num [g1CounterexampleWitnessAB])
  · exact (hj g1CounterexampleWitnessAB
      g1CounterexampleWitnessAB_isWitness) (by
        norm_num [g1CounterexampleWitnessAB])
  · exact (hj g1CounterexampleWitnessAB
      g1CounterexampleWitnessAB_isWitness) (by
        norm_num [g1CounterexampleWitnessAB])

/-- The universal `CommonTouchedHalfWitnesses` roadmap premise is false. -/
theorem not_commonTouchedHalfWitnesses : ¬CommonTouchedHalfWitnesses := by
  intro hG1
  have hcommon := hG1 (n := 6) (M := 503) (by norm_num)
    g1CounterexampleTuple g1CounterexampleTuple_valid
    ⟨g1CounterexampleWitnessAB, g1CounterexampleWitnessAB_isWitness⟩
  exact g1Counterexample_no_common_touched hcommon

/-- The counterexample lies far outside the first-even critical range for
seven coordinates (`1006 ≥ 126`), so it does not refute the corrected G1
premise used by the global lower-bound induction. -/
theorem g1Counterexample_outside_critical_range :
    ¬1006 < stratumBound 7 1 := by
  norm_num [stratumBound]

end MinModulus
