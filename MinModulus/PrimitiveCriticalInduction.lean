import MinModulus.CriticalAffineCompression

/-!
# Strong-dimension induction with primitive critical G1

The affine-compression child bound is discharged internally by strong
induction on tuple dimension. Every exact stratum and the global envelope
follow from the primitive three-omission residual plus the SAME G2 and G3.
There is no extra induction hypothesis or fourth global gate in the final
theorems. Small half-deletion bases are constructed directly by parity.

The numerical step below is the arithmetic of GlobalRoadmap's existing
stratified induction, exposed pointwise so the induction order can change
without modifying that foundational module or its downstream interfaces.
The primitive residual, G2, and G3 remain open assumptions, not axioms.
-/

namespace MinModulus
open Finset

/-- The numerical step in the existing stratified induction, exposed for
strong induction on DIMENSION. The actual parent and the child stratum
bound are retained; G3 is used only at the exceptional boundary. -/
theorem stratum_lower_bound_of_valid_half_child_stratum_bound
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 3 ≤ n)
    (hv : AdmitsValidTuple n (2^(s+1)*q))
    (hih : stratumBound (n-1) s ≤ 2^s*q) :
    stratumBound n (s+1) ≤ 2^(s+1)*q := by
  let M := 2^s*q
  have hnprev : 2 ≤ n-1 := by omega
  have hv2 : AdmitsValidTuple n (2*M) := by
    simpa [M,pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hv
  let m := Nat.log 2 n
  have hm_lt : m < n := Nat.log_lt_self 2 (by omega)
  have hpred_ne : n - 1 ≠ 0 := by omega
  have hlog_adj : Nat.log 2 (n - 1) = m ↔ 2 ^ m ≠ n := by
    simpa [m, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (Nat.log_eq_log_succ_iff (b := 2) (n := n - 1) (by omega) hpred_ne)
  by_cases hpow : 2 ^ m = n
  · have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      have hn1 : n = 1 := by simpa [hm0] using hpow.symm
      omega
    have hmform : m = m - 1 + 1 := by omega
    have hp_pos : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
    have hp_split : 2 ^ m = 2 ^ (m - 1) * 2 := by
      calc
        2 ^ m = 2 ^ (m - 1 + 1) := congrArg (fun e => 2 ^ e) hmform
        _ = 2 ^ (m - 1) * 2 := pow_succ 2 (m - 1)
    have hp_low : 2 ^ (m - 1) ≤ n - 1 := by omega
    have hp_high : n - 1 < 2 ^ (m - 1 + 1) := by
      rw [← hmform, hpow]
      omega
    have hlogpred : Nat.log 2 (n - 1) = m - 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow hp_low hp_high
    have hexp : min s (m - 1) + 1 = min (s + 1) m := by omega
    have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc
        2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
        _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
        _ = 2 * 2 ^ (n - 1) := by omega
    have hstep : stratumBound n (s + 1) = 2 * stratumBound (n - 1) s := by
      unfold stratumBound
      rw [hlogpred]
      rw [hpow_n, ← hexp]
      rw [show 2 ^ (min s (m - 1) + 1) =
        2 * 2 ^ min s (m - 1) by rw [pow_succ]; omega]
      omega
    rw [hstep]
    calc
      2 * stratumBound (n - 1) s ≤ 2 * M := Nat.mul_le_mul_left 2 hih
      _ = 2 ^ (s + 1) * q := by
        simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
  · have hlogpred : Nat.log 2 (n - 1) = m := hlog_adj.mpr hpow
    by_cases hs : s < m
    · have hexp : min s m + 1 = min (s + 1) m := by omega
      have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
        calc
          2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
          _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
          _ = 2 * 2 ^ (n - 1) := by omega
      have hstep : stratumBound n (s + 1) =
          2 * stratumBound (n - 1) s := by
        unfold stratumBound
        rw [hlogpred]
        rw [hpow_n, ← hexp]
        rw [show 2 ^ (min s m + 1) = 2 * 2 ^ min s m by
          rw [pow_succ]; omega]
        omega
      rw [hstep]
      calc
        2 * stratumBound (n - 1) s ≤ 2 * M := Nat.mul_le_mul_left 2 hih
        _ = 2 ^ (s + 1) * q := by
          simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
    · have hms : m ≤ s := by omega
      have hprev : stratumBound (n - 1) s = globalBound (n - 1) := by
        simp [stratumBound, globalBound, hlogpred, min_eq_right hms]
      have hcur : stratumBound n (s + 1) = globalBound n := by
        have hmss : m ≤ s + 1 := by omega
        simp [stratumBound, globalBound, m, min_eq_right hmss]
      have hCM : globalBound (n - 1) ≤ M := by simpa [hprev, M] using hih
      have hMne : M ≠ globalBound (n - 1) := by
        intro heq
        exact (hG3 n (by omega) hpow) (by simpa [heq] using hv2)
      have hCltM : globalBound (n - 1) < M := lt_of_le_of_ne hCM (Ne.symm hMne)
      have hm_pred : m ≤ n - 1 := by omega
      have hdvdM : 2 ^ m ∣ M := by
        refine ⟨2 ^ (s - m) * q, ?_⟩
        have hsform : s = m + (s - m) := by omega
        have hpows : 2 ^ s = 2 ^ m * 2 ^ (s - m) := by
          calc
            2 ^ s = 2 ^ (m + (s - m)) := congrArg (fun e => 2 ^ e) hsform
            _ = 2 ^ m * 2 ^ (s - m) := pow_add 2 m (s - m)
        calc
          M = 2 ^ s * q := rfl
          _ = (2 ^ m * 2 ^ (s - m)) * q := by rw [hpows]
          _ = 2 ^ m * (2 ^ (s - m) * q) := by ring
      have hdvdC : 2 ^ m ∣ globalBound (n - 1) := by
        refine ⟨2 ^ (n - 1 - m) - 1, ?_⟩
        unfold globalBound
        rw [hlogpred]
        have hnform' : n - 1 = m + (n - 1 - m) := by omega
        have hpown' : 2 ^ (n - 1) = 2 ^ m * 2 ^ (n - 1 - m) := by
          calc
            2 ^ (n - 1) = 2 ^ (m + (n - 1 - m)) :=
              congrArg (fun e => 2 ^ e) hnform'
            _ = 2 ^ m * 2 ^ (n - 1 - m) := pow_add 2 m (n - 1 - m)
        calc
          2 ^ (n - 1) - 2 ^ m =
              2 ^ m * 2 ^ (n - 1 - m) - 2 ^ m := by rw [hpown']
          _ = 2 ^ m * (2 ^ (n - 1 - m) - 1) := by
            rw [Nat.mul_sub_left_distrib, mul_one]
      obtain ⟨u, hu⟩ := hdvdM
      obtain ⟨v, hv⟩ := hdvdC
      have huv : v + 1 ≤ u := by
        rw [hu, hv] at hCltM
        exact Nat.succ_le_iff.mpr ((Nat.mul_lt_mul_left (pow_pos (by omega) m)).mp hCltM)
      have hgap : globalBound (n - 1) + 2 ^ m ≤ M := by
        rw [hu, hv]
        calc
          2 ^ m * v + 2 ^ m = 2 ^ m * (v + 1) := by ring
          _ ≤ 2 ^ m * u := Nat.mul_le_mul_left _ huv
      have hCsum : globalBound (n - 1) + 2 ^ m = 2 ^ (n - 1) := by
        unfold globalBound
        rw [hlogpred]
        have hp_le : 2 ^ m ≤ 2 ^ (n - 1) :=
          Nat.pow_le_pow_right (by omega) hm_pred
        exact Nat.sub_add_cancel hp_le
      have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
        calc
          2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
          _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
          _ = 2 * 2 ^ (n - 1) := by omega
      rw [hcur]
      calc
        globalBound n ≤ 2 ^ n := Nat.sub_le _ _
        _ = 2 * 2 ^ (n - 1) := hpow_n
        _ ≤ 2 * M := by rw [← hCsum]; exact Nat.mul_le_mul_left 2 hgap
        _ = 2 ^ (s + 1) * q := by
          simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]

/-- Every tuple of length at most three has a same-parity subtuple of
one fewer coordinate, giving an actual half child without any gate. -/
theorem admitsValidTuple_half_of_length_le_three
    {n M : ℕ} [NeZero M] (hn : n ≤ 2)
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g) :
    AdmitsValidTuple n M := by
  rcases admitsValidTuple_half_or_two_large_parity_fibres g hg with hhalf | hlarge
  · exact hhalf
  · have hcard := parity_fibre_card_zero_add_one g
    omega

/-- The SAME three-omission G1 obligation, restricted to parents whose
every deleted subtuple affinely generates the ambient group. The small
dimensions are excluded here because their half children are automatic. -/
def PrimitiveThreeOmissionDeleteStep : Prop :=
  ∀ {n s q : ℕ}, 3 ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      AdmitsValidTuple n (2^s*q)

/-- The original G1 input implies the restricted input. No fourth gate
or independent primitivity assumption is introduced. -/
theorem primitiveThreeOmissionDeleteStep_of_threeOmissionDeleteStep
    (hG1 : CriticalThreeOmissionDeleteStep) : PrimitiveThreeOmissionDeleteStep := by
  intro n s q _ hq g hg hcritical hthree _
  exact hG1 hq g hg hcritical hthree

/-- Given the bound in the strictly smaller dimension, the primitive
residual supplies the complete critical deletion step at this dimension.
Compression, common touch, and the small bases are already proved. -/
theorem critical_delete_of_primitive_threeOmissions_of_child_bound
    (hPrimitive : PrimitiveThreeOmissionDeleteStep)
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L) :
    AdmitsValidTuple n (2^s*q) := by
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^s*q) := ⟨ne_of_gt hM⟩
  letI : NeZero (2^(s+1)*q) := ⟨ne_of_gt (mul_pos (by positivity) hq.pos)⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  by_cases hn : n ≤ 2
  · have hvalid : AdmitsValidTuple (n+1) (2*(2^s*q)) := by
      simpa only [hN] using (show AdmitsValidTuple (n+1) (2^(s+1)*q) from ⟨g,hg⟩)
    obtain ⟨f,hf⟩ := hvalid
    exact admitsValidTuple_half_of_length_le_three hn f hf
  have hn3 : 3 ≤ n := by omega
  rcases half_descent_or_all_deleted_affine_spans_top_of_critical_stratum
    hn3 hq g hg hcritical hbound with hhalf | hfull
  · exact hhalf
  have hsmall : 2^(s+1)*q < 2^(n+1) := hcritical.trans_le (Nat.sub_le _ _)
  rcases commonTouched_or_threeOmissions_of_lt_two_pow hN hM g hg hsmall
      with ⟨j,hj⟩ | hthree
  · exact exists_validTuple_half_of_delete hN hM hg j hj
  · exact hPrimitive hn3 hq g hg hcritical hthree hfull

/-- Strong induction on DIMENSION discharges the child-bound premise
internally. Only the primitive G1 residual, G2, and G3 remain as inputs;
there is no fourth global induction hypothesis. -/
theorem stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (hPrimitive : PrimitiveThreeOmissionDeleteStep)
    (hG2 : OddStratumLowerBound) (hG3 : ExceptionalLiftObstruction) :
    ∀ {n s q : ℕ}, 2 ≤ n → Odd q → AdmitsValidTuple n (2^s*q) →
      stratumBound n s ≤ 2^s*q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s q hn hq hv
    cases s with
    | zero =>
      have h := hG2 hq (by simpa using hv)
      simpa [stratumBound] using h
    | succ s =>
      by_cases hcritical : 2^(s+1)*q < stratumBound n (s+1)
      swap
      · omega
      by_cases hn2 : n=2
      · subst n
        have hb : stratumBound 2 (s+1)=2 := by
          norm_num [stratumBound,min_eq_right (by omega : 1 ≤ s+1)]
        rw [hb]
        have hqpos := hq.pos
        have hpowpos : 0 < 2^s := by positivity
        rw [pow_succ',mul_assoc]
        nlinarith
      have hn3 : 3 ≤ n := by omega
      have hnprev : 2 ≤ n-1 := by omega
      have hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple (n-1) L → globalBound (n-1) ≤ L := by
        intro L hL hvalid
        obtain ⟨t,r,hr,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hL.ne'
        have hs := ih (n-1) (by omega) hnprev hr hvalid
        have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
          (min_le_right t (Nat.log 2 (n-1)))
        exact (Nat.sub_le_sub_left hp (2^(n-1))).trans hs
      have hnform : n-1+1=n := by omega
      have hvalid : AdmitsValidTuple (n-1+1) (2^(s+1)*q) := by simpa only [hnform] using hv
      obtain ⟨g,hg⟩ := hvalid
      have hdelete := critical_delete_of_primitive_threeOmissions_of_child_bound hPrimitive hq g hg
        (by simpa only [hnform] using hcritical) hbound
      have hchild := ih (n-1) (by omega) hnprev hq hdelete
      exact stratum_lower_bound_of_valid_half_child_stratum_bound hG3 hn3 hv hchild

/-- Direct sufficient route to the unconditional Conjecture 1 using only
the genuinely primitive part of G1, plus the SAME open G2 and G3. The
lower-dimensional hypothesis from affine compression is now discharged. -/
theorem global_lower_bound_of_primitive_threeOmissionDeleteStep
    (hPrimitive : PrimitiveThreeOmissionDeleteStep)
    (hG2 : OddStratumLowerBound) (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hs := stratum_lower_bound_of_primitive_threeOmissionDeleteStep hPrimitive hG2 hG3 hn hq hv
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (min_le_right s (Nat.log 2 n))
  exact (Nat.sub_le_sub_left hp (2^n)).trans hs

end MinModulus
