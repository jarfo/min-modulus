/-
# Interfaces for the global min-modulus roadmap

This file packages the three remaining conjectural inputs separately from the
proved descent machinery.  In particular, `admits_half_or_delete_of_g1` is the
exact operational consequence of G1 used by a stratified induction.
-/
import MinModulus.QuadraticWedge
import MinModulus.UniqueSums

namespace MinModulus

open Finset

/-- A cyclic modulus `N` admits a valid tuple of length `n`. -/
def AdmitsValidTuple (n N : ℕ) : Prop :=
  ∃ g : Fin n → ZMod N, ValidTuple g

/-- The fixed-set bound from the paper, used to state the exceptional lift
modulus in G3. -/
def globalBound (n : ℕ) : ℕ :=
  2 ^ n - 2 ^ Nat.log 2 n

/-- The predicted lower bound in the exact `2^s * q` stratum (`q` odd).
For `s ≤ log₂ n` this is the endpoint `2^n - 2^s`; afterwards it is the
global envelope `globalBound n`. -/
def stratumBound (n s : ℕ) : ℕ :=
  2 ^ n - 2 ^ min s (Nat.log 2 n)

/-- Transport the paper's fixed super-increasing validity predicate to the
group-theoretic `ValidTuple` predicate used by the descent. -/
theorem validTuple_fixed_of_valid {n N : ℕ} (hv : Valid n N) :
    ValidTuple (fun i : Fin n => (a i.val : ZMod N)) := by
  intro k hksum hkval
  let K : ℕ → ℕ := fun i => if hi : i < n then k ⟨i, hi⟩ else 0
  have hKsum : dsum n K = n := by
    unfold dsum
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [K] using hksum
  have hcast :
      ((∑ i : Fin n, k i * a i.val : ℕ) : ZMod N)
        = ((∑ i : Fin n, a i.val : ℕ) : ZMod N) := by
    push_cast
    simpa [nsmul_eq_mul] using hkval
  have hleft :
      (∑ i ∈ range n, K i * a i) = ∑ i : Fin n, k i * a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    simp [K]
  have hright : (∑ i ∈ range n, a i) = ∑ i : Fin n, a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
  have hmod : (∑ i ∈ range n, K i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] := by
    rw [hleft, hright]
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hcast
  have hones := hv K hKsum hmod
  intro i
  simpa [K, i.isLt] using hones i.val i.isLt

/-- Every power-gap endpoint from `valid_gap` therefore admits a valid tuple
in the group-theoretic formulation. -/
theorem admitsValidTuple_gap {n t : ℕ} (hn : 2 ≤ n) (htn : 2 ^ t ≤ n) :
    AdmitsValidTuple n (2 ^ n - 2 ^ t) :=
  ⟨_, validTuple_fixed_of_valid (valid_gap hn htn)⟩

/-- **G1, common-touch form.**  Whenever the half-witness family of a valid
tuple modulo `2M` is nonempty, one coordinate is nonzero in every such
witness. -/
def CommonTouchedHalfWitnesses : Prop :=
  ∀ {n M : ℕ} (_hM : 0 < M) (g : Fin (n + 1) → ZMod (2 * M)),
    ValidTuple g →
    (∃ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c) →
    ∃ j : Fin (n + 1),
      ∀ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c → c j ≠ 0

/-- **G2, odd-base form.**  A valid `n`-tuple modulo an odd number forces the
odd modulus to be at least `2^n - 1`. -/
def OddStratumLowerBound : Prop :=
  ∀ {n N : ℕ}, Odd N → AdmitsValidTuple n N → 2 ^ n - 1 ≤ N

/-- **G3, exceptional-lift form.**  Away from powers of two, no valid
`n`-tuple exists at the one high-valuation modulus where deletion gives only
`2 * B(n-1)` rather than `B(n)`.  `2^log₂(n) ≠ n` is the arithmetic form of
"`n` is not a power of two" used by the paper. -/
def ExceptionalLiftObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2 ^ Nat.log 2 n ≠ n →
    ¬AdmitsValidTuple n (2 * globalBound (n - 1))

/-- G1 plus the proved quotient lemmas gives the load-bearing dichotomy:
halving either preserves the tuple length or deletes exactly one coordinate. -/
theorem admits_half_or_delete_of_g1 (hG1 : CommonTouchedHalfWitnesses)
    {n M : ℕ} (hM : 0 < M) (hvalid : AdmitsValidTuple (n + 1) (2 * M)) :
    AdmitsValidTuple (n + 1) M ∨ AdmitsValidTuple n M := by
  obtain ⟨g, hg⟩ := hvalid
  by_cases hw : ∃ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c
  · right
    obtain ⟨j, hj⟩ := hG1 hM g hg hw
    exact exists_validTuple_half_of_delete (N := 2 * M) (M := M) rfl hM hg j hj
  · left
    apply exists_validTuple_half_of_no_witness (N := 2 * M) (M := M) rfl hM hg
    intro c hc
    exact hw ⟨c, hc⟩

/-- The three roadmap gaps imply the complete stratified lower bound.  This
packages the induction that was previously only described in the handoff.

The exceptional use of G3 is forced precisely when deletion occurs after the
valuation has reached `log₂ n` and `n` is not a power of two.  The induction
then gives `M ≥ globalBound (n-1)`.  Both sides are multiples of `2^log₂ n`,
so either equality holds (excluded by G3) or the next multiple already lies
above the required stratum endpoint. -/
theorem stratum_lower_bound_of_gaps
    (hG1 : CommonTouchedHalfWitnesses)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction) :
    ∀ {n s q : ℕ}, 2 ≤ n → Odd q → AdmitsValidTuple n (2 ^ s * q) →
      stratumBound n s ≤ 2 ^ s * q := by
  intro n s
  induction s generalizing n with
  | zero =>
      intro q hn hq hv
      have h := hG2 hq (by simpa using hv)
      simpa [stratumBound] using h
  | succ s ih =>
      intro q hn hq hv
      let M := 2 ^ s * q
      have hM : 0 < M := mul_pos (pow_pos (by omega) _) (Odd.pos hq)
      have hv2 : AdmitsValidTuple n (2 * M) := by
        simpa [M, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hv
      have hnform : n - 1 + 1 = n := by omega
      have hvform : AdmitsValidTuple (n - 1 + 1) (2 * M) := by
        simpa [hnform] using hv2
      rcases admits_half_or_delete_of_g1 hG1 hM hvform with hkeep | hdelete
      · have hih := ih hn hq (by simpa [hnform, M] using hkeep)
        have hlog : Nat.log 2 n ≤ n - 1 := by
          have := Nat.log_lt_self 2 (by omega : n ≠ 0)
          omega
        have hmin : min s (Nat.log 2 n) ≤ n - 1 :=
          (min_le_right _ _).trans hlog
        have hp_le : 2 ^ min s (Nat.log 2 n) ≤ 2 ^ (n - 1) :=
          Nat.pow_le_pow_right (by omega) hmin
        have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
          calc
            2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
            _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
            _ = 2 * 2 ^ (n - 1) := by omega
        have hhalf : 2 ^ (n - 1) ≤ stratumBound n s := by
          unfold stratumBound
          omega
        calc
          stratumBound n (s + 1) ≤ 2 ^ n := Nat.sub_le _ _
          _ ≤ 2 * stratumBound n s := by omega
          _ ≤ 2 * M := Nat.mul_le_mul_left 2 hih
          _ = 2 ^ (s + 1) * q := by
            simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
      · by_cases hn2 : n = 2
        · subst hn2
          have hlog22 : Nat.log 2 2 = 1 :=
            Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
          have hb : stratumBound 2 (s + 1) = 2 := by
            rw [stratumBound, hlog22, min_eq_right (show 1 ≤ s + 1 by omega)]
            norm_num
          rw [hb]
          calc
            2 ≤ 2 ^ (s + 1) := by
              rw [pow_succ]
              exact Nat.le_mul_of_pos_left 2 (pow_pos (by omega) s)
            _ ≤ 2 ^ (s + 1) * q := Nat.le_mul_of_pos_right _ (Odd.pos hq)
        · have hnprev : 2 ≤ n - 1 := by omega
          have hih := ih hnprev hq (by simpa [M] using hdelete)
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
                exact (hG3 n hn hpow) (by simpa [heq] using hv2)
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

/-- Conditional form of Conjecture 1: once G1, G2, and G3 are proved, every
positive modulus admitting a valid `n`-tuple is at least `globalBound n`. -/
theorem global_lower_bound_of_gaps
    (hG1 : CommonTouchedHalfWitnesses)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N := by
  obtain ⟨s, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hs := stratum_lower_bound_of_gaps hG1 hG2 hG3 hn hq hv
  have hmin : min s (Nat.log 2 n) ≤ Nat.log 2 n := min_le_right _ _
  have hp : 2 ^ min s (Nat.log 2 n) ≤ 2 ^ Nat.log 2 n :=
    Nat.pow_le_pow_right (by omega) hmin
  exact (Nat.sub_le_sub_left hp (2 ^ n)).trans hs

end MinModulus
