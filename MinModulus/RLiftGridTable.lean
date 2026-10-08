import MinModulus.RLiftBits
import MinModulus.RLiftPowerChain
import MinModulus.RLiftSheetChain
import MinModulus.RLiftRival

/-!
# The grid table: the 16 fixed top-window certificates

For `m = w + 6` (any `w`), each of the sixteen residue families of
the R-lift grid table — extras `λ·2^(m_child-4)` for
`λ ∈ {2,3,4,5,6,9,10,12,17,18,20}`, the three `M`-neighborhood
residues, the zero residue and the duplicated top coin — is excluded
by a fixed 2–4 member rival certificate.  Each member pins a sheet-bit
sum; the supports cancel in pairs while the targets sum to `sheet`.
Both sheets of each residue are covered at once, since the extra's own
sheet bit is part of the lift.  Generated from the computational
verifier (`rlift/topgrid.py`, `rlift/final.py`).
-/

namespace MinModulus

open Finset

/-- Integer representatives of a reflected-child parent with an
arbitrary extra `e`. -/
def rliftParentE (m e : ℕ) : Fin (m + 3) → ℕ :=
  Fin.cons 0 (Fin.cons 1
    (Fin.snoc (fun j : Fin m => 2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1))
      e))

lemma rliftParentE_zero (m e : ℕ) : rliftParentE m e ⟨0, by omega⟩ = 0 := rfl

lemma rliftParentE_one (m e : ℕ) : rliftParentE m e ⟨1, by omega⟩ = 1 := rfl

lemma rliftParentE_tau (m e : ℕ) (j : ℕ) (h : j < m) :
    rliftParentE m e (tauC m j h)
      = 2 ^ (m + 1) - 1 - (2 ^ (j + 1) - 1) := by
  have h1 : (tauC m j h) = Fin.succ (Fin.succ ⟨j, by omega⟩) := by
    apply Fin.ext; simp [tauC, Fin.succ]
  rw [h1, rliftParentE, Fin.cons_succ, Fin.cons_succ]
  have h2 : (⟨j, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨j, h⟩ := by
    apply Fin.ext; simp
  rw [h2, Fin.snoc_castSucc]

lemma rliftParentE_last (m e : ℕ) : rliftParentE m e (extraC m) = e := by
  have h1 : extraC m = Fin.succ (Fin.succ (Fin.last m)) := by
    apply Fin.ext; simp [extraC, Fin.succ]
  rw [h1, rliftParentE, Fin.cons_succ, Fin.cons_succ, Fin.snoc_last]

/-! ## Coordinate distinctness helpers -/

lemma tauC_ne_tauC (m : ℕ) {j j' : ℕ} (hj : j < m) (hj' : j' < m)
    (hne : j ≠ j') : tauC m j hj ≠ tauC m j' hj' := by
  intro h
  apply hne
  have := congrArg Fin.val h
  simpa [tauC] using this

lemma tauC_ne_extraC (m : ℕ) {j : ℕ} (hj : j < m) :
    tauC m j hj ≠ extraC m := by
  intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega

lemma mk0_ne_tauC (m : ℕ) {j : ℕ} (hj : j < m) :
    (⟨0, by omega⟩ : Fin (m + 3)) ≠ tauC m j hj := by
  intro h; have := congrArg Fin.val h; simp [tauC] at this

lemma mk1_ne_tauC (m : ℕ) {j : ℕ} (hj : j < m) :
    (⟨1, by omega⟩ : Fin (m + 3)) ≠ tauC m j hj := by
  intro h; have := congrArg Fin.val h; simp [tauC] at this

lemma mk0_ne_mk1 (m : ℕ) :
    (⟨0, by omega⟩ : Fin (m + 3)) ≠ ⟨1, by omega⟩ := by
  intro h; have := congrArg Fin.val h; simp at this

lemma mk0_ne_extraC (m : ℕ) :
    (⟨0, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
  intro h; have := congrArg Fin.val h; simp [extraC] at this

lemma mk1_ne_extraC (m : ℕ) :
    (⟨1, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
  intro h; have := congrArg Fin.val h; simp [extraC] at this

/-! ## Casting exact multiples of `M` -/

lemma gridA_cast_zero (m : ℕ) (A : ℤ) (hA : A % 4 = 0) :
    ((A * (2 ^ (m + 1) - 1) : ℤ) : ZMod (2 ^ (m + 3) - 4)) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, A = 4 * t := ⟨A / 4, by omega⟩
  subst ht
  have hmod : (4 * t * (2 ^ (m + 1) - 1) : ℤ)
      = t * ((2 ^ (m + 3) - 4 : ℕ) : ℤ) := by
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h4 := rlift_modulus m
    push_cast [Nat.cast_sub (by omega : 4 ≤ 2 ^ (m + 3))]
    have hp : ((2 : ℤ)) ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
    rw [hp]
    ring
  rw [hmod, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero]

lemma gridA_cast_sheet (m : ℕ) (A : ℤ) (hA : A % 4 = 2) :
    ((A * (2 ^ (m + 1) - 1) : ℤ) : ZMod (2 ^ (m + 3) - 4)) = sheet m := by
  obtain ⟨t, ht⟩ : ∃ t, A = 4 * t + 2 := ⟨A / 4, by omega⟩
  subst ht
  have hmod : ((4 * t + 2) * (2 ^ (m + 1) - 1) : ℤ)
      = t * ((2 ^ (m + 3) - 4 : ℕ) : ℤ)
        + ((2 * (2 ^ (m + 1) - 1) : ℕ) : ℤ) := by
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h4 := rlift_modulus m
    push_cast [Nat.cast_sub (by omega : 4 ≤ 2 ^ (m + 3)), Nat.cast_sub h1]
    have hp : ((2 : ℤ)) ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
    rw [hp]
    ring
  rw [hmod, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_self, mul_zero, zero_add]
  rfl

/-! ## The sixteen residue families -/

set_option maxHeartbeats 1600000 in
/-- Grid family `lam2`: extra `2 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam2_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (2 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega))
    (mk1_ne_extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
  rw [rliftParentE_one (w + 6) (2 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (2 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 3) (by omega)] at hM0
  have hz0 : (2 * ((1 : ℕ) : ℤ) + ((2 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT2, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM0
  have hc0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = 0 ∨ (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (extraC (w + 6))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    exact c3
  have hP0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = 0 := by
    rcases hc0 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (2 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (2 * 2 ^ (w + 3))] at hM1
  have hz1 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT1, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_2mm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (2 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 3) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  -- member 3
  have hM3 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (2 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (2 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (2 * 2 ^ (w + 3))] at hM3
  have hz3 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz3, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM3
  have hc3 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP3 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc3.resolve_left hM3
  have hcomb : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
      = 0 + sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP0, hP1, hP3, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_c0, hd_e]; simp
  have htsum : 0 + sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (0 + sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam3`: extra `3 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam3_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (3 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 3) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (3 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (3 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((3 * 2 ^ (w + 3) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT3, hnT1, hnT2]
    rw [Nat.cast_sub hbT3, Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 3) (by omega))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_last (w + 6) (3 * 2 ^ (w + 3))] at hM1
  have hz1 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((3 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT2, hnT1, hnT3, hnT4]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 2) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (3 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (3 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_zero (w + 6) (3 * 2 ^ (w + 3))] at hM2
  have hz2 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((3 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT2, hnT4]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP0, hP1, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T4 : β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_T4, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam4`: extra `4 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam4_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (4 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_2mm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (4 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (4 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_zero (w + 6) (4 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((4 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    rw [hnT1]
    rw [Nat.cast_sub hbT1]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c1
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (4 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_last (w + 6) (4 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (4 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (4 * 2 ^ (w + 3))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((4 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_2mm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (4 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (4 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (4 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((4 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP1, hP0, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam5`: extra `5 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam5_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (5 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (5 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (5 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((5 * 2 ^ (w + 3) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT1, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_last (w + 6) (5 * 2 ^ (w + 3))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((5 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT1, hnT2, hnT4]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 3) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (5 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_tau (w + 6) (5 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_zero (w + 6) (5 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((5 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT2, hnT3, hnT4]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT3, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (extraC (w + 6))) (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP2 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP0, hP1, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T4 : β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_T4, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam6`: extra `6 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam6_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (6 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (6 * 2 ^ (w + 3))] at hM0
  have hz0 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((6 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT2, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_last (w + 6) (6 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (6 * 2 ^ (w + 3))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((6 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_2mm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (6 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (6 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (6 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((6 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT2]
    rw [Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c1
  have hP2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP0, hP1, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam9`: extra `9 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam9_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (9 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (9 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (9 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((9 * 2 ^ (w + 3) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT2, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_pppmmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 3) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (9 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_zero (w + 6) (9 * 2 ^ (w + 3))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((9 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT1, hnT2, hnT3, hnT4]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT3, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (extraC (w + 6))) hs2
    have c3 := pair_sum_cases c2 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c4 := pair_sum_cases c3 (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c5 := pair_sum_cases c4 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c5
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_2mm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (9 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_last (w + 6) (9 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((9 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT2, hnT4]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 2) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP2 : (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP1, hP0, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T4 : β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_T4, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam10`: extra `10 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam10_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (10 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_2mm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
  rw [rliftParentE_last (w + 6) (10 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 4) (by omega)] at hM0
  have hz0 : (2 * ((10 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    exact c1
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
  rw [rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (10 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 3) (by omega)] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((10 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT1, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_2mm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (10 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (10 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((10 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 3) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) := by
    rw [hP1, hP0, hP2]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6)) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam12`: extra `12 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam12_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (12 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6))
    (mk0_ne_mk1 (w + 6)).symm
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_one (w + 6) (12 * 2 ^ (w + 3)), rliftParentE_zero (w + 6) (12 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (12 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (12 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (12 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((12 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz0, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM0
  have hc0 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 := by
    rcases hc0 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM0
  -- member 1
  have hM1 := rival_3mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (12 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (12 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (12 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (12 * 2 ^ (w + 3))] at hM1
  have hz1 : (3 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((12 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  have hcomb : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
      = 0 + sheet (w + 6) := by
    rw [hP0, hP1]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 := by
    calc (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_c0, hd_e]; simp
  have htsum : 0 + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = 0 + sheet (w + 6) := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam17`: extra `17 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam17_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (17 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (17 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((17 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT4, hnT1, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT4, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 2) (by omega))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_zero (w + 6) (17 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (17 * 2 ^ (w + 3))] at hM1
  have hz1 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((17 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT2, hnT1, hnT4]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 2) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (17 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (17 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((17 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT4, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT4, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 2) (by omega))) (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP2 : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  -- member 3
  have hM3 := rival_2mm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 2) (by omega)) (extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_one (w + 6) (17 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (17 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_last (w + 6) (17 * 2 ^ (w + 3))] at hM3
  have hz3 : (2 * ((1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((17 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    rw [hnT4]
    rw [Nat.cast_sub hbT4]
    push_cast
    ring
  rw [hz3, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM3
  have hc3 : (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 2) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP3 : (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 := by
    rcases hc3 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM3
  have hcomb : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 := by
    rw [hP0, hP1, hP2, hP3]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T4 : β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 2) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega))) + (β (tauC (w + 6) (w + 2) (by omega)) + β (tauC (w + 6) (w + 2) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T3, hd_T4, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam18`: extra `18 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam18_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (18 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
  rw [rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_last (w + 6) (18 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 3) (by omega)] at hM0
  have hz0 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((18 * 2 ^ (w + 3) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT2, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (18 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (18 * 2 ^ (w + 3))] at hM1
  have hz1 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((18 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT2, hnT1, hnT3]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (18 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (18 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((18 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT3, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT3, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 3) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP2 : (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  -- member 3
  have hM3 := rival_2mm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_one (w + 6) (18 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (18 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (18 * 2 ^ (w + 3))] at hM3
  have hz3 : (2 * ((1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((18 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT3]
    rw [Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz3, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM3
  have hc3 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 3) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP3 : (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 := by
    rcases hc3 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM3
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 := by
    rw [hP0, hP1, hP2, hP3]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `lam20`: extra `20 * 2 ^ (w + 3)` (either sheet) is excluded. -/
theorem rliftGrid_lam20_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (20 * 2 ^ (w + 3)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 2) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_last (w + 6) (20 * 2 ^ (w + 3))] at hM0
  have hz0 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((20 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT4, hnT2, hnT1, hnT3]
    rw [Nat.cast_sub hbT4, Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_zero (w + 6) (20 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (20 * 2 ^ (w + 3))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((20 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT1, hnT2]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_22mmmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 2) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (tauC (w + 6) (w + 3) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 5) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 2) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 3) (by omega), rliftParentE_zero (w + 6) (20 * 2 ^ (w + 3)), rliftParentE_last (w + 6) (20 * 2 ^ (w + 3))] at hM2
  have hz2 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + 2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 2 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 3 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((20 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT4 : (2 : ℕ) ^ ((w + 2) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT4 : 1 ≤ (2 : ℕ) ^ ((w + 2) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT4 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 2) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 2) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT3 : (2 : ℕ) ^ ((w + 3) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT3 : 1 ≤ (2 : ℕ) ^ ((w + 3) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT3 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 3) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 3) + 1) := by omega
    rw [hnT1, hnT4, hnT2, hnT3]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT4, Nat.cast_sub hbT2, Nat.cast_sub hbT3]
    push_cast
    ring
  rw [hz2, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM2
  have hc2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (tauC (w + 6) (w + 3) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc2.resolve_left hM2
  -- member 3
  have hM3 := rival_2mm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_one (w + 6) (20 * 2 ^ (w + 3)), rliftParentE_tau (w + 6) (20 * 2 ^ (w + 3)) (w + 4) (by omega), rliftParentE_last (w + 6) (20 * 2 ^ (w + 3))] at hM3
  have hz3 : (2 * ((1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((20 * 2 ^ (w + 3) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    rw [hnT2]
    rw [Nat.cast_sub hbT2]
    push_cast
    ring
  rw [hz3, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM3
  have hc3 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    exact c1
  have hP3 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 := by
    rcases hc3 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM3
  have hcomb : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 := by
    rw [hP0, hP1, hP2, hP3]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T3 : β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 3) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (tauC (w + 6) (w + 3) (by omega)) + β (tauC (w + 6) (w + 3) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_T3, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6)
        = (sheet (w + 6) + sheet (w + 6) + sheet (w + 6) + 0) - (sheet (w + 6) + sheet (w + 6)) := by abel
      _ = 0 - 0 := by rw [htsum, h2s]
      _ = 0 := by simp
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `M`: extra `2 ^ (w + 6 + 1) - 1` (either sheet) is excluded. -/
theorem rliftGrid_M_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (2 ^ (w + 6 + 1) - 1) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (⟨1, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk1_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_mk1 (w + 6))
  rw [rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1) (w + 4) (by omega), rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1), rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1) (w + 5) (by omega), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1)] at hM0
  have hz0 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      = ((2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    rw [hnT2, hnT1]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub h1]
    push_cast
    ring
  rw [hz0, gridA_cast_sheet (w + 6) (2) (by decide)] at hM0
  have hc0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (extraC (w + 6))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    rcases hc0 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 5) (by omega)) (⟨1, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_mk1 (w + 6))
    (mk0_ne_extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1) (w + 4) (by omega), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1), rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1) (w + 5) (by omega), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1), rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1)] at hM1
  have hz1 : (2 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    rw [hnT2, hnT1]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hbT1, Nat.cast_sub h1]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  have hcomb : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
      = 0 + sheet (w + 6) := by
    rw [hP0, hP1]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_u : β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 := by
    calc (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_c0, hd_u, hd_e]; simp
  have htsum : 0 + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = 0 + sheet (w + 6) := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `Mq`: extra `2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)` (either sheet) is excluded. -/
theorem rliftGrid_Mq_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_2mm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
  rw [rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)), rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)) (w + 5) (by omega), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5))] at hM0
  have hz0 : (2 * ((2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hne : (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ)
        = 2 ^ (w + 6 + 1) + 2 ^ (w + 5) - 1 := by omega
    have hXe : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) + 2 ^ (w + 5) := by omega
    rw [hnT1, hne]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hXe]
    push_cast
    ring
  rw [hz0, gridA_cast_sheet (w + 6) (2) (by decide)] at hM0
  have hc0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c1
  have hP0 : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    rcases hc0 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (w + 4) (by omega)) (⟨1, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk1_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)) (w + 5) (by omega), rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)) (w + 4) (by omega), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)), rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) - ((1 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hne : (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ)
        = 2 ^ (w + 6 + 1) + 2 ^ (w + 5) - 1 := by omega
    have hXe : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) + 2 ^ (w + 5) := by omega
    rw [hnT1, hnT2, hne]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbT2, Nat.cast_sub hXe]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (tauC (w + 6) (w + 4) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  -- member 2
  have hM2 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 4) (by omega)) (extraC (w + 6)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (⟨1, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk1_ne_extraC (w + 6)).symm
    (mk0_ne_mk1 (w + 6))
  rw [rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)) (w + 4) (by omega), rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5)), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5))] at hM2
  have hz2 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 4 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      = ((2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT2 : (2 : ℕ) ^ ((w + 4) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT2 : 1 ≤ (2 : ℕ) ^ ((w + 4) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 4) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 4) + 1) := by omega
    have hne : (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 5) : ℕ)
        = 2 ^ (w + 6 + 1) + 2 ^ (w + 5) - 1 := by omega
    have hXe : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) + 2 ^ (w + 5) := by omega
    rw [hnT2, hne]
    rw [Nat.cast_sub hbT2, Nat.cast_sub hXe]
    push_cast
    ring
  rw [hz2, gridA_cast_sheet (w + 6) (2) (by decide)] at hM2
  have hc2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 4) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP2 : (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    rcases hc2 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM2
  have hcomb : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)))
      = 0 + sheet (w + 6) + 0 := by
    rw [hP1, hP2, hP0]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_T2 : β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_u : β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 4) (by omega)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (w + 4) (by omega)) + β (tauC (w + 6) (w + 4) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_T2, hd_c0, hd_u, hd_e]; simp
  have htsum : 0 + sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = 0 + sheet (w + 6) + 0 := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `Mh`: extra `2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)` (either sheet) is excluded. -/
theorem rliftGrid_Mh_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_3mmm_ne hβ2 hg hv
    (extraC (w + 6)) (tauC (w + 6) (w + 5) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (⟨1, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk1_ne_extraC (w + 6)).symm
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_mk1 (w + 6))
  rw [rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)), rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)) (w + 5) (by omega), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6))] at hM0
  have hz0 : (3 * ((2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      = ((4 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hne : (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6) : ℕ)
        = 2 ^ (w + 6 + 1) + 2 ^ (w + 6) - 1 := by omega
    have hXe : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) + 2 ^ (w + 6) := by omega
    rw [hnT1, hne]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hXe]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (4) (by decide), zero_add] at hM0
  have hc0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (extraC (w + 6))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP0 : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_ppmm_ne hβ2 hg hv
    (tauC (w + 6) (w + 5) (by omega)) (extraC (w + 6)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (⟨1, by omega⟩ : Fin (w + 6 + 3))
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (mk1_ne_tauC (w + 6) (by omega)).symm
    (mk0_ne_extraC (w + 6)).symm
    (mk1_ne_extraC (w + 6)).symm
    (mk0_ne_mk1 (w + 6))
  rw [rliftParentE_tau (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)) (w + 5) (by omega), rliftParentE_last (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)), rliftParentE_zero (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6)), rliftParentE_one (w + 6) (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6))] at hM1
  have hz1 : (((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      = ((2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hne : (2 ^ (w + 6 + 1) - 1 + 2 ^ (w + 6) : ℕ)
        = 2 ^ (w + 6 + 1) + 2 ^ (w + 6) - 1 := by omega
    have hXe : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) + 2 ^ (w + 6) := by omega
    rw [hnT1, hne]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hXe]
    push_cast
    ring
  rw [hz1, gridA_cast_sheet (w + 6) (2) (by decide)] at hM1
  have hc1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 ∨ (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (w + 5) (by omega))) (hβ (extraC (w + 6))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (⟨1, by omega⟩ : Fin (w + 6 + 3))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    rcases hc1 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM1
  have hcomb : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)))
      = sheet (w + 6) + 0 := by
    rw [hP0, hP1]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_u : β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) = 0 := by
    calc (β (extraC (w + 6)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (tauC (w + 6) (w + 5) (by omega)) + β (extraC (w + 6)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (⟨1, by omega⟩ : Fin (w + 6 + 3)) + β (⟨1, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_c0, hd_u, hd_e]; simp
  have htsum : sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = sheet (w + 6) + 0 := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `zero`: extra `0` (either sheet) is excluded. -/
theorem rliftGrid_zero_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (0) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_3mmm_ne hβ2 hg hv
    (tauC (w + 6) (0) (by omega)) (tauC (w + 6) (1) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_tau (w + 6) (0) (0) (by omega), rliftParentE_tau (w + 6) (0) (1) (by omega), rliftParentE_zero (w + 6) (0), rliftParentE_last (w + 6) (0)] at hM0
  have hz0 : (3 * ((2 ^ (w + 6 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (1 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbt1 : (2 : ℕ) ^ ((0) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt1 : 1 ≤ (2 : ℕ) ^ ((0) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((0) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((0) + 1) := by omega
    have hbt2 : (2 : ℕ) ^ ((1) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt2 : 1 ≤ (2 : ℕ) ^ ((1) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((1) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((1) + 1) := by omega
    rw [hnt1, hnt2]
    rw [Nat.cast_sub hbt1, Nat.cast_sub hbt2]
    push_cast
    ring
  rw [hz0, gridA_cast_sheet (w + 6) (2) (by decide)] at hM0
  have hc0 : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (0) (by omega))) (hβ (tauC (w + 6) (1) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 := by
    rcases hc0 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM0
  -- member 1
  have hM1 := rival_21mmm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (1) (by omega)) (tauC (w + 6) (0) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk0_ne_mk1 (w + 6)).symm
    (mk1_ne_extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_one (w + 6) (0), rliftParentE_tau (w + 6) (0) (1) (by omega), rliftParentE_tau (w + 6) (0) (0) (by omega), rliftParentE_zero (w + 6) (0), rliftParentE_last (w + 6) (0)] at hM1
  have hz1 : (2 * ((1 : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (1 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbt2 : (2 : ℕ) ^ ((1) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt2 : 1 ≤ (2 : ℕ) ^ ((1) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt2 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((1) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((1) + 1) := by omega
    have hbt1 : (2 : ℕ) ^ ((0) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt1 : 1 ≤ (2 : ℕ) ^ ((0) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((0) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((0) + 1) := by omega
    rw [hnt2, hnt1]
    rw [Nat.cast_sub hbt2, Nat.cast_sub hbt1]
    push_cast
    ring
  rw [hz1, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM1
  have hc1 : (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (1) (by omega))) (hβ (tauC (w + 6) (0) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc1.resolve_left hM1
  have hcomb : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
      = 0 + sheet (w + 6) := by
    rw [hP0, hP1]
  have hd_t1 : β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (0) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_t2 : β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (1) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (1) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (0) (by omega))) + (β (tauC (w + 6) (1) (by omega)) + β (tauC (w + 6) (1) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_t1, hd_t2, hd_c0, hd_e]; simp
  have htsum : 0 + sheet (w + 6) = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = 0 + sheet (w + 6) := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

set_option maxHeartbeats 1600000 in
/-- Grid family `dup`: extra `2 ^ (w + 6)` (either sheet) is excluded. -/
theorem rliftGrid_dup_not_valid (w : ℕ)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) (2 ^ (w + 6)) i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hs2 := two_nsmul_sheet (w + 6)
  -- member 0
  have hM0 := rival_21mmm_ne hβ2 hg hv
    (⟨1, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (0) (by omega)) (tauC (w + 6) (w + 5) (by omega)) (⟨0, by omega⟩ : Fin (w + 6 + 3)) (extraC (w + 6))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk1_ne_tauC (w + 6) (by omega))
    (mk0_ne_mk1 (w + 6)).symm
    (mk1_ne_extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega)).symm
    (tauC_ne_extraC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
  rw [rliftParentE_one (w + 6) (2 ^ (w + 6)), rliftParentE_tau (w + 6) (2 ^ (w + 6)) (0) (by omega), rliftParentE_tau (w + 6) (2 ^ (w + 6)) (w + 5) (by omega), rliftParentE_zero (w + 6) (2 ^ (w + 6)), rliftParentE_last (w + 6) (2 ^ (w + 6))] at hM0
  have hz0 : (2 * ((1 : ℕ) : ℤ) + ((2 ^ (w + 6 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - ((2 ^ (w + 6) : ℕ) : ℤ))
      = ((0 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbt1 : (2 : ℕ) ^ ((0) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt1 : 1 ≤ (2 : ℕ) ^ ((0) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((0) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((0) + 1) := by omega
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    rw [hnt1, hnT1]
    rw [Nat.cast_sub hbt1, Nat.cast_sub hbT1]
    push_cast
    ring
  rw [hz0, gridA_cast_zero (w + 6) (0) (by decide), zero_add] at hM0
  have hc0 : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = 0 ∨ (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (tauC (w + 6) (0) (by omega))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP0 : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) = sheet (w + 6) := by
    exact hc0.resolve_left hM0
  -- member 1
  have hM1 := rival_3mmm_ne hβ2 hg hv
    (⟨0, by omega⟩ : Fin (w + 6 + 3)) (tauC (w + 6) (w + 5) (by omega)) (tauC (w + 6) (0) (by omega)) (extraC (w + 6))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_tauC (w + 6) (by omega))
    (mk0_ne_extraC (w + 6))
    (tauC_ne_tauC (w + 6) (by omega) (by omega) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
    (tauC_ne_extraC (w + 6) (by omega))
  rw [rliftParentE_zero (w + 6) (2 ^ (w + 6)), rliftParentE_tau (w + 6) (2 ^ (w + 6)) (w + 5) (by omega), rliftParentE_tau (w + 6) (2 ^ (w + 6)) (0) (by omega), rliftParentE_last (w + 6) (2 ^ (w + 6))] at hM1
  have hz1 : (3 * ((0 : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (w + 5 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ) - ((2 ^ (w + 6) : ℕ) : ℤ))
      = ((-2 : ℤ)) * (2 ^ (w + 6 + 1) - 1) := by
    have h1 : 1 ≤ (2 : ℕ) ^ (w + 6 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hbT1 : (2 : ℕ) ^ ((w + 5) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpT1 : 1 ≤ (2 : ℕ) ^ ((w + 5) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnT1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((w + 5) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((w + 5) + 1) := by omega
    have hbt1 : (2 : ℕ) ^ ((0) + 1) ≤ 2 ^ (w + 6 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpt1 : 1 ≤ (2 : ℕ) ^ ((0) + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnt1 : (2 ^ (w + 6 + 1) - 1 - (2 ^ ((0) + 1) - 1) : ℕ)
        = 2 ^ (w + 6 + 1) - 2 ^ ((0) + 1) := by omega
    rw [hnT1, hnt1]
    rw [Nat.cast_sub hbT1, Nat.cast_sub hbt1]
    push_cast
    ring
  rw [hz1, gridA_cast_sheet (w + 6) (-2) (by decide)] at hM1
  have hc1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6))) = 0 ∨ (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6))) = sheet (w + 6) := by
    have c1 := pair_sum_cases (hβ (⟨0, by omega⟩ : Fin (w + 6 + 3))) (hβ (tauC (w + 6) (w + 5) (by omega))) hs2
    have c2 := pair_sum_cases c1 (hβ (tauC (w + 6) (0) (by omega))) hs2
    have c3 := pair_sum_cases c2 (hβ (extraC (w + 6))) hs2
    exact c3
  have hP1 : (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6))) = 0 := by
    rcases hc1 with h0 | hS
    · exact h0
    · exact absurd (by rw [hS, ← two_nsmul]; exact two_nsmul_sheet _) hM1
  have hcomb : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6)))
      = sheet (w + 6) + 0 := by
    rw [hP0, hP1]
  have hd_T1 : β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_t1 : β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (0) (by omega)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_c0 : β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hd_e : β (extraC (w + 6)) + β (extraC (w + 6)) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hzero : (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6))) = 0 := by
    calc (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (w + 5) (by omega)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (extraC (w + 6))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (0) (by omega)) + β (extraC (w + 6)))
        = (β (tauC (w + 6) (w + 5) (by omega)) + β (tauC (w + 6) (w + 5) (by omega))) + (β (tauC (w + 6) (0) (by omega)) + β (tauC (w + 6) (0) (by omega))) + (β (⟨0, by omega⟩ : Fin (w + 6 + 3)) + β (⟨0, by omega⟩ : Fin (w + 6 + 3))) + (β (extraC (w + 6)) + β (extraC (w + 6))) := by abel
      _ = 0 := by rw [hd_T1, hd_t1, hd_c0, hd_e]; simp
  have htsum : sheet (w + 6) + 0 = 0 := hcomb.symm.trans hzero
  have h2s : sheet (w + 6) + sheet (w + 6) = 0 := by
    rw [← two_nsmul]; exact two_nsmul_sheet _
  have hfin : sheet (w + 6) = 0 := by
    calc sheet (w + 6) = sheet (w + 6) + 0 := by abel
      _ = 0 := htsum
  exact sheet_ne_zero (w + 6) hfin

end MinModulus
