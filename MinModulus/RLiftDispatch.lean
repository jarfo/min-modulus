import MinModulus.RLiftSpecials
import MinModulus.RLiftSheetChain

/-!
# The extra dispatch: every extra is excluded

For every extra value `e` and every lift, the parent of the reflected child
is invalid: the derived target `u` either has a master certificate, or the
residue of `e` lands on the sheet chain, the power chain, one of the sixteen
grid families, or one of the three specials.
-/

set_option maxHeartbeats 1600000

namespace MinModulus

open Finset

/-! ## Modular helpers -/

/-- Every extra has a derived target: `u < M` with `2u + e ≡ 0 (mod M)`. -/
lemma exists_derived_target (Mv e : ℕ) (hModd : Odd Mv) :
    ∃ u, u < Mv ∧ (2 * u + e) % Mv = 0 := by
  obtain ⟨c, hc⟩ := hModd
  have hM1 : 1 ≤ Mv := by omega
  have hda := Nat.div_add_mod e Mv
  by_cases h0 : e % Mv = 0
  · exact ⟨0, by omega, by simp [h0]⟩
  · rcases Nat.even_or_odd (e % Mv) with ⟨c2, hc2⟩ | ⟨c2, hc2⟩
    · have hsM : e % Mv < Mv := Nat.mod_lt _ (by omega)
      refine ⟨Mv - c2, by omega, ?_⟩
      have hkey : 2 * (Mv - c2) + e = Mv * (e / Mv + 2) := by
        have hr : Mv * (e / Mv + 2) = Mv * (e / Mv) + 2 * Mv := by ring
        omega
      rw [hkey]
      exact Nat.mul_mod_right _ _
    · have hsM : e % Mv < Mv := Nat.mod_lt _ (by omega)
      refine ⟨c - c2, by omega, ?_⟩
      have hkey : 2 * (c - c2) + e = Mv * (e / Mv + 1) := by
        have hr : Mv * (e / Mv + 1) = Mv * (e / Mv) + Mv := by ring
        omega
      rw [hkey]
      exact Nat.mul_mod_right _ _

/-- Two solutions of the same congruence `2u + · ≡ 0` have equal residues. -/
lemma e_mod_eq {Mv u e r : ℕ} (hr : r < Mv)
    (hu : (2 * u + r) % Mv = 0) (hgM : (2 * u + e) % Mv = 0) :
    e % Mv = r := by
  have h1 : (2 * u + e) ≡ (2 * u + r) [MOD Mv] := by
    unfold Nat.ModEq
    rw [hgM, hu]
  have h2 : e ≡ r [MOD Mv] := Nat.ModEq.add_left_cancel' (2 * u) h1
  unfold Nat.ModEq at h2
  rw [Nat.mod_eq_of_lt hr] at h2
  exact h2

/-- Lift a residue mod `M` to the two residues mod `2M`. -/
lemma mod_double_split {Mv e r : ℕ} (_hM : 0 < Mv) (hr : r < Mv)
    (he : e % Mv = r) :
    e % (2 * Mv) = r ∨ e % (2 * Mv) = r + Mv := by
  have hda := Nat.div_add_mod e Mv
  rw [he] at hda
  rcases Nat.even_or_odd (e / Mv) with ⟨c, hc⟩ | ⟨c, hc⟩
  · left
    have hkey : e = 2 * Mv * c + r := by
      have h2 : Mv * (e / Mv) = 2 * Mv * c := by rw [hc]; ring
      omega
    rw [hkey, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · right
    have hkey : e = 2 * Mv * c + (r + Mv) := by
      have h2 : Mv * (e / Mv) = 2 * Mv * c + Mv := by rw [hc]; ring
      omega
    rw [hkey, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)

/-- The residue of an even number modulo an even modulus is even. -/
lemma even_mod_double {Mv e : ℕ} (he : Even e) : Even (e % (2 * Mv)) := by
  rcases Nat.eq_zero_or_pos Mv with rfl | hM
  · simpa using he
  have hda := Nat.div_add_mod e (2 * Mv)
  obtain ⟨c, hc⟩ := he
  have h2 : 2 * Mv * (e / (2 * Mv)) = 2 * (Mv * (e / (2 * Mv))) := by ring
  exact ⟨c - Mv * (e / (2 * Mv)), by omega⟩

/-- Retarget the parent's extra to its canonical representative, absorbing
the `2M`-multiple into the sheet bits. -/
lemma retarget (L e E t : ℕ)
    (ht : e = E + 2 * (2 ^ (L + 1) - 1) * t)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ∃ β' : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4),
      (∀ i, β' i = 0 ∨ β' i = sheet L) ∧
      ∀ i, g i = ((rliftParentE L E i : ℕ) : ZMod (2 ^ (L + 3) - 4))
          + β' i := by
  classical
  set Δ : ZMod (2 ^ (L + 3) - 4) :=
    ((2 * (2 ^ (L + 1) - 1) * t : ℕ) : ZMod (2 ^ (L + 3) - 4)) with hΔ
  have hΔmem : Δ = 0 ∨ Δ = sheet L := by
    have h := intCast_two_mul_M_mul L (t : ℤ)
    have hcast : Δ = ((2 * ((2 : ℤ) ^ (L + 1) - 1) * (t : ℤ) : ℤ) :
        ZMod (2 ^ (L + 3) - 4)) := by
      rw [hΔ, ← Int.cast_natCast]
      congr 1
      push_cast [mersenne_cast]
      ring
    rw [hcast]
    exact h
  have hlast : Fin.succ (Fin.succ (Fin.last L)) = extraC L := by
    apply Fin.ext; simp [extraC, Fin.succ]
  have hsplit : ∀ i : Fin (L + 3), i = extraC L ∨
      rliftParentE L e i = rliftParentE L E i := by
    intro i
    refine Fin.cases ?_ (fun i1 => ?_) i
    · right; rfl
    · refine Fin.cases ?_ (fun i2 => ?_) i1
      · right; rfl
      · refine Fin.lastCases ?_ (fun j => ?_) i2
        · left; exact hlast
        · right
          rw [rliftParentE, rliftParentE, Fin.cons_succ, Fin.cons_succ,
            Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc,
            Fin.snoc_castSucc]
  have hcongr : ∀ i : Fin (L + 3), i ≠ extraC L →
      rliftParentE L e i = rliftParentE L E i := by
    intro i hi
    rcases hsplit i with h | h
    · exact absurd h hi
    · exact h
  refine ⟨fun i => if i = extraC L then Δ + β i else β i,
    fun i => ?_, fun i => ?_⟩
  · show (if i = extraC L then Δ + β i else β i) = 0 ∨
      (if i = extraC L then Δ + β i else β i) = sheet L
    by_cases hi : i = extraC L
    · rw [if_pos hi]
      rcases hΔmem with hΔ0 | hΔs <;> rcases hβ i with hβ0 | hβs
      · left; rw [hΔ0, hβ0, add_zero]
      · right; rw [hΔ0, hβs, zero_add]
      · right; rw [hΔs, hβ0, add_zero]
      · left
        rw [hΔs, hβs, ← two_nsmul]
        exact two_nsmul_sheet L
    · rw [if_neg hi]
      exact hβ i
  · show g i = ((rliftParentE L E i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + (if i = extraC L then Δ + β i else β i)
    by_cases hi : i = extraC L
    · rw [if_pos hi, hi, hg (extraC L), rliftParentE_last,
        rliftParentE_last]
      rw [ht, Nat.cast_add, hΔ]
      ring
    · rw [if_neg hi, hg i, hcongr i hi]

/-! ## The complete extra dispatch -/

/-- **Every extra is excluded.**  For every `e : ℕ` and every sheeted lift,
the parent of the reflected child with extra `e` is invalid modulo `4M`. -/
theorem rliftParentE_not_valid_all (w e : ℕ) (hw2 : 2 ≤ w) (hwe : Even w)
    {g β : Fin (w + 6 + 3) → ZMod (2 ^ (w + 6 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet (w + 6))
    (hg : ∀ i, g i = ((rliftParentE (w + 6) e i : ℕ) :
        ZMod (2 ^ (w + 6 + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  have hp0 : (2 : ℕ) ^ (w + 2) * 2 = 2 ^ (w + 3) := by rw [← pow_succ]
  have hp2 : (2 : ℕ) ^ (w + 3) * 2 = 2 ^ (w + 4) := by rw [← pow_succ]
  have hp3 : (2 : ℕ) ^ (w + 4) * 2 = 2 ^ (w + 5) := by rw [← pow_succ]
  have hp4 : (2 : ℕ) ^ (w + 5) * 2 = 2 ^ (w + 6) := by rw [← pow_succ]
  have hp5 : (2 : ℕ) ^ (w + 6) * 2 = 2 ^ (w + 7) := by rw [← pow_succ]
  have hp1 : (1 : ℕ) ≤ 2 ^ (w + 2) := Nat.one_le_pow _ _ (by norm_num)
  have hwe6 : Even (w + 6) := by
    obtain ⟨c, hc⟩ := hwe
    exact ⟨c + 3, by omega⟩
  set Mv : ℕ := 2 ^ (w + 7) - 1 with hMv
  have hModd : Odd Mv := ⟨2 ^ (w + 6) - 1, by omega⟩
  obtain ⟨u, hu, hgM⟩ := exists_derived_target Mv e hModd
  by_cases hex : (u = 0 ∨ u = 2 ^ (w + 7) - 2 ∨ u = 2 ^ (w + 6) - 1
      ∨ u = 2 ^ (w + 6) + 2 ^ (w + 5) - 1 ∨ u = 7 * 2 ^ (w + 4) - 1
      ∨ (Even e ∧
          (u = 2 ^ (w + 5) - 1 ∨ u = 3 * 2 ^ (w + 4) - 1
           ∨ u = 5 * 2 ^ (w + 4) - 1
           ∨ u = 7 * 2 ^ (w + 3) - 1 ∨ u = 11 * 2 ^ (w + 3) - 1
           ∨ u = 13 * 2 ^ (w + 3) - 1 ∨ u = 15 * 2 ^ (w + 3) - 1
           ∨ u = 15 * 2 ^ (w + 2) - 1 ∨ u = 23 * 2 ^ (w + 2) - 1
           ∨ u = 27 * 2 ^ (w + 2) - 1 ∨ u = 29 * 2 ^ (w + 2) - 1
           ∨ (w + 6 = 8 ∧ u = 506))))
  case neg =>
    exact master_not_valid (w + 6) e u (by omega) hu hgM hex hβ hg
  rcases hex with h | h | h | h | h | ⟨hee, hin⟩
  · -- u = 0: grid zero / grid M
    subst h
    have hr : e % Mv = 0 :=
      e_mod_eq (by omega) (by simp) hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e 0 (e / (2 * Mv))
        (show e = 0 + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      exact rliftGrid_zero_not_valid w hβ' hg'
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (2 ^ (w + 7) - 1)
        (e / (2 * Mv))
        (show e = (2 ^ (w + 7) - 1) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_M_not_valid w hβ' hg'
  · -- u = M − 1: the e ≡ 2 (mod M) special
    subst h
    have huc : (2 * (2 ^ (w + 7) - 2) + 2) % Mv = 0 := by
      have h2 : 2 * (2 ^ (w + 7) - 2) + 2 = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 2 := e_mod_eq (by omega) huc hgM
    exact special_modM_two_not_valid (w + 6) e (by omega) hr hβ hg
  · -- u = 2^{m−1} − 1: sheet chain / power chain
    subst h
    have huc : (2 * (2 ^ (w + 6) - 1) + 1) % Mv = 0 := by
      have h2 : 2 * (2 ^ (w + 6) - 1) + 1 = Mv * 1 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 1
    have hr : e % Mv = 1 := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e 1 (e / (2 * Mv))
        (show e = 1 + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      have hsh : rliftParentSheet (w + 6) = rliftParentE (w + 6) 1 := rfl
      rw [← hsh] at hg'
      exact rliftParentSheet_not_valid (by omega) hwe6 hβ' hg'
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (2 ^ (w + 7))
        (e / (2 * Mv))
        (show e = 2 ^ (w + 7) + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      have hpw : rliftParent (w + 6) = rliftParentE (w + 6) (2 ^ (w + 7)) :=
        rfl
      rw [← hpw] at hg'
      exact rliftParent_power_not_valid (by omega) hwe6 hβ' hg'
  · -- u = 3·2^{m−2} − 1: grid dup / grid Mh
    subst h
    have huc : (2 * (2 ^ (w + 6) + 2 ^ (w + 5) - 1) + 2 ^ (w + 6)) % Mv
        = 0 := by
      have h2 : 2 * (2 ^ (w + 6) + 2 ^ (w + 5) - 1) + 2 ^ (w + 6)
          = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 2 ^ (w + 6) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (2 ^ (w + 6))
        (e / (2 * Mv))
        (show e = 2 ^ (w + 6) + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      exact rliftGrid_dup_not_valid w hβ' hg'
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e
        (2 ^ (w + 7) - 1 + 2 ^ (w + 6)) (e / (2 * Mv))
        (show e = (2 ^ (w + 7) - 1 + 2 ^ (w + 6))
            + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      exact rliftGrid_Mh_not_valid w hβ' hg'
  · -- u = 7·2^{m−3} − 1: grid lam4 / grid Mq
    subst h
    have huc : (2 * (7 * 2 ^ (w + 4) - 1) + 2 ^ (w + 5)) % Mv = 0 := by
      have h2 : 2 * (7 * 2 ^ (w + 4) - 1) + 2 ^ (w + 5) = Mv * 2 := by
        omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 2 ^ (w + 5) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (4 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 4 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam4_not_valid w hβ' hg'
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e
        (2 ^ (w + 7) - 1 + 2 ^ (w + 5)) (e / (2 * Mv))
        (show e = (2 ^ (w + 7) - 1 + 2 ^ (w + 5))
            + 2 * Mv * (e / (2 * Mv)) by omega) hβ hg
      exact rliftGrid_Mq_not_valid w hβ' hg'
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h
  · -- u = 2^{m−2} − 1: the 3·2^{m−1} special
    subst h
    have huc : (2 * (2 ^ (w + 5) - 1) + (2 ^ (w + 6) + 1)) % Mv = 0 := by
      have h2 : 2 * (2 ^ (w + 5) - 1) + (2 ^ (w + 6) + 1) = Mv * 1 := by
        omega
      rw [h2]
      exact Nat.mul_mod_right Mv 1
    have hr : e % Mv = 2 ^ (w + 6) + 1 := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
    · have hres : e % (2 * Mv) = 3 * 2 ^ (w + 6) := by omega
      exact special_threeHalf_not_valid (w + 6) e (by omega) hres hβ hg
  · -- u = 3 * 2 ^ (w + 4) - 1: residue 2 ^ (w + 5) + 1 (odd), even sheet member
    subst h
    have huc : (2 * (3 * 2 ^ (w + 4) - 1) + (2 ^ (w + 5) + 1)) % Mv = 0 := by
      have h2 : 2 * (3 * 2 ^ (w + 4) - 1) + (2 ^ (w + 5) + 1) = Mv * 1 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 1
    have hr : e % Mv = 2 ^ (w + 5) + 1 := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (20 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 20 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam20_not_valid w hβ' hg'
  · -- u = 5 * 2 ^ (w + 4) - 1: residue 12 * 2 ^ (w + 3), grid lam12
    subst h
    have huc : (2 * (5 * 2 ^ (w + 4) - 1) + (12 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (5 * 2 ^ (w + 4) - 1) + (12 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 12 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (12 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 12 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam12_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 7 * 2 ^ (w + 3) - 1: residue 2 ^ (w + 4) + 1 (odd), even sheet member
    subst h
    have huc : (2 * (7 * 2 ^ (w + 3) - 1) + (2 ^ (w + 4) + 1)) % Mv = 0 := by
      have h2 : 2 * (7 * 2 ^ (w + 3) - 1) + (2 ^ (w + 4) + 1) = Mv * 1 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 1
    have hr : e % Mv = 2 ^ (w + 4) + 1 := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (18 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 18 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam18_not_valid w hβ' hg'
  · -- u = 11 * 2 ^ (w + 3) - 1: residue 10 * 2 ^ (w + 3), grid lam10
    subst h
    have huc : (2 * (11 * 2 ^ (w + 3) - 1) + (10 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (11 * 2 ^ (w + 3) - 1) + (10 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 10 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (10 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 10 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam10_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 13 * 2 ^ (w + 3) - 1: residue 6 * 2 ^ (w + 3), grid lam6
    subst h
    have huc : (2 * (13 * 2 ^ (w + 3) - 1) + (6 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (13 * 2 ^ (w + 3) - 1) + (6 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 6 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (6 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 6 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam6_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 15 * 2 ^ (w + 3) - 1: residue 2 * 2 ^ (w + 3), grid lam2
    subst h
    have huc : (2 * (15 * 2 ^ (w + 3) - 1) + (2 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (15 * 2 ^ (w + 3) - 1) + (2 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 2 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (2 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 2 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam2_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 15 * 2 ^ (w + 2) - 1: residue 2 ^ (w + 3) + 1 (odd), even sheet member
    subst h
    have huc : (2 * (15 * 2 ^ (w + 2) - 1) + (2 ^ (w + 3) + 1)) % Mv = 0 := by
      have h2 : 2 * (15 * 2 ^ (w + 2) - 1) + (2 ^ (w + 3) + 1) = Mv * 1 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 1
    have hr : e % Mv = 2 ^ (w + 3) + 1 := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (17 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 17 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam17_not_valid w hβ' hg'
  · -- u = 23 * 2 ^ (w + 2) - 1: residue 9 * 2 ^ (w + 3), grid lam9
    subst h
    have huc : (2 * (23 * 2 ^ (w + 2) - 1) + (9 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (23 * 2 ^ (w + 2) - 1) + (9 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 9 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (9 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 9 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam9_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 27 * 2 ^ (w + 2) - 1: residue 5 * 2 ^ (w + 3), grid lam5
    subst h
    have huc : (2 * (27 * 2 ^ (w + 2) - 1) + (5 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (27 * 2 ^ (w + 2) - 1) + (5 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 5 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (5 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 5 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam5_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- u = 29 * 2 ^ (w + 2) - 1: residue 3 * 2 ^ (w + 3), grid lam3
    subst h
    have huc : (2 * (29 * 2 ^ (w + 2) - 1) + (3 * 2 ^ (w + 3))) % Mv = 0 := by
      have h2 : 2 * (29 * 2 ^ (w + 2) - 1) + (3 * 2 ^ (w + 3)) = Mv * 2 := by omega
      rw [h2]
      exact Nat.mul_mod_right Mv 2
    have hr : e % Mv = 3 * 2 ^ (w + 3) := e_mod_eq (by omega) huc hgM
    rcases mod_double_split (by omega) (by omega) hr with h2 | h2
    · have hda := Nat.div_add_mod e (2 * Mv)
      rw [h2] at hda
      obtain ⟨β', hβ', hg'⟩ := retarget (w + 6) e (3 * 2 ^ (w + 3))
        (e / (2 * Mv))
        (show e = 3 * 2 ^ (w + 3) + 2 * Mv * (e / (2 * Mv)) by omega)
        hβ hg
      exact rliftGrid_lam3_not_valid w hβ' hg'
    · exfalso
      have hpar := Nat.even_iff.mp (even_mod_double (Mv := Mv) hee)
      rw [h2] at hpar
      omega
  · -- the sporadic (m, e) = (9, 10) family
    obtain ⟨hw8, hu506⟩ := h
    subst hu506
    have hw2' : w = 2 := by omega
    subst hw2'
    have hMv511 : Mv = 511 := by rw [hMv]; norm_num
    rw [hMv511] at hgM
    have he2 := Nat.even_iff.mp hee
    have hres : e % 1022 = 10 := by omega
    exact special_sporadic_not_valid e hres hβ hg

/-! ## The triple contradiction -/

/-- Casting an integer multiple of `4M` (the modulus) gives `0`. -/
lemma intCast_four_mul_M_mul (L : ℕ) (H : ℤ) :
    ((4 * (2 ^ (L + 1) - 1) * H : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 := by
  have hmod : ((2 ^ (L + 3) - 4 : ℕ) : ℤ) = 4 * (2 ^ (L + 1) - 1) := by
    have h := rlift_modulus L
    have h1 : (1 : ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [h, Nat.cast_sub h1]
    ring
  rw [← hmod, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/-- **The triple contradiction.**  Three admissible rivals whose odd
supports cancel pairwise (each coordinate is odd in an even number of
them), each with value a multiple of `2M`, and total value a multiple of
`4M`, cannot all be avoided. -/
lemma master_triple_contra {L : ℕ}
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)} {r : Fin (L + 3) → ℕ}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod (2 ^ (L + 3) - 4)) + β i)
    (hv : ValidTuple g)
    (c₁ c₂ c₃ : Fin (L + 3) → ℤ)
    (hf₁ : ∀ i, -1 ≤ c₁ i) (hf₂ : ∀ i, -1 ≤ c₂ i) (hf₃ : ∀ i, -1 ≤ c₃ i)
    (hs₁ : ∑ i, c₁ i = 0) (hs₂ : ∑ i, c₂ i = 0) (hs₃ : ∑ i, c₃ i = 0)
    {j₁ j₂ j₃ : Fin (L + 3)}
    (hw₁ : c₁ j₁ ≠ 0) (hw₂ : c₂ j₂ ≠ 0) (hw₃ : c₃ j₃ ≠ 0)
    (hxor : ∀ i, ((Odd (c₁ i) ↔ Odd (c₂ i)) ↔ ¬ Odd (c₃ i)))
    (hV₁ : ∃ G : ℤ, ∑ i, c₁ i * (r i : ℤ) = 2 * (2 ^ (L + 1) - 1) * G)
    (hV₂ : ∃ G : ℤ, ∑ i, c₂ i * (r i : ℤ) = 2 * (2 ^ (L + 1) - 1) * G)
    (hV₃ : ∃ G : ℤ, ∑ i, c₃ i * (r i : ℤ) = 2 * (2 ^ (L + 1) - 1) * G)
    (hVtot : ∃ H : ℤ, (∑ i, c₁ i * (r i : ℤ)) + (∑ i, c₂ i * (r i : ℤ))
        + (∑ i, c₃ i * (r i : ℤ)) = 4 * (2 ^ (L + 1) - 1) * H) :
    False := by
  classical
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet L
  have hss : sheet L + sheet L = 0 := by
    rw [← two_nsmul]
    exact two_nsmul_sheet L
  have h₁ := rival_vector_ne hβ2 hg hv c₁ hf₁ hs₁ hw₁
  have h₂ := rival_vector_ne hβ2 hg hv c₂ hf₂ hs₂ hw₂
  have h₃ := rival_vector_ne hβ2 hg hv c₃ hf₃ hs₃ hw₃
  set S₁ := ∑ i ∈ Finset.univ.filter (fun i => Odd (c₁ i)), β i with hS₁
  set S₂ := ∑ i ∈ Finset.univ.filter (fun i => Odd (c₂ i)), β i with hS₂
  set S₃ := ∑ i ∈ Finset.univ.filter (fun i => Odd (c₃ i)), β i with hS₃
  have hc₁m : ((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 ∨
      ((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
    obtain ⟨G, hG⟩ := hV₁
    rw [hG]
    exact intCast_two_mul_M_mul L G
  have hc₂m : ((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 ∨
      ((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
    obtain ⟨G, hG⟩ := hV₂
    rw [hG]
    exact intCast_two_mul_M_mul L G
  have hc₃m : ((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 ∨
      ((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
    obtain ⟨G, hG⟩ := hV₃
    rw [hG]
    exact intCast_two_mul_M_mul L G
  have hS₁m : S₁ = 0 ∨ S₁ = sheet L :=
    sum_mem_pair (two_nsmul_sheet L) _ _ (fun i _ => hβ i)
  have hS₂m : S₂ = 0 ∨ S₂ = sheet L :=
    sum_mem_pair (two_nsmul_sheet L) _ _ (fun i _ => hβ i)
  have hS₃m : S₃ = 0 ∨ S₃ = sheet L :=
    sum_mem_pair (two_nsmul_sheet L) _ _ (fun i _ => hβ i)
  have hX₁ : ((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₁
      = sheet L := (pair_sum_cases hc₁m hS₁m (two_nsmul_sheet L)).resolve_left h₁
  have hX₂ : ((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₂
      = sheet L := (pair_sum_cases hc₂m hS₂m (two_nsmul_sheet L)).resolve_left h₂
  have hX₃ : ((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₃
      = sheet L := (pair_sum_cases hc₃m hS₃m (two_nsmul_sheet L)).resolve_left h₃
  -- the odd supports cancel
  have hzero : S₁ + S₂ + S₃ = 0 := by
    rw [hS₁, hS₂, hS₃, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hx := hxor i
    by_cases hb : β i = 0
    · simp [hb]
    · have hbs : β i = sheet L := (hβ i).resolve_left hb
      by_cases ho₁ : Odd (c₁ i) <;> by_cases ho₂ : Odd (c₂ i) <;>
        by_cases ho₃ : Odd (c₃ i)
      · simp [ho₁, ho₂, ho₃] at hx
      · rw [if_pos ho₁, if_pos ho₂, if_neg ho₃, add_zero, hbs]
        exact hss
      · rw [if_pos ho₁, if_neg ho₂, if_pos ho₃, add_zero, hbs]
        exact hss
      · simp [ho₁, ho₂, ho₃] at hx
      · rw [if_neg ho₁, if_pos ho₂, if_pos ho₃, zero_add, hbs]
        exact hss
      · simp [ho₁, ho₂, ho₃] at hx
      · simp [ho₁, ho₂, ho₃] at hx
      · simp [ho₁, ho₂, ho₃]
  -- the total integer value vanishes
  have htot : ((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4))
      + ((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4))
      + ((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 := by
    obtain ⟨H, hH⟩ := hVtot
    rw [← Int.cast_add, ← Int.cast_add, hH]
    exact intCast_four_mul_M_mul L H
  -- combine
  have hcomb : sheet L
      = (((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₁)
        + (((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₂)
        + (((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₃) := by
    rw [hX₁, hX₂, hX₃, hss, zero_add]
  rw [show (((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₁)
        + (((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₂)
        + (((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S₃)
      = (((∑ i, c₁ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4))
          + ((∑ i, c₂ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4))
          + ((∑ i, c₃ i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)))
        + (S₁ + S₂ + S₃) from by ring] at hcomb
  rw [htot, hzero, zero_add] at hcomb
  exact sheet_ne_zero L hcomb

end MinModulus


