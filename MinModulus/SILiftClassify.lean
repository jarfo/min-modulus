import MinModulus.SILiftTarget
import MinModulus.SILiftTwoCoins

/-!
# The SI-lift classification

Assembly of the pieces.  A valid parent over an exact super-increasing
child has its extra entry reducing to the NEXT super-increasing entry —
that is, the parent is affine-`SI` one step up.

The argument, by contradiction.  If the extra does NOT reduce correctly
then neither of the two rival targets is the unreachable residue
`2 ^ s - 1`.  Exactly one of the two lies in `[NC, NP)`, and it is not the
exceptional residue `2 ^ (m+1) + 2 ^ t - 1` either — for if it were, the
other target would be `2 ^ s - 1`, already excluded.  So `exists_two_coins`
supplies a realizing family there carrying two coins at `t - 1` or at `m`,
the sheet transport carries it to the other target with the SAME sheet sum,
and whichever of the two sits at the target matching that sheet sum is a
rival.  `siLiftSI_not_valid_of_target` then contradicts validity.
-/

namespace MinModulus

open Finset

section Classify

variable {m t : ℕ}

/-- If a rival target is the unreachable residue, the extra reduces
correctly.  Both sheet choices are covered, since `c` ranges over the
kernel of the reduction. -/
lemma siReduce_e_of_target (hmt : t ≤ m) (e c : ZMod (siFull m t))
    (hc : siReduce hmt c = 0)
    (h : ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) + e + c
      = ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t))) :
    siReduce hmt e
      = siReduce hmt ((2 ^ (m + 1) - 1 : ℕ) : ZMod (siFull m t)) := by
  have he : e = ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t))
      - ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) - c := by
    rw [← h]; ring
  rw [he, map_sub, map_sub, hc, sub_zero]
  have hkey : ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t))
      = (((2 ^ (m + 1) - 1) + 2 ^ (m + 1) - siFull m t : ℕ) :
          ZMod (siFull m t)) := by
    congr 1
    have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h3 : (2 : ℕ) ^ (t + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNv : siFull m t = 2 ^ (m + 2) - 2 ^ (t + 1) := rfl
    have hp : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    omega
  rw [hkey, Nat.cast_sub (by
      have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      have hNv : siFull m t = 2 ^ (m + 2) - 2 ^ (t + 1) := rfl
      have hp : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      have h2 : (1 : ℕ) ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega),
    Nat.cast_add, ZMod.natCast_self]
  simp only [map_sub, map_add, map_zero, sub_zero]
  abel

/-- The sheet's canonical representative is the child modulus. -/
lemma siSheet_val (hmt : t ≤ m) :
    haveI : NeZero (siFull m t) := ⟨by have := siFull_pos hmt; omega⟩
    (siSheet m t).val = siHalf m t := by
  haveI : NeZero (siFull m t) := ⟨by have := siFull_pos hmt; omega⟩
  unfold siSheet
  refine ZMod.val_natCast_of_lt ?_
  have h := siFull_eq_two_mul (m := m) (t := t) hmt
  have := siHalf_pos (m := m) (t := t) hmt
  omega

/-- **The SI-lift classification.**  A valid parent over an exact
super-increasing child has its extra entry reducing to the next
super-increasing entry: the parent is affine-`SI` one step up. -/
theorem siLiftSI_affine (hmt : t ≤ m) (hm5 : 5 ≤ m) (ht : 1 ≤ t)
    (htm : 2 ^ (t + 1) ≤ m + 2) (b : ℕ → ℕ) (e : ZMod (siFull m t))
    (hv : ValidTuple (siLiftSI m t b e)) :
    siReduce hmt e
      = siReduce hmt ((2 ^ (m + 1) - 1 : ℕ) : ZMod (siFull m t)) := by
  haveI : NeZero (siFull m t) := ⟨by have := siFull_pos hmt; omega⟩
  by_contra hcon
  obtain ⟨T0, hT0⟩ : ∃ T : ZMod (siFull m t),
      T = ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) + e := ⟨_, rfl⟩
  have hsh : siSheet m t = ((siHalf m t : ℕ) : ZMod (siFull m t)) := rfl
  have hNC : siHalf m t = 2 ^ (m + 1) - 2 ^ t := rfl
  have hNP : siFull m t = 2 ^ (m + 2) - 2 ^ (t + 1) := rfl
  have hhalf := siFull_eq_two_mul (m := m) (t := t) hmt
  have hpos := siHalf_pos (m := m) (t := t) hmt
  -- neither target is the unreachable residue `2 ^ s - 1`
  have hT0ne : T0.val ≠ 2 ^ (t + 1) - 1 := by
    intro h
    refine hcon (siReduce_e_of_target hmt e 0 (map_zero _) ?_)
    rw [add_zero, ← hT0, ← h]
    exact (ZMod.natCast_rightInverse T0).symm
  have hT1ne : (T0 + siSheet m t).val ≠ 2 ^ (t + 1) - 1 := by
    intro h
    refine hcon
      (siReduce_e_of_target hmt e (siSheet m t) (siReduce_sheet hmt) ?_)
    rw [← hT0, ← h]
    exact (ZMod.natCast_rightInverse (T0 + siSheet m t)).symm
  -- the core: a target in `[NC, NP)` that is not the exceptional residue
  have core : ∀ Tb : ZMod (siFull m t),
      (Tb = T0 ∨ Tb = T0 + siSheet m t) → siHalf m t ≤ Tb.val →
      Tb.val ≠ 2 ^ (m + 1) + 2 ^ t - 1 → False := by
    intro Tb hTb hbig hexc
    have hblt : Tb.val < siFull m t := ZMod.val_lt Tb
    have hcastb : ((Tb.val : ℕ) : ZMod (siFull m t)) = Tb :=
      ZMod.natCast_rightInverse Tb
    obtain ⟨κ, hκv, hκd, hκ2⟩ :=
      exists_two_coins (m := m) (t := t) hm5 ht htm
        (by rw [← hNC]; exact hbig) (by rw [← hNP]; exact hblt) hexc
    -- transport to the other target, keeping the sheet sum
    obtain ⟨κ', hv', hd', hs'⟩ : ∃ κ',
        ((val (m + 1) κ' : ℕ) : ZMod (siFull m t)) = Tb + siSheet m t
          ∧ dsum (m + 1) κ' = m + 2
          ∧ sheetSum (m + 1) b κ' = sheetSum (m + 1) b κ := by
      rcases hκ2 with h2 | h2
      · obtain ⟨hu, hdd, hss⟩ := shiftTwo_sheet_step (k := κ) b ht hmt h2
        refine ⟨shiftTwo κ (t - 1) m, ?_, by rw [hdd, hκd], hss⟩
        have hvv : val (m + 1) (shiftTwo κ (t - 1) m)
            = Tb.val + siHalf m t := by
          have h1 : (2 : ℕ) ^ t ≤ 2 ^ (m + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hκv] at hu; omega
        rw [hvv, Nat.cast_add, hcastb, ← hsh]
      · obtain ⟨hu, hdd, hss⟩ := shiftTwo_sheet_step_down (k := κ) b ht hmt h2
        refine ⟨shiftTwo κ m (t - 1), ?_, by rw [hdd, hκd], hss⟩
        have hvv : val (m + 1) (shiftTwo κ m (t - 1)) + siHalf m t
            = Tb.val := by
          have h1 : (2 : ℕ) ^ t ≤ 2 ^ (m + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hκv] at hu; omega
        have : ((val (m + 1) (shiftTwo κ m (t - 1)) : ℕ) :
            ZMod (siFull m t)) + siSheet m t = Tb := by
          rw [hsh, ← Nat.cast_add, hvv, hcastb]
        rw [← this, add_assoc, siSheet_add_self hmt, add_zero]
    -- whichever family sits at the target matching its sheet sum is a rival
    have hcastk : ((val (m + 1) κ : ℕ) : ZMod (siFull m t)) = Tb := by
      rw [hκv, hcastb]
    have hsheetval : ∀ c : ℕ, c • siSheet m t
        = if c % 2 = 0 then 0 else siSheet m t := by
      intro c
      rw [nsmul_siSheet hmt c]
      by_cases h : c % 2 = 0
      · rw [h]; simp
      · rw [show c % 2 = 1 from by omega]; simp
    have hkill : ∀ (κ'' : ℕ → ℕ), dsum (m + 1) κ'' = m + 2 →
        ((val (m + 1) κ'' : ℕ) : ZMod (siFull m t))
          = T0 + (sheetSum (m + 1) b κ'') • siSheet m t → False := by
      intro κ'' hd hval
      exact siLiftSI_not_valid_of_target hmt b κ'' e hd
        (by rw [hval, hT0]) hv
    by_cases hpar : sheetSum (m + 1) b κ % 2 = 0
    · -- even sheet sum: the rival must sit at `T0`
      rcases hTb with rfl | rfl
      · exact hkill κ hκd (by rw [hcastk, hsheetval, if_pos hpar, add_zero])
      · refine hkill κ' hd' ?_
        rw [hv', hs', hsheetval, if_pos hpar, add_zero]
        have := siSheet_add_self (m := m) (t := t) hmt
        rw [add_assoc, this, add_zero]
    · -- odd sheet sum: the rival must sit at `T0 + sheet`
      rcases hTb with rfl | rfl
      · refine hkill κ' hd' ?_
        rw [hv', hs', hsheetval, if_neg (by omega)]
      · exact hkill κ hκd (by rw [hcastk, hsheetval, if_neg (by omega)])
  -- exactly one of the two targets lies in `[NC, NP)`
  have hvadd : (T0 + siSheet m t).val
      = (T0.val + siHalf m t) % siFull m t := by
    rw [ZMod.val_add, siSheet_val hmt]
  have hT0lt : T0.val < siFull m t := ZMod.val_lt T0
  rcases Nat.lt_or_ge T0.val (siHalf m t) with hlt | hge
  · refine core (T0 + siSheet m t) (Or.inr rfl) ?_ ?_
    · rw [hvadd, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hvadd, Nat.mod_eq_of_lt (by omega)]
      intro hc
      apply hT0ne
      have h1 : (2 : ℕ) ^ t ≤ 2 ^ (m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_pow _ _ (by norm_num)
      have hpt : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
      omega
  · refine core T0 (Or.inl rfl) hge ?_
    intro hc
    apply hT1ne
    have h1 : (2 : ℕ) ^ t ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_pow _ _ (by norm_num)
    have hpt : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
    have hpm : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    have hsum : T0.val + siHalf m t = siFull m t + (2 ^ (t + 1) - 1) := by
      omega
    rw [hvadd, hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

end Classify

end MinModulus
