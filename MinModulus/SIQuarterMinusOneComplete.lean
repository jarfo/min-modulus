/-
# Complete quarter-minus-one G3 exclusion

The small logarithmic block is settled by a dimension-uniform extraction,
not an enumeration. At half modulus M=2(2^m-2), an extra at M/2-1 is forced
to its upper sheet by validity. It then forms a two-term antipodal block
with the top prefix coin. The m-term quotient cover has at most one hole;
at that hole the other extra must equal the next SI entry in the quotient.
Thus the existing full-prefix lift theorem closes the small G3 block.

Combined with SIQuarterMinusOne, the resulting G3 exclusion holds for
every non-power full dimension n>=5. Quotient affine transport and all
independent original lift bits are allowed. Arbitrary shorter-prefix lifts
and the unrestricted G1/G2/G3 inputs remain open.
-/
import MinModulus.SIQuarterMinusOne

namespace MinModulus
open Finset

/-- At dyadic gap two, the prefix and quarter-minus-one coin cover the
entire half modulus with m terms except for one explicit target. -/
theorem exists_gap_four_quarter_minus_one_coin_cover_except_hole
    {m z : ℕ} (hm : 3 ≤ m) (hz : z < 2 * (2 ^ m - 2))
    (hne : z ≠ 2 * 2 ^ m - m - 3) :
    ∃ e ≤ 1, ∃ s : Multiset ℕ, s.card + e ≤ m ∧
      (∀ i ∈ s, i < m) ∧ (s.map a).sum + e * (2 ^ m - 3) = z := by
  let R := 2 ^ (m - 1)
  have hpow : 2 ^ m = 2 * R := by dsimp [R]; rw [← pow_succ']; congr 1; omega
  have hR : m ≤ R := by have := Nat.lt_two_pow_self (n := m - 1); dsimp [R]; omega
  by_cases hlo : z < 3 * (R - 1) - (m - 2)
  · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
      (by omega : 1 ≤ m - 1) 1 z (by
        change z < (1 + 2) * (R - 1) - ((m - 1) - 1)
        omega)
    exact ⟨0, by omega, s, by omega, fun i hi ↦ by have := hmem i hi; omega,
      by simpa using hsum⟩
  · let r := z - (2 ^ m - 3)
    have hrz : r + (2 ^ m - 3) = z := by dsimp [r]; omega
    have hr : r ≤ 2 * (R - 1) := by omega
    have hrne : r ≠ 2 * (R - 1) - ((m - 1) - 1) := by intro hh; exact hne (by omega)
    have hrep : ∃ s : Multiset ℕ, s.card ≤ m - 1 ∧
        (∀ i ∈ s, i < m) ∧ (s.map a).sum = r := by
      by_cases heq : r = 2 * (R - 1)
      · refine ⟨Multiset.replicate 2 (m - 1), by simp; omega, ?_, ?_⟩
        · intro i hi
          have := (Multiset.mem_replicate.mp hi).2
          omega
        · simp [a, R] at heq ⊢; omega
      · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
          (by omega : 1 ≤ m - 1) r (by omega) hrne
        exact ⟨s, hs, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
    obtain ⟨s, hs, hmem, hsum⟩ := hrep
    exact ⟨1, by omega, s, by omega, hmem, by rw [hsum]; simpa using hrz⟩

/-- A normalized quarter-minus-one extra at gap four forces the OTHER
extra to complete the SI prefix. This is structural extraction from
validity in every dimension m>=3, not a finite tuple classification. -/
theorem next_extra_of_valid_normalized_si_lifts_quarter_minus_one_gap_four
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * (2 ^ m - 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hone : g ((⟨1, by omega⟩ : Fin m).castSucc.castSucc) = 1)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ((2 ^ m - 3 : ℕ) : ZMod M)) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = (a m : ZMod M) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let u := fun i : Fin (m + 1) ↦ g i.castSucc
  let one : Fin m := ⟨1, by omega⟩
  let top : Fin m := ⟨m - 1, by omega⟩
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  let X := ∑ i, g i
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hR : m ≤ 2 ^ (m - 1) := by have := Nat.lt_two_pow_self (n := m - 1); omega
  have hnatTop : 2 * a top.val = 2 ^ m - 2 := by dsimp [top, a]; omega
  have htop : 2 • u top.castSucc = ((2 ^ m - 2 : ℕ) : ZMod (2 * M)) := by
    have hh := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) (u top.castSucc)
      (a top.val : ZMod (2 * M)) (by simpa only [map_natCast] using hprefix top)
    rw [hh]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hnatTop
  have hxUpper : g x = ((2 ^ m - 3 : ℕ) : ZMod (2 * M)) + M := by
    rcases eq_or_eq_add_half_of_castHom_eq (g x) ((2 ^ m - 3 : ℕ) : ZMod (2 * M))
      (by simpa only [map_natCast] using hx) with hlo | hhi
    · apply False.elim
      apply not_validTuple_of_double_eq_distinct_pair g x one.castSucc.castSucc
        top.castSucc.castSucc ?_ ?_ hg
      · intro hh
        exact Fin.castSucc_ne_last one ((Fin.castSucc_injective (m + 1) hh).symm)
      · rw [hlo, hone]
        change 2 • u top.castSucc = _
        rw [htop]
        have hn : (2 ^ m - 3) + 1 = 2 ^ m - 2 := by omega
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hn.symm
    · exact hhi
  let lo := Multiset.replicate 2 top.castSucc
  let hi : Multiset (Fin (m + 1)) := {Fin.last m} + {one.castSucc}
  have hlo : (lo.map u).sum = ((2 ^ m - 2 : ℕ) : ZMod (2 * M)) := by
    simpa only [lo, Multiset.map_replicate, Multiset.sum_replicate] using htop
  have hpair : (hi.map u).sum = (lo.map u).sum + M := by
    simp only [hi, Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
    change g x + g one.castSucc.castSucc = _
    rw [hxUpper, hone, hlo]
    have hn : (2 ^ m - 3) + 1 = 2 ^ m - 2 := by omega
    have hc := congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hn
    push_cast at hc
    linear_combination hc
  have hsum : π X = ((2 ^ m - m - 1 : ℕ) : ZMod M) +
      ((2 ^ m - 3 : ℕ) : ZMod M) + π (g y) := by
    dsimp only [X, y]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, map_add, map_add, map_sum, hx]
    congr 2
    simp only [π, hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole]
  let z := π (X - (lo.map u).sum)
  have hz : z.val < 2 * (2 ^ m - 2) := by have := z.val_lt; omega
  by_cases hhole : z.val = 2 * 2 ^ m - m - 3
  · have hzcast : z = ((2 * 2 ^ m - m - 3 : ℕ) : ZMod M) := by
      rw [← hhole, ZMod.natCast_zmod_val]
    have hnat : (2 * 2 ^ m - m - 3) + (2 ^ m - 2) =
        (2 ^ m - m - 1) + (2 ^ m - 3) + a m := by unfold a; omega
    have hc := congrArg (fun k : ℕ ↦ (k : ZMod M)) hnat
    push_cast at hc
    have hzp : z + ((2 ^ m - 2 : ℕ) : ZMod M) =
        ((2 ^ m - m - 1 : ℕ) : ZMod M) + ((2 ^ m - 3 : ℕ) : ZMod M) + π (g y) := by
      dsimp only [z]
      rw [map_sub, hlo, map_natCast, hsum]
      abel
    rw [hzcast] at hzp
    linear_combination hc - hzp
  · obtain ⟨e, he, s, hs, hmem, hcoin⟩ :=
      exists_gap_four_quarter_minus_one_coin_cover_except_hole hm hz hhole
    obtain ⟨v, hv, hvsum⟩ := exists_lifted_prefix_extra_quotient_sum_of_nat_coins
      (by omega) u hprefix hx s hs hmem
    have hproj : π ((v.map u).sum + (lo.map u).sum) = π X := by
      rw [map_add, hvsum]
      have hc := congrArg (fun k : ℕ ↦ (k : ZMod M)) hcoin
      have hh : (((s.map a).sum : ℕ) : ZMod M) + e • ((2 ^ m - 3 : ℕ) : ZMod M) = z := by
        simpa only [Nat.cast_add, Nat.cast_mul, nsmul_eq_mul, ZMod.natCast_zmod_val] using hc
      rw [hh]
      dsimp only [z]
      rw [map_sub]
      abel
    obtain ⟨w, hw, hwSum⟩ := exists_multiset_sum_of_antipodal_blocks (L := m + 2) u lo hi v
      (by simp [lo, hi]) hpair (by simp only [lo, Multiset.card_replicate]; omega) X hproj
    apply False.elim
    apply not_validTuple_of_multiset_omission g (w.map Fin.castSucc)
      (by simpa using hw) (by simpa only [Multiset.map_map, Function.comp_def] using hwSum)
      (Fin.last (m + 1)) ?_ hg
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact Fin.castSucc_ne_last i hi

/-- Actual lifted zero/one normalization removes any lift coherence
assumption from the gap-four next-entry extraction. -/
theorem next_extra_of_valid_si_lifts_quarter_minus_one_gap_four
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * (2 ^ m - 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ((2 ^ m - 3 : ℕ) : ZMod M)) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = (a m : ZMod M) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let zero : Fin m := ⟨0, by omega⟩
  let one : Fin m := ⟨1, by omega⟩
  let b := g zero.castSucc.castSucc
  let v := fun i ↦ g i - b
  let c := v one.castSucc.castSucc
  have hb : π b = 0 := (hprefix zero).trans (by norm_num [zero, a])
  have hc : π c = 1 := by
    rw [map_sub, hprefix, hb, sub_zero]
    norm_num [one, a]
  have hv : ValidTuple v := validTuple_sub_const g hg b
  have hcc := (mul_self_and_half_eq_of_castHom_eq_one hM c hc).1
  let φ : ZMod (2 * M) →+ ZMod (2 * M) :=
    { toFun := fun z ↦ c * z, map_zero' := mul_zero c, map_add' := mul_add c }
  have hw : ValidTuple (fun i ↦ c * v i) := by
    apply validTuple_of_comp φ
    convert hv using 1
    funext i
    change c * (c * v i) = v i
    rw [← mul_assoc, hcc, one_mul]
  have hnext := next_extra_of_valid_normalized_si_lifts_quarter_minus_one_gap_four
    hm hM (fun i ↦ c * v i) hw
    (by intro i; rw [map_mul, hc, one_mul, map_sub, hprefix, hb, sub_zero]) hcc
    (by rw [map_mul, hc, one_mul, map_sub, hx, hb, sub_zero])
  change π (c * v (Fin.last (m + 1))) = (a m : ZMod M) at hnext
  rw [map_mul, hc, one_mul, map_sub, hb, sub_zero] at hnext
  exact hnext

/-- Complete G3 exclusion for the quarter-minus-one family in every
relevant dimension n>=5. The small logarithmic block follows from the
uniform next-entry extraction, not a finite enumeration of lifts. -/
theorem not_validTuple_exceptional_of_si_lifts_quarter_minus_one_of_not_power
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hx : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) = ((globalBound (m + 1) / 2 - 1 : ℕ) : ZMod (globalBound (m + 1)))) :
    ¬ ValidTuple g := by
  by_cases hm7 : 7 ≤ m
  · exact not_validTuple_exceptional_of_si_lifts_quarter_minus_one hm7 g hprefix hx
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  have hlog : Nat.log 2 (m + 1) = 2 := by
    have hlo : 2 ≤ Nat.log 2 (m + 1) :=
      (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
    have hhi : Nat.log 2 (m + 1) < 3 := by
      by_contra hn
      have hp := (Nat.le_log_iff_pow_le (by norm_num : 1 < (2 : ℕ)) (by omega : m + 1 ≠ 0)).mp
        (show 3 ≤ Nat.log 2 (m + 1) by omega)
      norm_num at hp
      omega
    omega
  have hM : globalBound (m + 1) = 2 * (2 ^ m - 2) := by
    unfold globalBound
    rw [hlog, pow_succ', Nat.mul_sub_left_distrib]
    norm_num
  have hx' : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) = ((2 ^ m - 3 : ℕ) : ZMod (globalBound (m + 1))) := by
    have hP : 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
    have hhalf : globalBound (m + 1) / 2 - 1 = 2 ^ m - 3 := by omega
    simpa only [hhalf] using hx
  have hy := next_extra_of_valid_si_lifts_quarter_minus_one_gap_four hm hM g hg hprefix hx'
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  let p := Equiv.swap x y
  have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) heq)
    · exact Fin.castSucc_ne_last i.castSucc
  have hlong : ∀ i : Fin (m + 1),
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (p i.castSucc)) = (a i.val : ZMod (globalBound (m + 1))) := by
    intro i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simpa only [p, x, y, Equiv.swap_apply_left, Fin.val_last] using hy
    · rw [hfix]
      exact hprefix k
  exact not_validTuple_exceptional_of_si_lift_prefix (by omega) hnpow
    (fun i ↦ g (p i)) hlong (validTuple_embedding p.toEmbedding g hg)

/-- The complete quarter-minus-one G3 family allows an arbitrary affine
quotient prefix and independent original lift bits, for every n>=5. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_quarter_minus_one_of_not_power
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hx : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last m).castSucc)) = φ ((globalBound (m + 1) / 2 - 1 : ℕ) : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound (m + 1)) 2) φ
  let B : ZMod (2 * globalBound (m + 1)) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_exceptional_of_si_lifts_quarter_minus_one_of_not_power hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) _ _ hw
  · intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  · apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hx]
    simp [B]

end MinModulus
