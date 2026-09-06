/-
# Complete first-even SI lift exclusion and all-stratum G1 descent

The complete first-even threshold 2^n-2 <= N is proved for n>=5, N=2*M
with M odd, and an arbitrary unit-affine SI prefix of length n-1 in the
actual half quotient. All original lift bits and the extra are allowed.

Starting from the extracted one-defect normal form, uniform three- and
four-term rivals force j=2, then l=3, then contradict validity for n>=6.
The n=5 boundary is closed by six explicit pair identities at M=9,11,13.
No finite census or unrestricted global gate is used. The valid subbinary
endpoint gives a smaller fixed Mersenne tuple. Combined with higher-even
descent, every subbinary full unit-affine SI quotient-prefix lift now has
actual G1 descent. Arbitrary-prefix extraction and G1/G2/G3 remain open.
-/
import MinModulus.SILiftOddNormalForm

namespace MinModulus
open Finset

/-- A same-cardinality multiset replacement of a subset is a rival if
it repeats a coordinate outside the removed subset. This supports uniform
three- and four-term identities without enumerating full tuples. -/
theorem not_validTuple_of_multiset_sum_eq_finset_with_outside
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (S : Finset (Fin n)) (t : Multiset (Fin n)) (htcard : t.card = S.card)
    (htsum : (t.map g).sum = ∑ i ∈ S, g i)
    (c : Fin n) (hct : c ∈ t) (hcS : c ∉ S) : ¬ ValidTuple g := by
  classical
  let R := Sᶜ
  let v := R.val + t
  have hcard : v.card = n := by
    simp only [v, Multiset.card_add, htcard]
    have hh := Finset.card_compl_add_card S
    simpa only [R, Finset.card_def, Fintype.card_fin] using hh
  have hsum : (v.map g).sum = ∑ i, g i := by
    rw [Multiset.map_add, Multiset.sum_add, htsum]
    simpa only [R, Finset.sum_eq_multiset_sum] using Finset.sum_compl_add_sum S g
  intro hg
  have hc := multiset_count_eq_one_of_validTuple g hg v hcard hsum c
  have hr : 0 < R.val.count c := Multiset.count_pos.mpr (by simpa [R] using hcS)
  have ht : 0 < t.count c := Multiset.count_pos.mpr hct
  simp only [v, Multiset.count_add] at hc
  omega

/-- A three-term replacement with an outside entry is already enough
to violate validity, regardless of the remaining coordinates. -/
theorem not_validTuple_of_three_sum_eq_with_outside
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (a b c d e : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hea : e ≠ a) (heb : e ≠ b) (hec : e ≠ c)
    (heq : 2 • g d + g e = g a + g b + g c) : ¬ ValidTuple g := by
  classical
  apply not_validTuple_of_multiset_sum_eq_finset_with_outside g {a, b, c}
    (Multiset.replicate 2 d + {e}) _ _ e (by simp) (by simp [hea, heb, hec])
  · simp [hab, hac, hbc]
  · simpa [hab, hac, hbc, succ_nsmul, add_assoc] using heq

/-- Four distinct entries cannot sum to four copies of an outside entry. -/
theorem not_validTuple_of_four_sum_eq_with_outside
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (a b c d e : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hea : e ≠ a) (heb : e ≠ b) (hec : e ≠ c) (hed : e ≠ d)
    (heq : 4 • g e = g a + g b + g c + g d) : ¬ ValidTuple g := by
  classical
  apply not_validTuple_of_multiset_sum_eq_finset_with_outside g {a, b, c, d}
    (Multiset.replicate 4 e) _ _ e (by simp) (by simp [hea, heb, hec, hed])
  · simp [hab, hac, had, hbc, hbd, hcd]
  · simpa [hab, hac, had, hbc, hbd, hcd, succ_nsmul, add_assoc] using heq

/-- A coherent-terminal one-defect normal form can be valid only if the
defect is at index two. At a later defect, a uniform three-term identity
already gives a rival. No modulus bound or parity assumption is needed. -/
theorem defect_index_eq_two_of_valid_one_defect_si_normal_form
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (c : ZMod (2 * M)) (j : Fin m) (l : ℕ)
    (hj : 2 ≤ j.val) (hl : 3 ≤ l) (hlm : l ≤ m) (hlj : l ≠ j.val)
    (hform : ∀ i : Fin (m + 1), g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = j.val then (M : ZMod (2 * M)) else 0)
    (hx : g (Fin.last (m + 1)) = c * (1 + (2 ^ j.val : ℕ) - (2 ^ l : ℕ) : ZMod (2 * M))) :
    j.val = 2 := by
  by_contra hj2
  have hj3 : 3 ≤ j.val := by omega
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let two : Fin (m + 1) := ⟨2, by omega⟩
  let prev : Fin (m + 1) := ⟨j.val - 1, by omega⟩
  let ell : Fin (m + 1) := ⟨l, by omega⟩
  let x := Fin.last (m + 1)
  apply not_validTuple_of_three_sum_eq_with_outside g
    x ell.castSucc one.castSucc prev.castSucc two.castSucc
    (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm
    (by intro h; have hh : l = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _)
    (by intro h; have hh : (2 : ℕ) = l := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = 1 := congrArg Fin.val h; omega) _ hg
  have hp : g prev.castSucc = c * (a (j.val - 1) : ZMod (2 * M)) := by
    simpa only [prev, show j.val - 1 ≠ j.val by omega, ↓reduceIte, add_zero] using hform prev
  have htwo : g two.castSucc = 3 * c := by
    have hh := hform two
    change g two.castSucc = c * (a 2 : ZMod (2 * M)) + (if 2 = j.val then (M : ZMod (2 * M)) else 0) at hh
    rw [if_neg (by omega)] at hh
    norm_num only [a, Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat, add_zero] at hh
    rw [hh]; ring
  have hone : g one.castSucc = c := by
    have hh := hform one
    change g one.castSucc = c * (a 1 : ZMod (2 * M)) + (if 1 = j.val then (M : ZMod (2 * M)) else 0) at hh
    simpa [a, show (1 : ℕ) ≠ j.val by omega] using hh
  have hell : g ell.castSucc = c * (a l : ZMod (2 * M)) := by
    simpa only [ell, hlj, ↓reduceIte, add_zero] using hform ell
  have hpcast : 2 * (a (j.val - 1) : ZMod (2 * M)) + 3 =
      ((2 ^ j.val : ℕ) : ZMod (2 * M)) + 1 := by
    have hh : 2 * a (j.val - 1) + 3 = 2 ^ j.val + 1 := by
      have hp : 2 ^ j.val = 2 * 2 ^ (j.val - 1) := by rw [← pow_succ']; congr 1; omega
      have hpos : 0 < 2 ^ (j.val - 1) := by positivity
      unfold a; omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hh
  have hal : (a l : ZMod (2 * M)) + 1 = ((2 ^ l : ℕ) : ZMod (2 * M)) := by
    have hh : a l + 1 = 2 ^ l := by
      unfold a
      have hp : 0 < 2 ^ l := by positivity
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hh
  change 2 • g prev.castSucc + g two.castSucc = g (Fin.last (m + 1)) + g ell.castSucc + g one.castSucc
  rw [hp, htwo, hx, hell, hone, nsmul_eq_mul]
  linear_combination c * hpcast - c * hal

/-- Once the defect is at index two, a complement beyond eight gives a
uniform four-term rival. This uses neither oddness nor criticality. -/
theorem complement_eq_three_of_valid_index_two_si_normal_form
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (c : ZMod (2 * M)) (l : ℕ) (hl : 3 ≤ l) (hlm : l ≤ m)
    (hform : ∀ i : Fin (m + 1), g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = 2 then (M : ZMod (2 * M)) else 0)
    (hx : g (Fin.last (m + 1)) = c * (5 - (2 ^ l : ℕ) : ZMod (2 * M))) : l = 3 := by
  by_contra hl3
  have hl4 : 4 ≤ l := by omega
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let two : Fin (m + 1) := ⟨2, by omega⟩
  let three : Fin (m + 1) := ⟨3, by omega⟩
  let ell : Fin (m + 1) := ⟨l, by omega⟩
  let x := Fin.last (m + 1)
  apply not_validTuple_of_four_sum_eq_with_outside g
    x ell.castSucc three.castSucc one.castSucc two.castSucc
    (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm
    (by intro h; have hh : l = 3 := congrArg Fin.val h; omega)
    (by intro h; have hh : l = 1 := congrArg Fin.val h; omega)
    (by intro h; have hh : (3 : ℕ) = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _)
    (by intro h; have hh : (2 : ℕ) = l := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = 3 := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = 1 := congrArg Fin.val h; omega) _ hg
  have htwo : g two.castSucc = c * 3 + M := by simpa [two, a] using hform two
  have hthree : g three.castSucc = c * 7 := by simpa [three, a] using hform three
  have hone : g one.castSucc = c := by simpa [one, a] using hform one
  have hell : g ell.castSucc = c * (a l : ZMod (2 * M)) := by
    simpa only [ell, show l ≠ 2 by omega, ↓reduceIte, add_zero] using hform ell
  have hal : (a l : ZMod (2 * M)) + 1 = ((2 ^ l : ℕ) : ZMod (2 * M)) := by
    have hh : a l + 1 = 2 ^ l := by
      unfold a
      have hp : 0 < 2 ^ l := by positivity
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hh
  have hh := half_add_half (M := M) rfl
  change 4 • g two.castSucc = g (Fin.last (m + 1)) + g ell.castSucc + g three.castSucc + g one.castSucc
  rw [htwo, hx, hell, hthree, hone, nsmul_eq_mul]
  linear_combination 2 * hh - c * hal

/-- The final index-two/complement-eight family also has a uniform
three-term rival as soon as the coherent entry fifteen is available. -/
theorem not_validTuple_of_index_two_complement_three_si_normal_form
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (c : ZMod (2 * M))
    (hform : ∀ i : Fin (m + 1), g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = 2 then (M : ZMod (2 * M)) else 0)
    (hx : g (Fin.last (m + 1)) = -3 * c) : ¬ ValidTuple g := by
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let two : Fin (m + 1) := ⟨2, by omega⟩
  let three : Fin (m + 1) := ⟨3, by omega⟩
  let four : Fin (m + 1) := ⟨4, by omega⟩
  let x := Fin.last (m + 1)
  apply not_validTuple_of_three_sum_eq_with_outside g
    x four.castSucc one.castSucc two.castSucc three.castSucc
    (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm
    (by intro h; have hh : (4 : ℕ) = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _)
    (by intro h; have hh : (3 : ℕ) = 4 := congrArg Fin.val h; omega)
    (by intro h; have hh : (3 : ℕ) = 1 := congrArg Fin.val h; omega)
  have htwo : g two.castSucc = c * 3 + M := by simpa [two, a] using hform two
  have hthree : g three.castSucc = c * 7 := by simpa [three, a] using hform three
  have hfour : g four.castSucc = c * 15 := by simpa [four, a] using hform four
  have hone : g one.castSucc = c := by simpa [one, a] using hform one
  have hh := half_add_half (M := M) rfl
  change 2 • g two.castSucc + g three.castSucc = g (Fin.last (m + 1)) + g four.castSucc + g one.castSucc
  rw [htwo, hthree, hx, hfour, hone, nsmul_eq_mul]
  linear_combination hh

/-- The dimension-five boundary of the final family is elementary: the
binary floor and first-even criticality leave M=9,11,13, and each of the
two possible lifted-one values has an explicit pair rival. These are exact
base-case identities, not a census assumption for the general argument. -/
theorem not_validTuple_five_of_small_odd_index_two_complement_three
    {M : ℕ} [NeZero M] (hq : Odd M) (hM : M ≤ 14)
    (g : Fin 5 → ZMod (2 * M)) (c : ZMod (2 * M))
    (hc : ZMod.castHom (dvd_mul_left M 2) (ZMod M) c = 1)
    (hform : ∀ i : Fin 4, g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = 2 then (M : ZMod (2 * M)) else 0)
    (hx : g (Fin.last 4) = -3 * c) : ¬ ValidTuple g := by
  intro hg
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  norm_num only [Nat.reduceSub, Nat.reducePow, ZMod.card] at hbinary
  have hmods : M = 9 ∨ M = 11 ∨ M = 13 := by
    obtain ⟨r, hr⟩ := hq
    omega
  have hcs : c = 1 ∨ c = 1 + (M : ZMod (2 * M)) :=
    eq_or_eq_add_half_of_castHom_eq c 1 (by simpa only [map_one] using hc)
  have hgf : g = ![0, c, c * 3 + M, c * 7, -3 * c] := by
    funext i
    fin_cases i
    · simpa [a] using hform ⟨0, by decide⟩
    · simpa [a] using hform ⟨1, by decide⟩
    · simpa [a] using hform ⟨2, by decide⟩
    · simpa [a] using hform ⟨3, by decide⟩
    · exact hx
  subst g
  rcases hmods with rfl | rfl | rfl
  · rcases hcs with rfl | rfl
    · exact not_validTuple_of_double_eq_distinct_pair _ 2 0 4 (by decide) (by decide) hg
    · exact not_validTuple_of_pair_sum_eq_with_outside _ 0 3 1 4
        (by decide) (by decide) (by decide) (by decide) hg
  · rcases hcs with rfl | rfl
    · exact not_validTuple_of_double_eq_distinct_pair _ 2 0 3 (by decide) (by decide) hg
    · exact not_validTuple_of_pair_sum_eq_with_outside _ 0 4 1 3
        (by decide) (by decide) (by decide) (by decide) hg
  · rcases hcs with rfl | rfl
    · exact not_validTuple_of_pair_sum_eq_with_outside _ 4 0 2 3
        (by decide) (by decide) (by decide) (by decide) hg
    · exact not_validTuple_of_double_eq_distinct_pair _ 0 1 3 (by decide) (by decide) hg

/-- The entire normalized critical first-even full-prefix class is
impossible in every n>=5. This closes all lift bits and all extras in that
class, not merely the earlier same-parity branch. -/
theorem not_validTuple_of_critical_odd_si_lift_prefix_normalized
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨j, l, hj, hl, hlm, hlj, hform, hx⟩ :=
    exists_one_defect_normal_form_of_valid_critical_odd_si_lifts hm hq hM g hg hprefix hzero
  let c := g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)
  have hj2 := defect_index_eq_two_of_valid_one_defect_si_normal_form
    hm g hg c j l hj hl hlm hlj hform hx
  have hform2 : ∀ i : Fin (m + 1), g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = 2 then (M : ZMod (2 * M)) else 0 := by simpa only [hj2] using hform
  have hx5 : g (Fin.last (m + 1)) = c * (5 - (2 ^ l : ℕ) : ZMod (2 * M)) := by
    simpa only [hj2, Nat.reducePow, Nat.cast_ofNat, show (1 + 4 : ZMod (2 * M)) = 5 by norm_num] using hx
  have hl3 := complement_eq_three_of_valid_index_two_si_normal_form hm g hg c l hl hlm hform2 hx5
  have hx3 : g (Fin.last (m + 1)) = -3 * c := by
    rw [hl3] at hx5
    norm_num only [Nat.reducePow, Nat.cast_ofNat] at hx5
    calc
      _ = c * (-3 : ZMod (2 * M)) := hx5
      _ = _ := by ring
  by_cases hm4 : 4 ≤ m
  · exact not_validTuple_of_index_two_complement_three_si_normal_form hm4 g c hform2 hx3 hg
  · have hm3 : m = 3 := by omega
    subst m
    have hc : ZMod.castHom (dvd_mul_left M 2) (ZMod M) c = 1 :=
      (hprefix ⟨1, by decide⟩).trans (by norm_num [a])
    exact not_validTuple_five_of_small_odd_index_two_complement_three hq (by norm_num at hM; omega)
      g c hc hform2 hx3 hg

/-- Full first-even threshold for arbitrary independent lifts of a full
unit-affine SI quotient prefix, in every n>=5. No coherence, parity of
the lifted one, common touch, or unrestricted global gate is assumed. -/
theorem first_even_lower_bound_of_valid_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) :
    2 ^ (m + 2) - 2 ≤ 2 * M := by
  by_contra hbound
  have hM : M ≤ 2 * (2 ^ m - 1) := by
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hpos : 0 < 2 ^ m := by positivity
    omega
  have hpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin (m + 1)).castSucc
  let B := g (e zero)
  let w := fun i ↦ Φ.symm (g (e i) - B)
  have hB : ZMod.castHom (dvd_mul_left M 2) (ZMod M) B = b := by
    simpa only [a, pow_zero, Nat.sub_self, Nat.cast_zero, map_zero, zero_add] using hprefix ⟨0, by omega⟩
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hpref : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (w i.castSucc) = (a i.val : ZMod M) := by
    intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix, hB, add_sub_cancel_right]
  have hz : w zero = 0 := by simp [w, B]
  exact not_validTuple_of_critical_odd_si_lift_prefix_normalized hm hq hM w hpref hz hw

/-- Below the binary bound, the only first-even modulus for this entire
quotient-prefix class is the exact Mersenne half endpoint. -/
theorem half_eq_mersenne_of_valid_subbinary_odd_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : M = 2 ^ (m + 1) - 1 := by
  have hb := first_even_lower_bound_of_valid_quotient_affine_si_prefix hm hq g hg e φ b hprefix
  have hp : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [show m + 2 = m + 1 + 1 by omega, pow_succ']
  omega

/-- Actual half descent throughout the first-even subbinary full-prefix
class, including its valid boundary. The smaller tuple is the proved fixed
Mersenne endpoint, not an assumed canonical half deletion. -/
theorem admitsValidTuple_half_of_subbinary_odd_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : AdmitsValidTuple (m + 1) M := by
  have hM := half_eq_mersenne_of_valid_subbinary_odd_quotient_affine_si_prefix
    hm hq hupper g hg e φ b hprefix
  subst M
  refine ⟨_, validTuple_fixed_of_valid ?_⟩
  simpa only [pow_zero] using valid_gap (n := m + 1) (t := 0) (by omega) (by norm_num)

/-- Every subbinary full unit-affine SI quotient-prefix lift now has actual
G1 half descent, for ALL positive half moduli and all n>=5. This combines
the complete first-even threshold with the proved higher-even mechanism;
arbitrary-prefix extraction and the unrestricted global gates remain open. -/
theorem admitsValidTuple_half_of_subbinary_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : AdmitsValidTuple (m + 1) M := by
  rcases Nat.even_or_odd M with hM | hM
  · exact admitsValidTuple_half_of_subbinary_even_quotient_affine_si_prefix hm hM hupper g hg e φ b hprefix
  · exact admitsValidTuple_half_of_subbinary_odd_quotient_affine_si_prefix hm hM hupper g hg e φ b hprefix

end MinModulus
