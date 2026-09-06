/-
# First-even SI lift normal form and actual same-parity G1 descent

For n=m+2>=5 and odd M with 2*M<2^n-2, validity and a full SI quotient
prefix force exactly one wrong interior lift, a coherent terminal lift,
and an actual extra c*(1+2^j-2^l), with 3<=l<=m and l!=j. Here c is the
actual lifted one after normalizing the actual lifted zero to zero.

The general pair-sum lemmas work without criticality or SI structure.
Two forbidden quotient pair identities force opposite sheets upstairs;
their difference gives a forbidden actual third pair identity. Combined
with odd-period dyadic intersection, this removes the terminal defect.

When the lifted zero and one share parity, the normal form gives a large
parity coset and an actual smaller valid tuple at M. Quotient affine
transport is included. The opposite-parity branch, arbitrary-prefix
extraction, and unrestricted G1/G2/G3 remain open. No finite census or
assumed global gate is used.
-/
import MinModulus.SILiftOddDefects

namespace MinModulus
open Finset

/-- Replacing two distinct coordinates by a pair containing an outside
coordinate gives a rival, even if the new pair repeats an entry. -/
theorem not_validTuple_of_pair_sum_eq_with_outside
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (a b c d : Fin n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (heq : g c + g d = g a + g b) : ¬ ValidTuple g := by
  classical
  let R := (Finset.univ.erase a).erase b
  have hb : b ∈ Finset.univ.erase a := by simp [hab.symm]
  have hcR : c ∈ R := by simp [R, hca, hcb]
  have hcard : R.card + 2 = n := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a)]
    have hn : 2 ≤ n := by
      have hcard := Finset.card_le_card (show ({a, b} : Finset (Fin n)) ⊆ Finset.univ by simp)
      simpa [hab] using hcard
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ i ∈ R, g i) + g a + g b = ∑ i, g i := by
    have h1 := Finset.sum_erase_add (Finset.univ.erase a) g hb
    have h2 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ a)
    dsimp only [R]
    rw [show (∑ i ∈ (Finset.univ.erase a).erase b, g i) + g a + g b =
      ((∑ i ∈ (Finset.univ.erase a).erase b, g i) + g b) + g a by abel, h1, h2]
  let s := R.val + ({c} + {d})
  intro hg
  have hscard : s.card = n := by simpa [s] using hcard
  have hssum : (s.map g).sum = ∑ i, g i := by
    simp only [s, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton]
    rw [heq]
    simpa only [Finset.sum_eq_multiset_sum, add_assoc] using hsum
  have hc := multiset_count_eq_one_of_validTuple g hg s hscard hssum c
  have hcpos : 0 < R.val.count c := Multiset.count_pos.mpr hcR
  simp only [s, Multiset.count_add, Multiset.count_singleton_self] at hc
  omega

/-- A forbidden pair equality downstairs must use opposite sheets upstairs. -/
theorem pair_sum_eq_add_half_of_valid_quotient_pair
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M)) (hg : ValidTuple g)
    (a b c d : Fin n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (heq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g c + g d) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g a + g b)) :
    g c + g d = g a + g b + (M : ZMod (2 * M)) := by
  rcases eq_or_eq_add_half_of_castHom_eq _ _ heq with h | h
  · exact False.elim (not_validTuple_of_pair_sum_eq_with_outside g a b c d hab hca hcb h hg)
  · exact h

/-- A three-term quotient progression cannot have its difference repeated
by a pair based outside that progression. This holds without SI structure
or any criticality, parity-fibre, or global-bound assumption. -/
theorem not_validTuple_of_quotient_progression_repeated_difference
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M))
    (a c d b e : Fin n) (hac : a ≠ c) (hcd : c ≠ d) (had : a ≠ d)
    (hba : b ≠ a) (hbc : b ≠ c) (hbd : b ≠ d)
    (hfirst : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g a + g e) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g c + g b))
    (hsecond : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g c + g e) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g d + g b)) : ¬ ValidTuple g := by
  intro hg
  have h1 := pair_sum_eq_add_half_of_valid_quotient_pair g hg c b a e
    hbc.symm hac hba.symm hfirst
  have h2 := pair_sum_eq_add_half_of_valid_quotient_pair g hg d b c e
    hbd.symm hcd hbc.symm hsecond
  apply not_validTuple_of_double_eq_distinct_pair g a d c had _ hg
  rw [two_nsmul]
  linear_combination h2 - h1

/-- The SI near-power quotient values carry a progression with a repeated
difference, so in fact they are impossible at EVERY positive half modulus,
not only in the subbinary range. The terminal and all other lift bits are
arbitrary. -/
theorem not_validTuple_of_si_lift_extra_near_power
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (j : Fin m) (hj : 2 ≤ j.val)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        ((2 ^ j.val : ℕ) : ZMod M) ∨
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        1 + ((2 ^ j.val : ℕ) : ZMod M)) : ¬ ValidTuple g := by
  let zero : Fin (m + 1) := ⟨0, by omega⟩
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let two : Fin (m + 1) := ⟨2, by omega⟩
  let next : Fin (m + 1) := ⟨j.val + 1, by omega⟩
  let x := Fin.last (m + 1)
  have ha : (a next.val : ZMod M) + 1 = 2 * ((2 ^ j.val : ℕ) : ZMod M) := by
    have hh : a (j.val + 1) + 1 = 2 * 2 ^ j.val := by
      have : 0 < 2 ^ j.val := by positivity
      unfold a; rw [pow_succ']; omega
    simpa only [next, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
  have haj : (a j.val : ZMod M) + 1 = ((2 ^ j.val : ℕ) : ZMod M) := by
    have hh : a j.val + 1 = 2 ^ j.val := by
      unfold a
      have : 0 < 2 ^ j.val := by positivity
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
  rcases hx with hx | hx
  · apply not_validTuple_of_quotient_progression_repeated_difference g
      one.castSucc x next.castSucc zero.castSucc j.castSucc.castSucc
      (Fin.castSucc_ne_last _) (Fin.castSucc_ne_last _).symm
      (by intro h; have hh : (1 : ℕ) = j.val + 1 := congrArg Fin.val h; omega)
      (by intro h; have hh : (0 : ℕ) = 1 := congrArg Fin.val h; omega)
      (Fin.castSucc_ne_last _)
      (by intro h; have hh : (0 : ℕ) = j.val + 1 := congrArg Fin.val h; omega)
    · simp only [map_add, hprefix, x, hx]
      change (a 1 : ZMod M) + (a j.val : ZMod M) = (2 ^ j.val : ℕ) + (a 0 : ZMod M)
      norm_num only [a, pow_zero, pow_one, Nat.reduceSub, Nat.cast_zero, Nat.cast_one, add_zero]
      dsimp only [a] at haj
      linear_combination haj
    · simp only [map_add, hprefix, x, hx]
      change ((2 ^ j.val : ℕ) : ZMod M) + (a j.val : ZMod M) = (a next.val : ZMod M) + (a 0 : ZMod M)
      norm_num only [a, pow_zero, Nat.sub_self, Nat.cast_zero, add_zero]
      dsimp only [a] at haj ha
      linear_combination haj - ha
  · apply not_validTuple_of_quotient_progression_repeated_difference g
      two.castSucc x next.castSucc one.castSucc j.castSucc.castSucc
      (Fin.castSucc_ne_last _) (Fin.castSucc_ne_last _).symm
      (by intro h; have hh : (2 : ℕ) = j.val + 1 := congrArg Fin.val h; omega)
      (by intro h; have hh : (1 : ℕ) = 2 := congrArg Fin.val h; omega)
      (Fin.castSucc_ne_last _)
      (by intro h; have hh : (1 : ℕ) = j.val + 1 := congrArg Fin.val h; omega)
    · simp only [map_add, hprefix, x, hx]
      change (a 2 : ZMod M) + (a j.val : ZMod M) = 1 + (2 ^ j.val : ℕ) + (a 1 : ZMod M)
      norm_num only [a, Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat, pow_one, Nat.cast_one]
      dsimp only [a] at haj
      linear_combination haj
    · simp only [map_add, hprefix, x, hx]
      change (1 + (2 ^ j.val : ℕ) : ZMod M) + (a j.val : ZMod M) = (a next.val : ZMod M) + (a 1 : ZMod M)
      norm_num only [a, pow_one, Nat.reduceSub, Nat.cast_one]
      dsimp only [a] at haj ha
      linear_combination haj - ha

/-- A complement four cannot support an isolated interior defect: validity
propagates it to the lifted entry three. This local rigidity is independent
of the size or parity of the half modulus. -/
theorem si_lift_recurrence_of_complement_four_of_coherent_two
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (j : Fin m) (hj : 3 ≤ j.val)
    (htwo : g ((⟨2, by omega⟩ : Fin (m + 1)).castSucc) =
      3 * g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      (1 + (2 ^ j.val : ℕ) : ZMod M) - 4) :
    g j.castSucc.castSucc =
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let two : Fin (m + 1) := ⟨2, by omega⟩
  let prev : Fin (m + 1) := ⟨j.val - 1, by omega⟩
  let x := Fin.last (m + 1)
  have hjnat : a j.val + 1 = 2 ^ j.val := by
    unfold a; have hp : 0 < 2 ^ j.val := by positivity
    omega
  have hjcast : (a j.val : ZMod M) + 1 = ((2 ^ j.val : ℕ) : ZMod M) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hjnat
  have hpnat : 2 * a prev.val + 3 = 2 ^ j.val + 1 := by
    have hp : 2 ^ j.val = 2 * 2 ^ (j.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (j.val - 1) := by positivity
    dsimp [a, prev]; omega
  have hpcast : 2 * (a prev.val : ZMod M) + 3 = ((2 ^ j.val : ℕ) : ZMod M) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hpnat
  have hpair := pair_sum_eq_add_half_of_valid_quotient_pair g hg
    j.castSucc.castSucc one.castSucc two.castSucc x
    (by intro h; have hh : j.val = 1 := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = j.val := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = 1 := congrArg Fin.val h; omega)
    (by
      simp only [map_add, hprefix, x, hx]
      change (a 2 : ZMod M) + (1 + (2 ^ j.val : ℕ) - 4) = (a j.val : ZMod M) + (a 1 : ZMod M)
      norm_num only [a, Nat.reducePow, Nat.reduceSub, pow_one, Nat.cast_ofNat, Nat.cast_one]
      dsimp only [a] at hjcast
      linear_combination -hjcast)
  have hdouble : g x + g one.castSucc = 2 • g prev.castSucc + (M : ZMod (2 * M)) := by
    have hproj : π (g x + g one.castSucc) = π (2 • g prev.castSucc) := by
      simp only [π, map_add, map_nsmul, hprefix, x, hx]
      change (1 + (2 ^ j.val : ℕ) - 4 : ZMod M) + (a 1 : ZMod M) = 2 • (a prev.val : ZMod M)
      norm_num only [a, pow_one, Nat.reduceSub, Nat.cast_one, nsmul_eq_mul]
      dsimp only [a] at hpcast
      linear_combination -hpcast
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hproj with h | h
    · exact False.elim (not_validTuple_of_double_eq_distinct_pair g x one.castSucc prev.castSucc
        (Fin.castSucc_ne_last _).symm h.symm hg)
    · exact h
  change g two.castSucc = 3 * g one.castSucc at htwo
  rw [htwo] at hpair
  change g j.castSucc.castSucc = 2 • g prev.castSucc + g one.castSucc
  simp only [two_nsmul] at hdouble ⊢
  linear_combination hdouble - hpair

/-- The first-even critical residual has a unique interior defect and a
dyadic complement of exponent at least three, different from that defect's
index. This removes complement four using actual defect propagation, not a
finite case check. The terminal lift and other complements remain open. -/
theorem exists_single_defect_complement_ge_three_of_critical_odd_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) :
    ∃ (j : Fin m) (l : ℕ), 2 ≤ j.val ∧ 3 ≤ l ∧ l ≤ m ∧ l ≠ j.val ∧
      g j.castSucc.castSucc ≠
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a j.val : ZMod (2 * M)) ∧
      (∀ k : Fin m, k ≠ j → g k.castSucc.castSucc =
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a k.val : ZMod (2 * M))) ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        (1 + (2 ^ j.val : ℕ) : ZMod M) - (2 ^ l : ℕ) := by
  classical
  obtain ⟨j, hjdef, huniq⟩ := exists_unique_short_prefix_defect_of_critical_odd_si_lifts
    hm hq hM g hg hprefix hzero
  have hj : 2 ≤ j.val := by
    by_contra h
    have hj01 : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj01 with hj0 | hj1
    · apply hjdef
      have he : j.castSucc.castSucc = ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) := Fin.ext hj0
      rw [he, hzero, hj0]
      norm_num [a]
    · apply hjdef
      have he : j.castSucc.castSucc = ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := Fin.ext hj1
      rw [he, hj1]
      norm_num [a]
  have hcoh (k : Fin m) (hkj : k ≠ j) : g k.castSucc.castSucc =
      g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a k.val : ZMod (2 * M)) := by
    by_contra h
    exact hkj (huniq k h)
  have hjrec : g j.castSucc.castSucc ≠
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := by
    rw [si_lift_recurrence_rhs_eq_scaled_entry (by omega) g hprefix j (by omega)]
    exact hjdef
  obtain ⟨l, hl, hlm, hx⟩ := exists_positive_dyadic_complement_of_valid_si_lift_defect
    hm hM g hg hprefix hzero j hj hjrec
  have hcrit : 2 * M < stratumBound (m + 2) 1 := by
    have hlog : 1 ≤ Nat.log 2 (m + 2) :=
      (Nat.le_log_iff_pow_le (by decide) (by omega : m + 2 ≠ 0)).mpr (by norm_num)
    unfold stratumBound
    rw [min_eq_left hlog]
    norm_num only [pow_one]
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hpos : 0 < 2 ^ m := by positivity
    omega
  have hinj := injective_quotient_of_valid_critical_unit_short_prefix
    (m := m) (s := 1) (q := M) hm hq (by simp) hcrit g hg
    (Equiv.refl _) 1 0 isUnit_one
    (by intro i; simpa only [Equiv.refl_apply, one_mul, add_zero, Fin.val_castSucc] using hprefix i.castSucc)
  have hxne (i : Fin (m + 1)) :
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) ≠ (a i.val : ZMod M) := by
    intro h
    exact (Fin.castSucc_ne_last i).symm (hinj (h.trans (hprefix i).symm))
  have hlj : l ≠ j.val := by
    intro heq
    rw [heq, add_sub_cancel_right] at hx
    apply hxne ⟨1, by omega⟩
    simpa [a] using hx
  have hl1 : l ≠ 1 := by
    intro heq
    rw [heq] at hx
    have ha : (a j.val : ZMod M) + 1 = ((2 ^ j.val : ℕ) : ZMod M) := by
      have hh : a j.val + 1 = 2 ^ j.val := by
        unfold a
        have hp : 0 < 2 ^ j.val := by positivity
        omega
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
    apply hxne j.castSucc
    change _ = (a j.val : ZMod M)
    norm_num only [pow_one, Nat.cast_ofNat] at hx
    linear_combination hx - ha
  have hl2 : l ≠ 2 := by
    intro heq
    have hj3 : 3 ≤ j.val := by omega
    apply hjrec
    apply si_lift_recurrence_of_complement_four_of_coherent_two hm g hg hprefix j hj3
    · have hh := hcoh ⟨2, by omega⟩
        (by intro h; have hv : (2 : ℕ) = j.val := congrArg Fin.val h; omega)
      calc
        _ = g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a 2 : ZMod (2 * M)) := hh
        _ = _ := by norm_num [a]; ring
    · simpa only [heq, Nat.reducePow, Nat.cast_ofNat] using hx
  exact ⟨j, l, hj, by omega, hlm, hlj, hjdef, hcoh, hx⟩

/-- Two quotient pair identities with a common entry and a common target
force a forbidden actual third pair identity. The unused endpoint may
coincide with another index; only the displayed distinctions are needed. -/
theorem not_validTuple_of_quotient_pair_triangle
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M))
    (a b c d e f : Fin n)
    (hdb : d ≠ b) (had : a ≠ d) (hab : a ≠ b)
    (hdf : d ≠ f) (hcd : c ≠ d) (hcf : c ≠ f)
    (haf : a ≠ f) (hca : c ≠ a)
    (hfirst : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g a + g e) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g d + g b))
    (hsecond : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g c + g e) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g d + g f)) : ¬ ValidTuple g := by
  intro hg
  have h1 := pair_sum_eq_add_half_of_valid_quotient_pair g hg d b a e hdb had hab hfirst
  have h2 := pair_sum_eq_add_half_of_valid_quotient_pair g hg d f c e hdf hcd hcf hsecond
  apply not_validTuple_of_pair_sum_eq_with_outside g a f c b haf hca hcf _ hg
  linear_combination h2 - h1

/-- The terminal SI power cannot also be a positive dyadic complement of
an interior defect. The pair triangle allows the complement index to BE
the terminal index, so that boundary is included. -/
theorem not_validTuple_of_si_lift_terminal_power_dyadic_complement
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (j : Fin m) (hj : 2 ≤ j.val) (l : Fin (m + 1))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      ((2 ^ m : ℕ) : ZMod M))
    (hcomp : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      (1 + (2 ^ j.val : ℕ) : ZMod M) - (2 ^ l.val : ℕ)) : ¬ ValidTuple g := by
  let zero : Fin (m + 1) := ⟨0, by omega⟩
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let top := Fin.last m
  let x := Fin.last (m + 1)
  have ha (k : ℕ) : (a k : ZMod M) + 1 = ((2 ^ k : ℕ) : ZMod M) := by
    have hh : a k + 1 = 2 ^ k := by
      unfold a
      have hp : 0 < 2 ^ k := by positivity
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
  have hjc := ha j.val
  have hmc := ha m
  have hlc := ha l.val
  apply not_validTuple_of_quotient_pair_triangle g
    top.castSucc zero.castSucc x j.castSucc.castSucc l.castSucc one.castSucc
    (by intro h; have hh : j.val = 0 := congrArg Fin.val h; omega)
    (by intro h; have hh : m = j.val := congrArg Fin.val h; omega)
    (by intro h; have hh : m = 0 := congrArg Fin.val h; omega)
    (by intro h; have hh : j.val = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm
    (by intro h; have hh : m = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _).symm
  · simp only [map_add, hprefix]
    change (a m : ZMod M) + (a l.val : ZMod M) = (a j.val : ZMod M) + (a 0 : ZMod M)
    norm_num only [a, pow_zero, Nat.sub_self, Nat.cast_zero, add_zero]
    dsimp only [a] at hjc hmc hlc
    linear_combination hcomp - hx + hmc + hlc - hjc
  · simp only [map_add, hprefix, x]
    change _ + (a l.val : ZMod M) = (a j.val : ZMod M) + (a 1 : ZMod M)
    norm_num only [a, pow_one, Nat.reduceSub, Nat.cast_one]
    dsimp only [a] at hjc hlc
    linear_combination hcomp + hlc - hjc

/-- In a critical first-even full-prefix lift, the terminal recurrence is
coherent as well. Two dyadic localizations and odd-period non-wraparound
leave only the terminal power, which the pair triangle excludes. -/
theorem terminal_recurrence_of_valid_critical_odd_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) :
    g (Fin.last m).castSucc =
      2 • g ((⟨m - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := by
  by_contra hdef
  obtain ⟨j, l, hj, hl, hlm, hlj, _, _, hxl⟩ :=
    exists_single_defect_complement_ge_three_of_critical_odd_si_lifts hm hq hM g hg hprefix hzero
  obtain ⟨p, hp, hxp⟩ := exists_dyadic_complement_of_valid_si_lift_defect
    hm hM g hg hprefix hzero (Fin.last m) (by simp; omega) hdef
  change ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
    (1 + (2 ^ m : ℕ) : ZMod M) - p at hxp
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 2 - 1 = m + 1 by omega, pow_succ'] at hbinary
  have hfloor : 2 ^ m ≤ M := by omega
  have heven (k : ℕ) (hk : 1 ≤ k) : Even (2 ^ k) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using Nat.pow_dvd_pow 2 hk
  have hfloorlt : 2 ^ m < M := by
    apply lt_of_le_of_ne hfloor
    intro h
    obtain ⟨r, hr⟩ := hq
    obtain ⟨s, hs⟩ := heven m (by omega)
    omega
  have hjbound := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) j.isLt
  have hlbound := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hlm
  have hlpos : 0 < 2 ^ l := by positivity
  have hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      ((2 ^ m : ℕ) : ZMod M) := by
    rcases hp with rfl | ⟨v, hvm, rfl⟩
    · have hc : ((2 ^ m + 2 ^ l : ℕ) : ZMod M) = ((2 ^ j.val : ℕ) : ZMod M) := by
        simp only [Nat.cast_add, Nat.cast_zero, sub_zero] at hxp ⊢
        linear_combination hxl - hxp
      have hh := eq_of_even_natCast_eq_of_lt_two_mul_odd hq
        ((heven m (by omega)).add (heven l (by omega))) (heven j.val (by omega))
        (by omega) (by omega) hc
      omega
    · by_cases hv0 : v = 0
      · simpa [hv0] using hxp
      · have hvbound := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hvm
        have hc : ((2 ^ m + 2 ^ l : ℕ) : ZMod M) =
            ((2 ^ j.val + 2 ^ v : ℕ) : ZMod M) := by
          simp only [Nat.cast_add]
          linear_combination hxl - hxp
        have hh := eq_of_even_natCast_eq_of_lt_two_mul_odd hq
          ((heven m (by omega)).add (heven l (by omega)))
          ((heven j.val (by omega)).add (heven v (by omega)))
          (by omega) (by omega) hc
        have hlpow := (two_pow_cross_eq_of_add_eq_of_lt j.isLt hh.symm).1
        have hle : l = j.val := by
          rcases lt_trichotomy l j.val with h | h | h
          · have hh := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) h; omega
          · exact h
          · have hh := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) h; omega
        exact False.elim (hlj hle)
  exact not_validTuple_of_si_lift_terminal_power_dyadic_complement hm g hprefix j hj
    ⟨l, by omega⟩ hx hxl hg

/-- The extracted terminal recurrence agrees with the actual lifted-one
multiplier, independently of the lift bit of its predecessor. -/
theorem terminal_coherent_of_valid_critical_odd_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) :
    g (Fin.last m).castSucc =
      g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a m : ZMod (2 * M)) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let prev : Fin (m + 1) := ⟨m - 1, by omega⟩
  let c := g one.castSucc
  have hc : π c = 1 := (hprefix one).trans (by norm_num [one, a])
  have htwo := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2)
    (g prev.castSucc) (c * (a prev.val : ZMod (2 * M)))
    (by rw [map_mul, map_natCast, hc, one_mul]; exact hprefix prev)
  have ha : a m = 2 * a prev.val + 1 := by
    have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (m - 1) := by positivity
    dsimp [a, prev]; omega
  rw [terminal_recurrence_of_valid_critical_odd_si_lifts hm hq hM g hg hprefix hzero]
  change 2 • g prev.castSucc + c = c * (a m : ZMod (2 * M))
  rw [htwo, ha]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul]
  ring

/-- Actual first-even normal form: exactly one interior prefix lift is
wrong, the terminal prefix lift is coherent, and the extra is determined
upstairs by its dyadic complement. The multiplier is the actual lifted one,
and may be a nonunit. This is extracted from validity, not assumed. -/
theorem exists_one_defect_normal_form_of_valid_critical_odd_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) :
    ∃ (j : Fin m) (l : ℕ), 2 ≤ j.val ∧ 3 ≤ l ∧ l ≤ m ∧ l ≠ j.val ∧
      (∀ i : Fin (m + 1), g i.castSucc =
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a i.val : ZMod (2 * M)) +
          if i.val = j.val then (M : ZMod (2 * M)) else 0) ∧
      g (Fin.last (m + 1)) = g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) *
        (1 + (2 ^ j.val : ℕ) - (2 ^ l : ℕ) : ZMod (2 * M)) := by
  classical
  obtain ⟨j, l, hj, hl, hlm, hlj, hjdef, hcoh, hx⟩ :=
    exists_single_defect_complement_ge_three_of_critical_odd_si_lifts hm hq hM g hg hprefix hzero
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let one : Fin (m + 1) := ⟨1, by omega⟩
  let c := g one.castSucc
  let x := Fin.last (m + 1)
  have hc : π c = 1 := (hprefix one).trans (by norm_num [one, a])
  have hwrong : g j.castSucc.castSucc = c * (a j.val : ZMod (2 * M)) + M := by
    have hp : π (g j.castSucc.castSucc) = π (c * (a j.val : ZMod (2 * M))) := by
      rw [map_mul, map_natCast, hc, one_mul]
      exact hprefix j.castSucc
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hp with h | h
    · exact False.elim (hjdef h)
    · exact h
  have hfull (i : Fin (m + 1)) (hij : i.val ≠ j.val) :
      g i.castSucc = c * (a i.val : ZMod (2 * M)) := by
    by_cases hi : i.val < m
    · exact hcoh ⟨i.val, hi⟩ (by intro h; exact hij (congrArg Fin.val h))
    · have hi : i = Fin.last m := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      subst i
      exact terminal_coherent_of_valid_critical_odd_si_lifts hm hq hM g hg hprefix hzero
  have hform (i : Fin (m + 1)) : g i.castSucc = c * (a i.val : ZMod (2 * M)) +
      if i.val = j.val then (M : ZMod (2 * M)) else 0 := by
    by_cases hij : i.val = j.val
    · have hi : i = j.castSucc := Fin.ext hij
      subst i
      simpa only [Fin.val_castSucc, ↓reduceIte] using hwrong
    · simp only [hij, ↓reduceIte, add_zero]
      exact hfull i hij
  refine ⟨j, l, hj, hl, hlm, hlj, hform, ?_⟩
  let ell : Fin (m + 1) := ⟨l, by omega⟩
  have hp := pair_sum_eq_add_half_of_valid_quotient_pair g hg
    j.castSucc.castSucc one.castSucc x ell.castSucc
    (by intro h; have hh : j.val = 1 := congrArg Fin.val h; omega)
    (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm
    (by
      have ha (k : ℕ) : (a k : ZMod M) + 1 = ((2 ^ k : ℕ) : ZMod M) := by
        have hh : a k + 1 = 2 ^ k := by
          unfold a
          have hp : 0 < 2 ^ k := by positivity
          omega
        simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
      have hjc := ha j.val
      have hlc := ha l
      simp only [map_add, hprefix, x, hx]
      change (1 + (2 ^ j.val : ℕ) - (2 ^ l : ℕ) : ZMod M) + (a l : ZMod M) =
        (a j.val : ZMod M) + (a 1 : ZMod M)
      norm_num only [a, pow_one, Nat.reduceSub, Nat.cast_one]
      dsimp only [a] at hjc hlc
      linear_combination hlc - hjc)
  rw [hwrong, hfull ell hlj] at hp
  have ha (k : ℕ) : (a k : ZMod (2 * M)) + 1 = ((2 ^ k : ℕ) : ZMod (2 * M)) := by
    have hh : a k + 1 = 2 ^ k := by
      unfold a
      have hp : 0 < 2 ^ k := by positivity
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hh
  have hjc := ha j.val
  have hlc := ha l
  have hh := half_add_half (M := M) rfl
  change g x = c * (1 + (2 ^ j.val : ℕ) - (2 ^ l : ℕ) : ZMod (2 * M))
  change g x + c * (a l : ZMod (2 * M)) = c * (a j.val : ZMod (2 * M)) + M + c + M at hp
  linear_combination hp + hh + c * hjc - c * hlc

/-- The even lifted-one branch of the critical first-even full-prefix class
has actual G1 descent: the extracted normal form puts every coordinate
except its unique defect in the even coset. -/
theorem admitsValidTuple_half_of_critical_odd_si_lifts_even_one
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (hc : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
      (g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) = 0) :
    AdmitsValidTuple (m + 1) M := by
  obtain ⟨j, _, _, _, _, _, hform, hx⟩ :=
    exists_one_defect_normal_form_of_valid_critical_odd_si_lifts hm hq hM g hg hprefix hzero
  apply admitsValidTuple_half_of_all_but_one_same_parity g hg j.castSucc.castSucc 0
  intro i hij
  by_cases hi : i.val < m + 1
  · let k : Fin (m + 1) := ⟨i.val, hi⟩
    have he : k.castSucc = i := Fin.ext rfl
    have hkj : k.val ≠ j.val := by intro h; exact hij (Fin.ext h)
    rw [← he, hform k, if_neg hkj, map_add, map_mul, hc, zero_mul, map_zero, zero_add]
  · have he : i = Fin.last (m + 1) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [he, hx, map_mul, hc, zero_mul]

/-- Additive endomorphisms of an even cyclic group preserve its even
subgroup. This transports the parity premise through quotient normalization. -/
theorem cast_two_addHom_eq_zero_of_cast_two_eq_zero
    {M : ℕ} [NeZero M] (f : ZMod (2 * M) →+ ZMod (2 * M))
    (x : ZMod (2 * M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) x = 0) :
    ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (f x) = 0 := by
  have heven : Even x.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hx
    exact even_iff_two_dvd.mpr hx
  obtain ⟨r, hr⟩ := heven
  have hrep : x = (r : ZMod (2 * M)) + r := by
    rw [← Nat.cast_add, ← hr, ZMod.natCast_zmod_val]
  rw [hrep, map_add, map_add, ← two_mul]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- Actual first-even G1 descent with quotient affine transport. If the
original lifted zero and one share a parity, the extracted unique-defect
normal form supplies a retained coset and hence a smaller valid tuple.
The opposite-parity branch and arbitrary tuples remain unresolved. -/
theorem admitsValidTuple_half_of_critical_odd_quotient_affine_si_prefix_same_parity
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b)
    (hparity : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
      (g (e ((⟨1, by omega⟩ : Fin (m + 1)).castSucc))) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
        (g (e ((⟨0, by omega⟩ : Fin (m + 1)).castSucc)))) :
    AdmitsValidTuple (m + 1) M := by
  have hpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin (m + 1)).castSucc
  let one : Fin (m + 2) := (⟨1, by omega⟩ : Fin (m + 1)).castSucc
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
  apply admitsValidTuple_half_of_critical_odd_si_lifts_even_one hm hq hM w hw hpref hz
  apply cast_two_addHom_eq_zero_of_cast_two_eq_zero Φ.symm.toAddMonoidHom (g (e one) - B)
  change ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e one) - g (e zero)) = 0
  rw [map_sub, hparity, sub_self]

end MinModulus
