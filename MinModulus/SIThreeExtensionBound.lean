/-
# Three-extra coherent SI prefixes

For every n >= 7 and every positive modulus, validity and a coherent
unit-affine SI prefix of length n-3 imply the full global and exact-stratum
bounds. Below 2^n, an actual extra completes the next prefix entry, and the
proved two-extra theorem gives fixed-set validity at the same modulus.

The dimension-free interval argument uses fifteen bounded-multiplicity
rivals. Its five-extra-coin case uses one shorter Mersenne prefix. All
arithmetic parameters remain symbolic; no finite solver or global gate
is a proof input. Arbitrary-prefix extraction and nonunit three-extra
prefixes are not asserted here.
-/
import MinModulus.SILiftStructuredDescent

namespace MinModulus
open Finset

/-- The Mersenne cover needed when at most five coins are assigned to
three extra coordinates. The five-coin case uses one shorter prefix. -/
theorem exists_fixed_sum_three_extra_budget
    {m N r c : ℕ} (hm : 4 ≤ m) (hc : c ≤ 5)
    (hr : (r : ℤ) < (6 - (c : ℤ)) * (2 ^ (m - 1) - 1) - m + 2) :
    ∃ s : Multiset (Fin m), s.card = m + 3 - c ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N) := by
  by_cases hc4 : c ≤ 4
  · have hp : 0 < 2 ^ (m - 1) := by positivity
    have hr' : r < ((4 - c) + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
      have hsub : ((4 - c : ℕ) : ℤ) = 4 - c := by omega
      have hsubm : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
      have hsubpow : ((2 ^ (m - 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (m - 1) - 1 := by
        rw [Int.natCast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      have hcast : (r : ℤ) + (m - 2 : ℕ) <
          (((4 - c) + 2) * (2 ^ (m - 1) - 1) : ℕ) := by
        push_cast
        rw [hsub, hsubm, hsubpow]
        nlinarith
      exact Nat.lt_sub_iff_add_lt.mpr (by exact_mod_cast hcast)
    obtain ⟨s, hs, hsum⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
      (N := N) (by omega : 2 ≤ m) hr'
    exact ⟨s, by omega, hsum⟩
  · have hc5 : c = 5 := by omega
    subst c
    have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    have hr' : r < (0 + 2) * (2 ^ ((m - 1) - 1) - 1) - ((m - 1) - 2) := by
      have hpowz : (2 : ℤ) ^ (m - 1) = 2 * (2 : ℤ) ^ (m - 2) := by exact_mod_cast hpow
      have hcast : (r : ℤ) + ((m - 1) - 2 : ℕ) <
          ((0 + 2) * (2 ^ ((m - 1) - 1) - 1) : ℕ) := by
        have he : (m - 1) - 1 = m - 2 := by omega
        rw [he]
        push_cast
        rw [Int.natCast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        omega
      exact Nat.lt_sub_iff_add_lt.mpr (by exact_mod_cast hcast)
    obtain ⟨s, hs, hsum⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
      (N := N) (by omega : 2 ≤ m - 1) hr'
    let f : Fin (m - 1) → Fin m := fun i ↦ ⟨i.val, by omega⟩
    refine ⟨s.map f, by simp only [Multiset.card_map, hs]; omega, ?_⟩
    simpa only [Multiset.map_map, Function.comp_def, f] using hsum

/-- A prefix embedding and one outside coordinate give actual validity
of their one-extra tuple in any ambient dimension. -/
theorem validTuple_fixed_embedding_with_outside
    {m n N : ℕ} (g : Fin n → ZMod N) (hg : ValidTuple g)
    (f : Fin m ↪ Fin n) (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (j : Fin n) (hj : ∀ i, f i ≠ j) :
    ValidTuple (Fin.lastCases (g j) (fun i : Fin m ↦ (a i.val : ZMod N))) := by
  let e : Fin (m + 1) → Fin n := Fin.lastCases j f
  have he : Function.Injective e := by
    intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · intro k
      refine Fin.lastCases ?_ (fun k' ↦ ?_) k
      · intro _; rfl
      · intro hik
        simp only [e, Fin.lastCases_last, Fin.lastCases_castSucc] at hik
        exact False.elim (hj k' hik.symm)
    · intro k
      refine Fin.lastCases ?_ (fun k' ↦ ?_) k
      · intro hik
        simp only [e, Fin.lastCases_last, Fin.lastCases_castSucc] at hik
        exact False.elim (hj i' hik)
      · intro hik
        simp only [e, Fin.lastCases_castSucc] at hik
        exact congrArg Fin.castSucc (f.injective hik)
  have hv := validTuple_embedding ⟨e, he⟩ g hg
  have heq : (fun i ↦ g (e i)) =
      Fin.lastCases (g j) (fun i : Fin m ↦ (a i.val : ZMod N)) := by
    funext i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i <;> simp [e, hprefix]
  change ValidTuple (fun i ↦ g (e i)) at hv
  rwa [heq] at hv

/-- A prefix representation and any nonstandard multiplicities at three
outside coordinates produce an actual rival, in any ambient dimension. -/
theorem not_validTuple_of_three_extra_block_rival
    {m n N A B C r K : ℕ} (g : Fin n → ZMod N) (f : Fin m ↪ Fin n)
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y) (hz : ∀ i, f i ≠ z)
    (hcounts : A ≠ 1 ∨ B ≠ 1 ∨ C ≠ 1) (hcard : K + A + B + C = n)
    (hcover : ∃ s : Multiset (Fin m), s.card = K ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N))
    (hsum : (r : ZMod N) + A • g x + B • g y + C • g z = ∑ i, g i) :
    ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hs, hssum⟩ := hcover
  let t := s.map f + Multiset.replicate A x + Multiset.replicate B y + Multiset.replicate C z
  have htcard : t.card = n := by simp only [t, Multiset.card_add, Multiset.card_map,
    Multiset.card_replicate, hs]; exact hcard
  have htsum : (t.map g).sum = ∑ i, g i := by
    simpa only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Function.comp_def, hprefix, Multiset.map_replicate, Multiset.sum_replicate,
      hssum] using hsum
  have hnot (j : Fin n) (hj : ∀ i, f i ≠ j) : j ∉ s.map f := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact hj i hi
  rcases hcounts with hA | hB | hC
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum x
    apply hA
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot x hx), hxy, hxz, Ne.symm hxy, Ne.symm hxz] using h
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum y
    apply hB
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot y hy), hxy, hyz, Ne.symm hxy, Ne.symm hyz] using h
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum z
    apply hC
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot z hz), hxz, hyz, Ne.symm hxz, Ne.symm hyz] using h

/-- Validity excludes every initial-interval representation with a
nonstandard three-extra multiplicity vector. All variables are symbolic. -/
theorem three_extra_initial_interval_excluded
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g) (f : Fin m ↪ Fin (m + 3))
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y z : Fin (m + 3)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y) (hz : ∀ i, f i ≠ z)
    (hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y + g z)
    (A B C : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbudget : A + B + C ≤ 5) (hne : A ≠ 1 ∨ B ≠ 1 ∨ C ≠ 1) (q : ℤ) :
    ((2 ^ m - m - 1 : ℕ) : ℤ) + (1-A)*(g x).val + (1-B)*(g y).val + (1-C)*(g z).val < q*N ∨
    q*N + (6-A-B-C)*(2 ^ (m-1)-1)-m+2 ≤
      ((2 ^ m - m - 1 : ℕ) : ℤ)+(1-A)*(g x).val+(1-B)*(g y).val+(1-C)*(g z).val := by
  by_contra hbad
  push Not at hbad
  lift A to ℕ using hA
  lift B to ℕ using hB
  lift C to ℕ using hC
  have habc : A + B + C ≤ 5 := by exact_mod_cast hbudget
  have hne' : A ≠ 1 ∨ B ≠ 1 ∨ C ≠ 1 := by omega
  let R : ℤ := ((2 ^ m - m - 1 : ℕ) : ℤ) + (1-A)*(g x).val +
    (1-B)*(g y).val + (1-C)*(g z).val - q*N
  have hRpos : 0 ≤ R := by dsimp [R]; omega
  let r := R.toNat
  have hr : (r : ℤ) = R := Int.toNat_of_nonneg hRpos
  have hrbound : (r : ℤ) < (6 - ((A+B+C : ℕ) : ℤ)) * (2 ^ (m - 1) - 1) - m + 2 := by
    rw [hr]
    push_cast
    dsimp [R]
    nlinarith [hbad.2]
  obtain ⟨s, hscard, hssum⟩ := exists_fixed_sum_three_extra_budget (N := N) hm habc hrbound
  apply not_validTuple_of_three_extra_block_rival g f hprefix x y z hxy hxz hyz hx hy hz
    hne' (by omega) ⟨s, hscard, hssum⟩ _ hg
  have heq : (r : ℤ) + A*(g x).val + B*(g y).val + C*(g z).val =
      ((2 ^ m - m - 1 : ℕ) : ℤ) + (g x).val + (g y).val + (g z).val - q*N := by
    rw [hr]
    dsimp [R]
    ring
  have hc := congrArg (fun v : ℤ ↦ (v : ZMod N)) heq
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, sub_zero,
    nsmul_eq_mul, hsum] using hc

set_option maxHeartbeats 10000000 in
/-- Uniform interval obstruction, with no enumeration premise. The twelve
explicit inequalities below force a contradiction for all these parameters. -/
theorem three_extra_interval_obstruction
    (m L N X Y Z : ℤ) (hm : 10 ≤ m) (hL : 8 * m ≤ L)
    (hNlo : 8 * L + 8 ≤ N) (hNhi : N ≤ 16 * L + 15)
    (hXlo : 2 * L + m ≤ X)
    (hYgap : 2 * L - m + 1 + X < Y)
    (hZgap : 2 * L - m + 1 + Y < Z)
    (hZhi : 2 * L - m + 1 + Z < N)
    (hno : ∀ a b c : ℤ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c ≤ 5 →
      (a ≠ 1 ∨ b ≠ 1 ∨ c ≠ 1) → ∀ q : ℤ,
      2 * L - m + 1 + (1-a)*X + (1-b)*Y + (1-c)*Z < q*N ∨
      q*N + (6-a-b-c)*L-m+2 ≤ 2*L-m+1+(1-a)*X+(1-b)*Y+(1-c)*Z) : False := by
  have h_0 := hno 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (1)
  have h_1 := hno 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (2)
  have h_2 := hno 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) (1)
  have h_3 := hno 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega) (0)
  have h_4 := hno 0 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (1)
  have h_5 := hno 0 3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (0)
  have h_6 := hno 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (1)
  have h_7 := hno 1 3 1 (by omega) (by omega) (by omega) (by omega) (by omega) (-1)
  have h_8 := hno 2 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (1)
  have h_9 := hno 3 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) (0)
  have h_10 := hno 4 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) (0)
  have h_11 := hno 4 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (0)
  omega

/-- The interval parameters grow sufficiently rapidly from prefix length ten. -/
theorem eight_mul_le_mersenne_pred {m : ℕ} (hm : 10 ≤ m) :
    8 * m ≤ 2 ^ (m - 1) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Nat.add_sub_cancel] at *
    omega

set_option maxHeartbeats 20000000 in
/-- Three additional rivals strengthen the interval argument to every
prefix length at least four, with only linear growth required of L. -/
theorem three_extra_interval_obstruction_strengthened
    (m L N X Y Z : ℤ) (hm : 4 ≤ m) (hL : 2 * m - 1 ≤ L)
    (hNlo : 8 * L + 8 ≤ N) (hNhi : N ≤ 16 * L + 15)
    (hXlo : 2 * L + m ≤ X)
    (hYgap : 2 * L - m + 1 + X < Y)
    (hZgap : 2 * L - m + 1 + Y < Z)
    (hZhi : 2 * L - m + 1 + Z < N)
    (hno : ∀ a b c : ℤ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c ≤ 5 →
      (a ≠ 1 ∨ b ≠ 1 ∨ c ≠ 1) → ∀ q : ℤ,
      2 * L - m + 1 + (1-a)*X + (1-b)*Y + (1-c)*Z < q*N ∨
      q*N + (6-a-b-c)*L-m+2 ≤ 2*L-m+1+(1-a)*X+(1-b)*Y+(1-c)*Z) : False := by
  have h₀ := hno 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have h₁ := hno 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) 2
  have h₂ := hno 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have h₃ := hno 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have h₅ := hno 0 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have h₇ := hno 0 3 0 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have h₁₁ := hno 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have h₁₄ := hno 1 3 1 (by omega) (by omega) (by omega) (by omega) (by omega) (-1)
  have h₁₆ := hno 2 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have h₁₉ := hno 3 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have h₂₄ := hno 4 0 1 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have h₂₅ := hno 4 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have hnew₀ := hno 3 0 0 (by omega) (by omega) (by omega) (by omega) (by omega) 1
  have hnew₁ := hno 0 3 1 (by omega) (by omega) (by omega) (by omega) (by omega) (-1)
  have hnew₂ := hno 1 0 3 (by omega) (by omega) (by omega) (by omega) (by omega) (-1)
  omega

/-- The strengthened linear growth bound holds from prefix length four. -/
theorem twice_mul_sub_one_le_mersenne_pred {m : ℕ} (hm : 4 ≤ m) :
    2 * m - 1 ≤ 2 ^ (m - 1) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Nat.add_sub_cancel] at *
    omega

/-- Three ordered extras cannot all miss the next SI entry below the
binary threshold. The rival argument is uniform in both dimension and modulus. -/
theorem not_validTuple_of_ordered_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hupper : N < 2 ^ (m + 3))
    (g : Fin (m + 3) → ZMod N) (f : Fin m ↪ Fin (m + 3))
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y z : Fin (m + 3)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y) (hz : ∀ i, f i ≠ z)
    (hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y + g z)
    (hxnext : g x ≠ (a m : ZMod N)) (_hynext : g y ≠ (a m : ZMod N))
    (hznext : g z ≠ (a m : ZMod N))
    (horderxy : (g x).val ≤ (g y).val) (horderyz : (g y).val ≤ (g z).val) :
    ¬ ValidTuple g := by
  intro hg
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 3 - 1 = m + 2 by omega] at hbinary
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hmexp := Nat.lt_two_pow_self (n := m)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow2 : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [pow_add, hpow]; norm_num; ring
  have hpow3 : 2 ^ (m + 3) = 16 * 2 ^ (m - 1) := by
    rw [pow_add, hpow]; norm_num; ring
  have hNlo : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N := by omega
  have hloc (j : Fin (m + 3)) (hj : ∀ i, f i ≠ j)
      (hnext : g j ≠ (a m : ZMod N)) :=
    fixed_prefix_extra_localization (by omega : 3 ≤ m) hNlo
      (Fin.lastCases (g j) (fun i : Fin m ↦ (a i.val : ZMod N)))
      (validTuple_fixed_embedding_with_outside g hg f hprefix j hj)
      (by intro i; simp) (by simpa only [Fin.lastCases_last] using hnext)
  have hlocx := hloc x hx hxnext
  have hlocz := hloc z hz hznext
  simp only [Fin.lastCases_last] at hlocx hlocz
  let L : ℤ := 2 ^ (m - 1) - 1
  have hLcast : ((2 ^ (m - 1) - 1 : ℕ) : ℤ) = L := by
    dsimp [L]; rw [Int.natCast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hScast : ((2 ^ m - m - 1 : ℕ) : ℤ) = 2 * L - m + 1 := by
    have hpowz : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by exact_mod_cast hpow
    rw [Int.natCast_sub (by omega), Int.natCast_sub (by omega), Nat.cast_pow]
    push_cast
    dsimp [L]
    omega
  have hno := three_extra_initial_interval_excluded (by omega : 4 ≤ m)
    g hg f hprefix x y z hxy hxz hyz hx hy hz hsum
  rw [hScast] at hno
  change ∀ A B C : ℤ, 0 ≤ A → 0 ≤ B → 0 ≤ C → A+B+C ≤ 5 →
    (A ≠ 1 ∨ B ≠ 1 ∨ C ≠ 1) → ∀ q : ℤ,
    2*L-m+1+(1-A)*(g x).val+(1-B)*(g y).val+(1-C)*(g z).val < q*N ∨
    q*N+(6-A-B-C)*L-m+2 ≤ 2*L-m+1+(1-A)*(g x).val+(1-B)*(g y).val+(1-C)*(g z).val at hno
  have hgapxy := hno 0 2 1 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have hgapyz := hno 1 0 2 (by omega) (by omega) (by omega) (by omega) (by omega) 0
  have hLbound : 2 * (m : ℤ) - 1 ≤ L := by
    have h := twice_mul_sub_one_le_mersenne_pred hm
    have h' : (((2 * m - 1 : ℕ) : ℤ)) ≤ ((2 ^ (m - 1) - 1 : ℕ) : ℤ) := by exact_mod_cast h
    have hcast : ((2 * m - 1 : ℕ) : ℤ) = 2 * m - 1 := by omega
    rwa [hcast, hLcast] at h'
  have hlocxz : 4 * L + 1 ≤ 2 * L - m + 1 + (g x).val := by
    have h := hlocx.1
    have h' : (4 : ℤ) * ((2 ^ (m - 1) - 1 : ℕ) : ℤ) + 1 ≤
        ((2 ^ m - m - 1 : ℕ) : ℤ) + (g x).val := by exact_mod_cast h
    rwa [hLcast, hScast] at h'
  have hloczz : 2 * L - m + 1 + (g z).val < N := by
    have h' : ((2 ^ m - m - 1 : ℕ) : ℤ) + (g z).val < N := by exact_mod_cast hlocz.2
    rwa [hScast] at h'
  have hNl : 8 * L + 8 ≤ (N : ℤ) := by
    have h' : 8 * (2 : ℤ) ^ (m - 1) ≤ N := by exact_mod_cast (hpow2 ▸ hbinary)
    dsimp [L]; omega
  have hNu : (N : ℤ) ≤ 16 * L + 15 := by
    have h' : (N : ℤ) < 16 * (2 : ℤ) ^ (m - 1) := by exact_mod_cast (hpow3 ▸ hupper)
    dsimp [L]; omega
  exact three_extra_interval_obstruction_strengthened m L N (g x).val (g y).val (g z).val
    (by exact_mod_cast hm) hLbound hNl hNu (by omega) (by omega) (by omega) hloczz hno

/-- A coherent prefix with three arbitrary extras extends by one entry
at every subbinary modulus, uniformly for prefix length at least four. -/
theorem exists_tail_eq_next_of_valid_fixed_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hupper : N < 2 ^ (m + 3))
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = (a i.val : ZMod N)) :
    ∃ j : Fin (m + 3), m ≤ j.val ∧ g j = (a m : ZMod N) := by
  by_contra hnone
  push Not at hnone
  let x : Fin (m + 3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m + 3) := (Fin.last (m + 1)).castSucc
  let z : Fin (m + 3) := Fin.last (m + 2)
  let f : Fin m ↪ Fin (m + 3) :=
    ⟨fun i ↦ i.castSucc.castSucc.castSucc,
      (Fin.castSucc_injective (m + 2)).comp
        ((Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m))⟩
  have houtside (j : Fin (m + 3)) (hj : m ≤ j.val) : ∀ i, f i ≠ j := by
    intro i heq
    have hv := congrArg Fin.val heq
    simp only [f, Function.Embedding.coeFn_mk, Fin.val_castSucc] at hv
    omega
  have hx := houtside x (by simp [x])
  have hy := houtside y (by simp [y])
  have hz := houtside z (by simp [z])
  have hxy : x ≠ y := by intro h; have := congrArg Fin.val h; simp [x, y] at this
  have hxz : x ≠ z := by intro h; have := congrArg Fin.val h; simp [x, z] at this
  have hyz : y ≠ z := by intro h; have := congrArg Fin.val h; simp [y, z] at this
  have hxnext := hnone x (by simp [x])
  have hynext := hnone y (by simp [y])
  have hznext := hnone z (by simp [z])
  have hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y + g z := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole, x, y, z]
  have hbad := not_validTuple_of_ordered_three_extra_prefix hm hupper g f hprefix
  rcases le_total (g x).val (g y).val with h₁ | h₁
  · rcases le_total (g y).val (g z).val with h₂ | h₂
    · exact hbad x y z hxy hxz hyz hx hy hz hsum hxnext hynext hznext h₁ h₂ hg
    · rcases le_total (g x).val (g z).val with h₃ | h₃
      · exact hbad x z y hxz hxy hyz.symm hx hz hy (by rw [hsum]; abel)
          hxnext hznext hynext h₃ h₂ hg
      · exact hbad z x y hxz.symm hyz.symm hxy hz hx hy (by rw [hsum]; abel)
          hznext hxnext hynext h₃ h₁ hg
  · rcases le_total (g x).val (g z).val with h₂ | h₂
    · exact hbad y x z hxy.symm hyz hxz hy hx hz (by rw [hsum]; abel)
        hynext hxnext hznext h₁ h₂ hg
    · rcases le_total (g y).val (g z).val with h₃ | h₃
      · exact hbad y z x hyz hxy.symm hxz.symm hy hz hx (by rw [hsum]; abel)
          hynext hznext hxnext h₃ h₂ hg
      · exact hbad z y x hyz.symm hxz.symm hxy.symm hz hy hx (by rw [hsum]; abel)
          hznext hynext hxnext h₃ h₁ hg

/-- The actual extracted coordinate extends the coherent prefix after
one swap, leaving exactly two unrestricted coordinates. -/
theorem exists_perm_short_prefix_of_valid_fixed_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hupper : N < 2 ^ (m + 3))
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = (a i.val : ZMod N)) :
    ∃ p : Equiv.Perm (Fin (m + 3)),
      ∀ i : Fin (m + 1), g (p i.castSucc.castSucc) = (a i.val : ZMod N) := by
  obtain ⟨j, hj, hnext⟩ := exists_tail_eq_next_of_valid_fixed_three_extra_prefix hm hupper g hg hprefix
  let x : Fin (m + 3) := (Fin.last m).castSucc.castSucc
  let p := Equiv.swap x j
  refine ⟨p, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simpa only [p, x, Equiv.swap_apply_left, Fin.val_last] using hnext
  · have hfix : p k.castSucc.castSucc.castSucc = k.castSucc.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [x, Fin.val_castSucc, Fin.val_last] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castSucc] at hv
        omega
    rw [hfix, hprefix]
    rfl

/-- Three-extra coherent prefixes have fixed-set validity at the same
subbinary modulus, with no conjectural descent input. -/
theorem valid_fixed_of_valid_fixed_three_extra_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = (a i.val : ZMod N))
    (hupper : N < 2 ^ (m + 3)) : Valid (m + 3) N := by
  obtain ⟨p, hp⟩ := exists_perm_short_prefix_of_valid_fixed_three_extra_prefix hm hupper g hg hprefix
  exact valid_fixed_of_valid_scaled_fixed_short_prefix_lt_two_pow
    (by omega : 3 ≤ m + 1) g hg p 1 0 (by intro i; simpa using hp i) hupper

/-- Unit-affine normalization preserves the three-extra same-modulus theorem. -/
theorem valid_fixed_of_valid_affine_three_extra_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 3))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b)
    (hupper : N < 2 ^ (m + 3)) : Valid (m + 3) N := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  exact valid_fixed_of_valid_fixed_three_extra_prefix_lt_two_pow hm
    (fun i ↦ φ.symm (g (e i) - b)) hw (by intro i; simp [hprefix]) hupper

/-- Full global lower bound for coherent unit-affine SI prefixes of
length n-3 and three arbitrary extras, every n>=7 and positive modulus. -/
theorem global_lower_bound_of_valid_affine_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 3))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b) :
    globalBound (m + 3) ≤ N := by
  by_cases hupper : N < 2 ^ (m + 3)
  · have hv := valid_fixed_of_valid_affine_three_extra_prefix_lt_two_pow hm g hg e φ b hprefix hupper
    have hbinary := two_pow_pred_le_card_of_validTuple g hg
    simp only [ZMod.card] at hbinary
    have htwo : 2 ≤ 2 ^ (m + 3 - 1) := by
      exact Nat.le_self_pow (by omega) 2
    exact (nmin_eq (by omega : 2 ≤ m + 3)).2 ⟨by omega, hv⟩
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- The same three-extra class satisfies every exact stratum, including
the odd stratum. No unrestricted G1, G2, or G3 premise is used. -/
theorem stratum_lower_bound_of_valid_affine_three_extra_prefix
    {m s q : ℕ} (hm : 4 ≤ m) (hq : Odd q)
    (g : Fin (m + 3) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 3)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b) :
    stratumBound (m + 3) s ≤ 2 ^ s * q := by
  have hqpos := hq.pos
  letI : NeZero (2 ^ s * q) := ⟨by positivity⟩
  by_cases hupper : 2 ^ s * q < 2 ^ (m + 3)
  · exact stratum_lower_bound_of_valid_fixed (by omega) hq
      (valid_fixed_of_valid_affine_three_extra_prefix_lt_two_pow hm g hg e φ b hprefix hupper)
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- Subbinary moduli in the three-extra coherent class are exactly
admissible fixed-set power gaps; this does not classify arbitrary tuples. -/
theorem exists_admissible_power_gap_of_valid_affine_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 3))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b)
    (hupper : N < 2 ^ (m + 3)) :
    ∃ t < m + 3, 2 ^ t ≤ m + 3 ∧ N = 2 ^ (m + 3) - 2 ^ t := by
  have hv := valid_fixed_of_valid_affine_three_extra_prefix_lt_two_pow hm g hg e φ b hprefix hupper
  have hb := global_lower_bound_of_valid_affine_three_extra_prefix hm g hg e φ b hprefix
  have hN2 : 2 ≤ N := (nmin_eq (by omega : 2 ≤ m + 3)).1.1.trans hb
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow (by omega) hN2 hupper hv
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 3 ≠ 0)
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
  refine ⟨t, ht, ?_, hgap⟩
  unfold globalBound at hb
  rw [hgap] at hb
  omega

/-- Critical tuples in any exact stratum cannot contain the specified
coherent unit-affine prefix of length n-3, for n>=7. -/
theorem not_validTuple_of_critical_affine_three_extra_prefix
    {m s q : ℕ} (hm : 4 ≤ m) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound (m + 3) s)
    (g : Fin (m + 3) → ZMod (2 ^ s * q))
    (e : Equiv.Perm (Fin (m + 3)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b) :
    ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge (stratum_lower_bound_of_valid_affine_three_extra_prefix
    hm hq g hg e φ b hprefix)) hcritical

/-- Below the last two binary residues, extending the three-extra prefix
and consuming two-extra extraction recovers the entire actual fixed tuple. -/
theorem exists_perm_fixed_of_valid_three_extra_prefix_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : N ≤ 2 ^ (m + 3) - 3)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = (a i.val : ZMod N)) :
    ∃ p : Equiv.Perm (Fin (m + 3)), ∀ i, g (p i) = (a i.val : ZMod N) := by
  have hupper : N < 2 ^ (m + 3) :=
    lt_of_le_of_lt hN (Nat.sub_lt (by positivity) (by omega))
  obtain ⟨p, hp⟩ := exists_perm_short_prefix_of_valid_fixed_three_extra_prefix hm hupper g hg hprefix
  obtain ⟨q, hq⟩ := exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le
    (by omega : 5 ≤ m + 1) hN (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg) hp
  exact ⟨q.trans p, hq⟩

/-- Whole-tuple extraction retains the original unit-affine map. It
applies in every n>=7 with N<=2^n-3, not to arbitrary tuples without a prefix. -/
theorem exists_perm_affine_fixed_of_valid_three_extra_prefix_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : N ≤ 2 ^ (m + 3) - 3)
    (g : Fin (m + 3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 3))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (a i.val) + b) :
    ∃ p : Equiv.Perm (Fin (m + 3)), ∀ i, g (p i) = φ (a i.val) + b := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  obtain ⟨p, hp⟩ := exists_perm_fixed_of_valid_three_extra_prefix_of_modulus_le hm hN
    (fun i ↦ φ.symm (g (e i) - b)) hw (by intro i; simp [hprefix])
  refine ⟨p.trans e, ?_⟩
  intro i
  have h := congrArg φ (hp i)
  rw [φ.apply_symm_apply] at h
  change g (e (p i)) = _
  exact (sub_eq_iff_eq_add).mp h

end MinModulus
