import MinModulus.SILiftShift
import MinModulus.SILiftDigit

/-!
# Representations with a reserved low block

To flip the sheet parity of a rival one needs a realizing coin family of a
PRESCRIBED shape, and `exists_two_of_dsum_gt` only supplies half of it.
This file supplies the rest for the shape that actually matters.

The sheet bit at exponent `0` can never be probed (`val_mod_two`), so a
sheet-bit vector that is non-constant away from exponent `0` differs
between some exponent `u ≥ 2` and exponent `1`.  Toggling the pair
`(u, 1)` needs

* **two coins at exponent `0`** and **one coin at exponent `u`**,

for `flipMove` at `c = 1` when `u = 2`, and for `shiftMove` with `j = u`,
`q = 0` when `u ≥ 3` — the requirement is the same in both cases.

`exists_reserved_rep` builds exactly such a family: it represents the
remainder `V - 2 ^ u - 2` with three fewer coins and then lays the reserved
block on top.
-/

namespace MinModulus

open Finset

section Reserve

variable {w u : ℕ}

/-- Two coins at exponent `0` and one at exponent `u`, on top of `kR`. -/
def reserve (kR : ℕ → ℕ) (u : ℕ) : ℕ → ℕ :=
  fun i => kR i + (if i = 0 then 2 else 0) + (if i = u then 1 else 0)

private lemma sum_indicator (c : ℕ) (p : ℕ) (hp : p < w) (g : ℕ → ℕ) :
    ∑ i ∈ range w, (if i = p then c else 0) * g i = c * g p := by
  have hmem : p ∈ range w := Finset.mem_range.mpr hp
  rw [← Finset.add_sum_erase (range w) _ hmem]
  have hz : ∑ i ∈ (range w).erase p, (if i = p then c else 0) * g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring
  rw [hz, if_pos rfl]
  ring

lemma reserve_val (hu : 1 ≤ u) (huw : u < w) (kR : ℕ → ℕ) :
    val w (reserve kR u) = val w kR + 2 + 2 ^ u := by
  unfold val reserve
  have hsplit : ∀ i ∈ range w,
      (kR i + (if i = 0 then 2 else 0) + (if i = u then 1 else 0)) * 2 ^ i
        = kR i * 2 ^ i + (if i = 0 then 2 else 0) * 2 ^ i
          + (if i = u then 1 else 0) * 2 ^ i := fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib,
    sum_indicator 2 0 (by omega) (fun i => 2 ^ i),
    sum_indicator 1 u huw (fun i => 2 ^ i)]
  ring

lemma reserve_dsum (hu : 1 ≤ u) (huw : u < w) (kR : ℕ → ℕ) :
    dsum w (reserve kR u) = dsum w kR + 3 := by
  unfold dsum reserve
  have hsplit : ∀ i ∈ range w,
      kR i + (if i = 0 then 2 else 0) + (if i = u then 1 else 0)
        = kR i + (if i = 0 then 2 else 0) * 1 + (if i = u then 1 else 0) * 1 :=
    fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib,
    sum_indicator 2 0 (by omega) (fun _ => 1),
    sum_indicator 1 u huw (fun _ => 1)]

lemma reserve_at_zero (hu : 1 ≤ u) (kR : ℕ → ℕ) : 2 ≤ reserve kR u 0 := by
  unfold reserve
  rw [if_pos rfl, if_neg (by omega)]
  omega

lemma reserve_at (hu : 1 ≤ u) (kR : ℕ → ℕ) : 1 ≤ reserve kR u u := by
  unfold reserve
  rw [if_pos rfl, if_neg (by omega)]
  omega

/-- **A realizing family of the prescribed shape.**  If the remainder
`V - 2 ^ u - 2` can be represented on exponents `< w` with `c - 3` coins,
then `V` can be represented with `c` coins by a family carrying two coins
at exponent `0` and one at exponent `u`. -/
theorem exists_reserved_rep (hu : 1 ≤ u) (huw : u < w) {V c : ℕ}
    (hV : 2 ^ u + 2 ≤ V) (hc : 3 ≤ c)
    (hex : ∃ kR, val w kR = V - 2 ^ u - 2 ∧ dsum w kR = c - 3) :
    ∃ k, val w k = V ∧ dsum w k = c ∧ 2 ≤ k 0 ∧ 1 ≤ k u := by
  obtain ⟨kR, hv, hd⟩ := hex
  refine ⟨reserve kR u, ?_, ?_, reserve_at_zero hu kR, reserve_at hu kR⟩
  · rw [reserve_val hu huw, hv]
    have h1 : (1 : ℕ) ≤ 2 ^ u := Nat.one_le_pow _ _ (by norm_num)
    omega
  · rw [reserve_dsum hu huw, hd]; omega

/-- The remainder hypothesis discharged by the standard digit interval:
a value below `2 ^ w` is representable with any coin count between its
popcount and itself. -/
theorem exists_reserved_rep_of_interval (hu : 1 ≤ u) (huw : u < w) {V c : ℕ}
    (hV : 2 ^ u + 2 ≤ V) (hc : 3 ≤ c)
    (hlt : V - 2 ^ u - 2 < 2 ^ w)
    (hlow : s2 (V - 2 ^ u - 2) ≤ c - 3)
    (hhigh : c - 3 ≤ V - 2 ^ u - 2) :
    ∃ k, val w k = V ∧ dsum w k = c ∧ 2 ≤ k 0 ∧ 1 ≤ k u := by
  refine exists_reserved_rep hu huw hV hc ?_
  obtain ⟨kR, _, hv, hd⟩ := binary_rep w (V - 2 ^ u - 2) hlt
  exact exists_dsum_eq ⟨kR, hv, by omega⟩ hhigh

/-! ### Both sheet parities are realized -/

/-- **Both parities.**  At a target admitting a reserved-shape
representation, a sheet-bit vector whose values at exponents `u` and `1`
differ admits realizing families of BOTH sheet parities: `flipMove` at
`c = 1` handles `u = 2`, and `shiftMove` with `j = u`, `q = 0` handles
`u ≥ 3`.  Both need exactly the reserved block. -/
theorem exists_both_parities (b : ℕ → ℕ) (hu : 2 ≤ u) (huw : u < w)
    {V cnt : ℕ} (hV : 2 ^ u + 2 ≤ V) (hc : 3 ≤ cnt)
    (hex : ∃ kR, val w kR = V - 2 ^ u - 2 ∧ dsum w kR = cnt - 3)
    (hne : b u % 2 ≠ b 1 % 2) :
    ∃ k k', (val w k = V ∧ dsum w k = cnt)
      ∧ (val w k' = V ∧ dsum w k' = cnt)
      ∧ sheetSum w b k' % 2 ≠ sheetSum w b k % 2 := by
  obtain ⟨k, hv, hd, h0, hku⟩ :=
    exists_reserved_rep (by omega) huw hV hc hex
  rcases Nat.lt_or_ge u 3 with h3 | h3
  · -- `u = 2`: the adjacent three-point move at `c = 1`
    obtain rfl : u = 2 := by omega
    obtain ⟨hd', hv', hp⟩ :=
      flipMove_rival (m := w) (c := 1) (k := k) b (by omega) (by omega)
        (by simpa using h0) (by simpa using hku)
        (by simpa using Ne.symm hne)
    exact ⟨k, flipMove k 1, ⟨hv, hd⟩, ⟨by rw [hv', hv], by rw [hd', hd]⟩, hp⟩
  · -- `u ≥ 3`: the split-and-merge move with `j = u`, `q = 0`
    obtain ⟨hd', hv', hp⟩ :=
      shiftMove_rival (m := w) (j := u) (q := 0) (k := k) b (by omega) huw
        (by omega) (Or.inl (by omega)) hku (by simpa using h0)
        (by simpa using hne)
    exact ⟨k, shiftMove k u 0, ⟨hv, hd⟩, ⟨by rw [hv', hv], by rw [hd', hd]⟩, hp⟩

/-- **Parity on demand.**  Since the two families of `exists_both_parities`
have opposite parities, every prescribed parity is realized. -/
theorem exists_rep_of_parity (b : ℕ → ℕ) (hu : 2 ≤ u) (huw : u < w)
    {V cnt : ℕ} (hV : 2 ^ u + 2 ≤ V) (hc : 3 ≤ cnt)
    (hex : ∃ kR, val w kR = V - 2 ^ u - 2 ∧ dsum w kR = cnt - 3)
    (hne : b u % 2 ≠ b 1 % 2) (p : ℕ) :
    ∃ k, val w k = V ∧ dsum w k = cnt ∧ sheetSum w b k % 2 = p % 2 := by
  obtain ⟨k, k', ⟨hv, hd⟩, ⟨hv', hd'⟩, hp⟩ :=
    exists_both_parities b hu huw hV hc hex hne
  rcases Nat.lt_or_ge (sheetSum w b k % 2) (p % 2) with h | h
  · exact ⟨k', hv', hd', by omega⟩
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact ⟨k, hv, hd, by omega⟩
    · exact ⟨k', hv', hd', by omega⟩

/-! ### The SI-lift specialization -/

/-- **Parity-refined digit cover, SI-lift parameters.**  Width `n - 1`
(exponents `0 .. n - 2`) and exactly `n` coins, which is the shape of a
rival omitting the extra entry.  For a sheet-bit vector differing between
exponents `u ≥ 2` and `1`, every target in range is realized with EITHER
prescribed sheet parity.

The arithmetic side-conditions say that the remainder `r - 2 ^ u - 2` fits
in width `n - 1` and that `n - 3` lies in its achievable coin interval
`[s2 R, R]`.  Since `s2 R ≤ n - 1` always, the popcount condition can fail
only for the thin set of remainders with `s2 R ∈ {n - 2, n - 1}`. -/
theorem si_exists_rep_of_parity {n u : ℕ} (b : ℕ → ℕ) (hn : 5 ≤ n)
    (hu : 2 ≤ u) (huw : u < n - 1) {r : ℕ}
    (hr : 2 ^ u + 2 ≤ r)
    (hlt : r - 2 ^ u - 2 < 2 ^ (n - 1))
    (hlow : s2 (r - 2 ^ u - 2) ≤ n - 3)
    (hhigh : n - 3 ≤ r - 2 ^ u - 2)
    (hne : b u % 2 ≠ b 1 % 2) (p : ℕ) :
    ∃ k, val (n - 1) k = r ∧ dsum (n - 1) k = n
      ∧ sheetSum (n - 1) b k % 2 = p % 2 := by
  refine exists_rep_of_parity b hu huw hr (by omega) ?_ hne p
  obtain ⟨kR, _, hv, hd⟩ := binary_rep (n - 1) (r - 2 ^ u - 2) hlt
  exact exists_dsum_eq ⟨kR, hv, by omega⟩ hhigh

end Reserve

/-! ### The general reserved block

`reserve` fixes the block at exponents `0` and `u`, which forces the toggle
pair to be `(u, 1)`.  Allowing the two coins to sit at an arbitrary exponent
`a` and the single coin at an arbitrary `x` gives the toggle pair
`(x, a + 1)` and a far larger supply of usable targets: an exhaustive count
over all rival shapes at `(n,s) = (6,2), (7,2), (8,2), (8,3), (9,3)` puts the
coverage of the general block above 95% of the targets that admit both
parities at all, against about 50% for the fixed block.

Note `1 ≤ x` is essential: exponent `0` can never be toggled
(`val_mod_two`), and dropping the hypothesis makes the statement false. -/

section ReserveTwo

variable {w a x : ℕ}

/-- Two coins at exponent `a` and one at exponent `x ≠ a`, on top of `kR`. -/
def reserveTwo (kR : ℕ → ℕ) (a x : ℕ) : ℕ → ℕ :=
  fun i => kR i + (if i = a then 2 else 0) + (if i = x then 1 else 0)

lemma reserveTwo_val (haw : a < w) (hxw : x < w) (kR : ℕ → ℕ) :
    val w (reserveTwo kR a x) = val w kR + 2 * 2 ^ a + 2 ^ x := by
  unfold val reserveTwo
  have hsplit : ∀ i ∈ range w,
      (kR i + (if i = a then 2 else 0) + (if i = x then 1 else 0)) * 2 ^ i
        = kR i * 2 ^ i + (if i = a then 2 else 0) * 2 ^ i
          + (if i = x then 1 else 0) * 2 ^ i := fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_indicator 2 a haw (fun i => 2 ^ i),
    sum_indicator 1 x hxw (fun i => 2 ^ i)]
  ring

lemma reserveTwo_dsum (haw : a < w) (hxw : x < w) (kR : ℕ → ℕ) :
    dsum w (reserveTwo kR a x) = dsum w kR + 3 := by
  unfold dsum reserveTwo
  have hsplit : ∀ i ∈ range w,
      kR i + (if i = a then 2 else 0) + (if i = x then 1 else 0)
        = kR i + (if i = a then 2 else 0) * 1 + (if i = x then 1 else 0) * 1 :=
    fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_indicator 2 a haw (fun _ => 1),
    sum_indicator 1 x hxw (fun _ => 1)]

lemma reserveTwo_at_a (hxa : x ≠ a) (kR : ℕ → ℕ) :
    2 ≤ reserveTwo kR a x a := by
  unfold reserveTwo
  rw [if_pos rfl, if_neg (Ne.symm hxa)]
  omega

lemma reserveTwo_at_x (hxa : x ≠ a) (kR : ℕ → ℕ) :
    1 ≤ reserveTwo kR a x x := by
  unfold reserveTwo
  rw [if_pos rfl, if_neg hxa]
  omega

/-- A realizing family with two coins at `a` and one at `x`. -/
theorem exists_reserved_two (hxa : x ≠ a) (haw : a < w) (hxw : x < w)
    {V cnt : ℕ} (hV : 2 * 2 ^ a + 2 ^ x ≤ V) (hc : 3 ≤ cnt)
    (hex : ∃ kR, val w kR = V - 2 * 2 ^ a - 2 ^ x ∧ dsum w kR = cnt - 3) :
    ∃ k, val w k = V ∧ dsum w k = cnt ∧ 2 ≤ k a ∧ 1 ≤ k x := by
  obtain ⟨kR, hv, hd⟩ := hex
  refine ⟨reserveTwo kR a x, ?_, ?_, reserveTwo_at_a hxa kR,
    reserveTwo_at_x hxa kR⟩
  · rw [reserveTwo_val haw hxw, hv]; omega
  · rw [reserveTwo_dsum haw hxw, hd]; omega

/-- **Both parities, general block.**  The reserved block at `(a, x)`
toggles the pair `(x, a + 1)`: `shiftMove` with `j = x`, `q = a` handles
`x < a` and `x > a + 2`, and `flipMove` at `c = a + 1` handles the
remaining adjacent case `x = a + 2`. -/
theorem exists_both_parities_two (b : ℕ → ℕ) (hx1 : 1 ≤ x) (haw1 : a + 1 < w)
    (hxw : x < w) (hxa : x ≠ a) (hxa1 : x ≠ a + 1)
    {V cnt : ℕ} (hV : 2 * 2 ^ a + 2 ^ x ≤ V) (hc : 3 ≤ cnt)
    (hex : ∃ kR, val w kR = V - 2 * 2 ^ a - 2 ^ x ∧ dsum w kR = cnt - 3)
    (hne : b x % 2 ≠ b (a + 1) % 2) :
    ∃ k k', (val w k = V ∧ dsum w k = cnt)
      ∧ (val w k' = V ∧ dsum w k' = cnt)
      ∧ sheetSum w b k' % 2 ≠ sheetSum w b k % 2 := by
  obtain ⟨k, hv, hd, ha, hx⟩ :=
    exists_reserved_two hxa (by omega) hxw hV hc hex
  rcases Nat.lt_or_ge x a with hlt | hge
  · -- `x < a`: the split-and-merge move, `j < q`
    obtain ⟨hd', hv', hp⟩ :=
      shiftMove_rival (m := w) (j := x) (q := a) (k := k) b hx1 hxw
        (by omega) (Or.inr hlt) hx ha hne
    exact ⟨k, shiftMove k x a, ⟨hv, hd⟩, ⟨by rw [hv', hv], by rw [hd', hd]⟩, hp⟩
  · rcases Nat.eq_or_lt_of_le (show a + 2 ≤ x by omega) with heq | hgt
    · -- `x = a + 2`: the adjacent three-point move at `c = a + 1`
      obtain ⟨hd', hv', hp⟩ :=
        flipMove_rival (m := w) (c := a + 1) (k := k) b (by omega) (by omega)
          (by simpa using ha) (by rw [show a + 1 + 1 = x from by omega]; exact hx)
          (by rw [show a + 1 + 1 = x from by omega]; exact Ne.symm hne)
      exact ⟨k, flipMove k (a + 1), ⟨hv, hd⟩,
        ⟨by rw [hv', hv], by rw [hd', hd]⟩, hp⟩
    · -- `x > a + 2`: the split-and-merge move, `q + 1 < j - 1`
      obtain ⟨hd', hv', hp⟩ :=
        shiftMove_rival (m := w) (j := x) (q := a) (k := k) b hx1 hxw
          (by omega) (Or.inl (by omega)) hx ha hne
      exact ⟨k, shiftMove k x a, ⟨hv, hd⟩,
        ⟨by rw [hv', hv], by rw [hd', hd]⟩, hp⟩

/-- Parity on demand, general block. -/
theorem exists_rep_of_parity_two (b : ℕ → ℕ) (hx1 : 1 ≤ x) (haw1 : a + 1 < w)
    (hxw : x < w) (hxa : x ≠ a) (hxa1 : x ≠ a + 1)
    {V cnt : ℕ} (hV : 2 * 2 ^ a + 2 ^ x ≤ V) (hc : 3 ≤ cnt)
    (hex : ∃ kR, val w kR = V - 2 * 2 ^ a - 2 ^ x ∧ dsum w kR = cnt - 3)
    (hne : b x % 2 ≠ b (a + 1) % 2) (p : ℕ) :
    ∃ k, val w k = V ∧ dsum w k = cnt ∧ sheetSum w b k % 2 = p % 2 := by
  obtain ⟨k, k', ⟨hv, hd⟩, ⟨hv', hd'⟩, hp⟩ :=
    exists_both_parities_two b hx1 haw1 hxw hxa hxa1 hV hc hex hne
  rcases Nat.lt_or_ge (sheetSum w b k % 2) (p % 2) with h | h
  · exact ⟨k', hv', hd', by omega⟩
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact ⟨k, hv, hd, by omega⟩
    · exact ⟨k', hv', hd', by omega⟩

end ReserveTwo

end MinModulus
