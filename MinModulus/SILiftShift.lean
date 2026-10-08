import MinModulus.SILiftFlip

/-!
# The split-and-merge move

`flipMove` toggles the sheet parity at an ADJACENT pair `(c, c+1)`, which
forces the prescribed non-constant pair of sheet bits to be adjacent and
demands coins on both sides of `c`.  The move here removes both
restrictions by decoupling the two toggles into independent halves:

* `splitAt k j` takes one coin at `j` and puts two at `j - 1`.  The value
  is unchanged (`2 ^ j = 2 * 2 ^ (j-1)`), the coin count goes UP by one,
  and the multiplicity parity toggles at `j` alone — the `+2` at `j - 1`
  cannot change a parity.
* `mergeAt k q` takes two coins at `q` and puts one at `q + 1`.  The value
  is unchanged, the coin count goes DOWN by one, and the parity toggles at
  `q + 1` alone.

Performing both preserves value AND coin count while toggling the parity at
`j` and at `q + 1`, which may be arbitrarily far apart.  So for a prescribed
toggle pair `(j, l)` the requirement is a coin at `j` and two coins at
`l - 1`, with no adjacency condition at all.
-/

namespace MinModulus

open Finset

section Shift

variable {m j q : ℕ} {k : ℕ → ℕ}

/-- Take one coin at `j` and put two at `j - 1`. -/
def splitAt (k : ℕ → ℕ) (j : ℕ) : ℕ → ℕ :=
  Function.update (Function.update k j (k j - 1)) (j - 1) (k (j - 1) + 2)

/-- Take two coins at `q` and put one at `q + 1`. -/
def mergeAt (k : ℕ → ℕ) (q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update k q (k q - 2)) (q + 1) (k (q + 1) + 1)

/-! ### Pointwise description -/

lemma splitAt_apply_of_ne (k : ℕ → ℕ) (j i : ℕ) (h1 : i ≠ j - 1) (h2 : i ≠ j) :
    splitAt k j i = k i := by
  unfold splitAt
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

lemma splitAt_at_pred (k : ℕ → ℕ) (j : ℕ) :
    splitAt k j (j - 1) = k (j - 1) + 2 := by
  unfold splitAt; rw [Function.update_self]

lemma splitAt_at (k : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    splitAt k j j = k j - 1 := by
  unfold splitAt
  rw [Function.update_of_ne (by omega), Function.update_self]

lemma mergeAt_apply_of_ne (k : ℕ → ℕ) (q i : ℕ) (h1 : i ≠ q + 1) (h2 : i ≠ q) :
    mergeAt k q i = k i := by
  unfold mergeAt
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

lemma mergeAt_at (k : ℕ → ℕ) (q : ℕ) : mergeAt k q q = k q - 2 := by
  unfold mergeAt
  rw [Function.update_of_ne (by omega), Function.update_self]

lemma mergeAt_at_succ (k : ℕ → ℕ) (q : ℕ) :
    mergeAt k q (q + 1) = k (q + 1) + 1 := by
  unfold mergeAt; rw [Function.update_self]

/-! ### Value and coin count -/

theorem splitAt_val (hj : 1 ≤ j) (hjm : j < m) (h : 1 ≤ k j) :
    val m (splitAt k j) = val m k := by
  have hp : (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by
    have hps := pow_succ 2 (j - 1)
    rw [show j - 1 + 1 = j from by omega] at hps
    omega
  have h1 := val_update m j (k j - 1) k hjm
  set k1 := Function.update k j (k j - 1) with hk1
  have hk1p : k1 (j - 1) = k (j - 1) := by
    rw [hk1, Function.update_of_ne (by omega)]
  have h2 := val_update m (j - 1) (k (j - 1) + 2) k1 (by omega)
  rw [hk1p] at h2
  have heq : splitAt k j = Function.update k1 (j - 1) (k (j - 1) + 2) := rfl
  rw [heq]
  have hmul : (k j - 1) * 2 ^ j + 2 ^ j = k j * 2 ^ j := by
    obtain ⟨t, ht⟩ : ∃ t, k j = t + 1 := ⟨k j - 1, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel]
    ring
  have hexp : (k (j - 1) + 2) * 2 ^ (j - 1)
      = k (j - 1) * 2 ^ (j - 1) + 2 * 2 ^ (j - 1) := by ring
  omega

theorem splitAt_dsum (hj : 1 ≤ j) (hjm : j < m) (h : 1 ≤ k j) :
    dsum m (splitAt k j) = dsum m k + 1 := by
  have h1 := dsum_update m j (k j - 1) k hjm
  set k1 := Function.update k j (k j - 1) with hk1
  have hk1p : k1 (j - 1) = k (j - 1) := by
    rw [hk1, Function.update_of_ne (by omega)]
  have h2 := dsum_update m (j - 1) (k (j - 1) + 2) k1 (by omega)
  rw [hk1p] at h2
  have heq : splitAt k j = Function.update k1 (j - 1) (k (j - 1) + 2) := rfl
  rw [heq]
  omega

theorem mergeAt_val (hqm : q + 1 < m) (h : 2 ≤ k q) :
    val m (mergeAt k q) = val m k := by
  have hp : (2 : ℕ) ^ (q + 1) = 2 * 2 ^ q := by rw [pow_succ]; ring
  have h1 := val_update m q (k q - 2) k (by omega)
  set k1 := Function.update k q (k q - 2) with hk1
  have hk1s : k1 (q + 1) = k (q + 1) := by
    rw [hk1, Function.update_of_ne (by omega)]
  have h2 := val_update m (q + 1) (k (q + 1) + 1) k1 hqm
  rw [hk1s] at h2
  have heq : mergeAt k q = Function.update k1 (q + 1) (k (q + 1) + 1) := rfl
  rw [heq]
  have hmul : (k q - 2) * 2 ^ q + 2 * 2 ^ q = k q * 2 ^ q := by
    obtain ⟨t, ht⟩ : ∃ t, k q = t + 2 := ⟨k q - 2, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel]
    ring
  have hexp : (k (q + 1) + 1) * 2 ^ (q + 1)
      = k (q + 1) * 2 ^ (q + 1) + 2 ^ (q + 1) := by ring
  omega

theorem mergeAt_dsum (hqm : q + 1 < m) (h : 2 ≤ k q) :
    dsum m (mergeAt k q) + 1 = dsum m k := by
  have h1 := dsum_update m q (k q - 2) k (by omega)
  set k1 := Function.update k q (k q - 2) with hk1
  have hk1s : k1 (q + 1) = k (q + 1) := by
    rw [hk1, Function.update_of_ne (by omega)]
  have h2 := dsum_update m (q + 1) (k (q + 1) + 1) k1 hqm
  rw [hk1s] at h2
  have heq : mergeAt k q = Function.update k1 (q + 1) (k (q + 1) + 1) := rfl
  rw [heq]
  omega

/-! ### A general two-point parity toggle for the sheet sum -/

private lemma sum_split_two_gen (f : ℕ → ℕ) {u v : ℕ} (hu : u < m) (hv : v < m)
    (huv : u ≠ v) :
    ∑ i ∈ range m, f i
      = f u + (f v + ∑ i ∈ ((range m).erase u).erase v, f i) := by
  have hmu : u ∈ range m := Finset.mem_range.mpr hu
  have hmv : v ∈ (range m).erase u :=
    Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_range.mpr hv⟩
  rw [← Finset.add_sum_erase (range m) f hmu,
    ← Finset.add_sum_erase ((range m).erase u) f hmv]

/-- **Two toggles, anywhere.**  If two coin families have the same
multiplicity parity off `{u, v}` and opposite parity at both `u` and `v`,
their sheet sums differ by `b u + b v` modulo two.  No adjacency or
ordering of `u` and `v` is assumed. -/
theorem sheetSum_toggle_two (b k k' : ℕ → ℕ) {u v : ℕ}
    (hu : u < m) (hv : v < m) (huv : u ≠ v)
    (hoff : ∀ i, i ≠ u → i ≠ v → k' i % 2 = k i % 2)
    (htu : k' u % 2 ≠ k u % 2) (htv : k' v % 2 ≠ k v % 2) :
    (sheetSum m b k' + sheetSum m b k) % 2 = (b u + b v) % 2 := by
  classical
  unfold sheetSum
  rw [sum_split_two_gen (fun i => if k' i % 2 = 0 then b i else 0) hu hv huv,
    sum_split_two_gen (fun i => if k i % 2 = 0 then b i else 0) hu hv huv]
  have hrest : ∑ i ∈ ((range m).erase u).erase v,
        (if k' i % 2 = 0 then b i else 0)
      = ∑ i ∈ ((range m).erase u).erase v,
        (if k i % 2 = 0 then b i else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiv : i ≠ v := Finset.ne_of_mem_erase hi
    have hiu : i ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    rw [hoff i hiu hiv]
  rw [hrest]
  have hA : (if k' u % 2 = 0 then b u else 0)
      + (if k u % 2 = 0 then b u else 0) = b u := by
    by_cases h : k u % 2 = 0
    · rw [if_neg (by omega), if_pos h]; omega
    · rw [if_pos (by omega), if_neg h]; omega
  have hB : (if k' v % 2 = 0 then b v else 0)
      + (if k v % 2 = 0 then b v else 0) = b v := by
    by_cases h : k v % 2 = 0
    · rw [if_neg (by omega), if_pos h]; omega
    · rw [if_pos (by omega), if_neg h]; omega
  omega

/-! ### A mergeable position always exists -/

/-- With more coins than exponents some exponent carries at least two coins,
so the merge half of the move can always be started.  In the SI-lift setting
there are `n` coins on the `n - 1` exponents `0 .. n - 2`, so this applies to
every rival. -/
lemma exists_two_of_dsum_gt (k : ℕ → ℕ) (hd : m < dsum m k) :
    ∃ q, q < m ∧ 2 ≤ k q := by
  by_contra hc
  push_neg at hc
  have hle : dsum m k ≤ m := by
    unfold dsum
    calc ∑ i ∈ range m, k i ≤ ∑ i ∈ range m, 1 :=
          Finset.sum_le_sum fun i hi => by
            have := hc i (Finset.mem_range.mp hi); omega
      _ = m := by simp
  omega

/-! ### The combined move -/

/-- Split one coin down at `j` and merge two coins up at `q`.  Value and
coin count are both preserved; the parity toggles exactly at `j` and
`q + 1`. -/
def shiftMove (k : ℕ → ℕ) (j q : ℕ) : ℕ → ℕ := mergeAt (splitAt k j) q

lemma shiftMove_at (hj : 1 ≤ j) (hd : q + 1 < j - 1 ∨ j < q) :
    shiftMove k j q j = k j - 1 := by
  unfold shiftMove
  rw [mergeAt_apply_of_ne _ _ _ (by omega) (by omega), splitAt_at k j hj]

lemma shiftMove_at_mergeSucc (hj : 1 ≤ j) (hd : q + 1 < j - 1 ∨ j < q) :
    shiftMove k j q (q + 1) = k (q + 1) + 1 := by
  unfold shiftMove
  rw [mergeAt_at_succ, splitAt_apply_of_ne k j (q + 1) (by omega) (by omega)]

lemma shiftMove_parity_off (hj : 1 ≤ j) (hd : q + 1 < j - 1 ∨ j < q)
    (h2 : 2 ≤ k q) {i : ℕ} (hij : i ≠ j) (hiq : i ≠ q + 1) :
    shiftMove k j q i % 2 = k i % 2 := by
  unfold shiftMove
  by_cases hq : i = q
  · subst hq
    rw [mergeAt_at, splitAt_apply_of_ne k j i (by omega) (by omega)]
    omega
  · rw [mergeAt_apply_of_ne _ _ _ hiq hq]
    by_cases hp : i = j - 1
    · subst hp
      rw [splitAt_at_pred]
      omega
    · rw [splitAt_apply_of_ne k j i hp hij]

theorem shiftMove_val (hj : 1 ≤ j) (hjm : j < m) (hqm : q + 1 < m)
    (hd : q + 1 < j - 1 ∨ j < q) (h1 : 1 ≤ k j) (h2 : 2 ≤ k q) :
    val m (shiftMove k j q) = val m k := by
  have hq : splitAt k j q = k q :=
    splitAt_apply_of_ne k j q (by omega) (by omega)
  unfold shiftMove
  rw [mergeAt_val hqm (by rw [hq]; exact h2), splitAt_val hj hjm h1]

theorem shiftMove_dsum (hj : 1 ≤ j) (hjm : j < m) (hqm : q + 1 < m)
    (hd : q + 1 < j - 1 ∨ j < q) (h1 : 1 ≤ k j) (h2 : 2 ≤ k q) :
    dsum m (shiftMove k j q) = dsum m k := by
  have hq : splitAt k j q = k q :=
    splitAt_apply_of_ne k j q (by omega) (by omega)
  have hm := mergeAt_dsum (k := splitAt k j) hqm (by rw [hq]; exact h2)
  have hs := splitAt_dsum hj hjm h1
  unfold shiftMove
  omega

theorem shiftMove_sheetSum (b : ℕ → ℕ) (hj : 1 ≤ j) (hjm : j < m)
    (hqm : q + 1 < m) (hd : q + 1 < j - 1 ∨ j < q)
    (h1 : 1 ≤ k j) (h2 : 2 ≤ k q) :
    (sheetSum m b (shiftMove k j q) + sheetSum m b k) % 2
      = (b j + b (q + 1)) % 2 := by
  refine sheetSum_toggle_two b k (shiftMove k j q) hjm hqm (by omega)
    (fun i hij hiq => shiftMove_parity_off hj hd h2 hij hiq) ?_ ?_
  · rw [shiftMove_at hj hd]; omega
  · rw [shiftMove_at_mergeSucc hj hd]; omega

/-- **The move as a rival transformer, with no adjacency condition.**
Given a coin family realizing a target with a prescribed coin count, a coin
at `j` and two coins at `q`, it returns a family realizing the SAME target
with the SAME count and the OPPOSITE sheet parity, whenever the sheet bits
differ at `j` and `q + 1`.

Together with `flipMove_rival`, which covers the adjacent pairs, every
prescribed toggle pair is reachable: for a pair at distance at least two
take `j` and `q = v - 1` here, and for an adjacent pair use the
three-point move. -/
theorem shiftMove_rival (b : ℕ → ℕ) (hj : 1 ≤ j) (hjm : j < m)
    (hqm : q + 1 < m) (hd : q + 1 < j - 1 ∨ j < q)
    (h1 : 1 ≤ k j) (h2 : 2 ≤ k q)
    (hne : b j % 2 ≠ b (q + 1) % 2) :
    dsum m (shiftMove k j q) = dsum m k
      ∧ val m (shiftMove k j q) = val m k
      ∧ sheetSum m b (shiftMove k j q) % 2 ≠ sheetSum m b k % 2 := by
  refine ⟨shiftMove_dsum hj hjm hqm hd h1 h2,
    shiftMove_val hj hjm hqm hd h1 h2, ?_⟩
  have h := shiftMove_sheetSum b hj hjm hqm hd h1 h2
  omega

end Shift

end MinModulus
