import MinModulus.GlobalRoadmap

/-!
# Sheet bits for half-quotient lifts

Generic layer for rival computations on tuples `g` whose coordinates are
known modulo half the (doubly even) modulus: writing
`g i = (r i : ZMod N) + β i` with `β i ∈ {0, H}` and `2 • H = 0`, any
integer coefficient vector `c` satisfies

    ∑ c i • g i = ((∑ c i * r i : ℤ) : ZMod N) + ∑_{c i odd} β i.

Even coefficients kill the bits, odd coefficients pass them through.
-/

namespace MinModulus

open Finset

/-- An even integer multiple of a 2-torsion element vanishes. -/
lemma zsmul_eq_zero_of_even_of_two_nsmul_eq_zero {G : Type*} [AddCommGroup G]
    {x : G} (hx : 2 • x = 0) {c : ℤ} (hc : Even c) : c • x = 0 := by
  obtain ⟨t, ht⟩ := hc
  have h2 : (2 : ℤ) • x = 0 := by
    rw [two_zsmul, ← two_nsmul, hx]
  calc c • x = (t * 2) • x := by rw [ht]; ring_nf
    _ = t • ((2 : ℤ) • x) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

/-- An odd integer multiple of a 2-torsion element is the element itself. -/
lemma zsmul_eq_self_of_odd_of_two_nsmul_eq_zero {G : Type*} [AddCommGroup G]
    {x : G} (hx : 2 • x = 0) {c : ℤ} (hc : Odd c) : c • x = x := by
  obtain ⟨t, ht⟩ := hc
  have heven : (2 * t : ℤ) • x = 0 :=
    zsmul_eq_zero_of_even_of_two_nsmul_eq_zero hx ⟨t, by ring⟩
  rw [ht, add_smul, heven, zero_add, one_smul]

/-- Bit decomposition of a weighted sum: even coefficients kill the
2-torsion bits, odd coefficients pass them through. -/
lemma zsmul_sum_bit_decomposition {n : ℕ} {G : Type*} [AddCommGroup G]
    (c : Fin n → ℤ) (v β : Fin n → G)
    (hβ : ∀ i, 2 • β i = 0) :
    ∑ i, c i • (v i + β i)
      = ∑ i, c i • v i + ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i := by
  have hsplit : ∀ i, c i • (v i + β i) = c i • v i + c i • β i := by
    intro i; rw [smul_add]
  calc ∑ i, c i • (v i + β i) = ∑ i, (c i • v i + c i • β i) := by
        exact Finset.sum_congr rfl fun i _ => hsplit i
    _ = ∑ i, c i • v i + ∑ i, c i • β i := Finset.sum_add_distrib
    _ = ∑ i, c i • v i + ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i := by
        congr 1
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Odd (c i))]
        have hz : ∑ i ∈ Finset.univ.filter (fun i => ¬ Odd (c i)), c i • β i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have : Even (c i) := Int.not_odd_iff_even.mp (Finset.mem_filter.mp hi).2
          exact zsmul_eq_zero_of_even_of_two_nsmul_eq_zero (hβ i) this
        rw [hz, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        exact zsmul_eq_self_of_odd_of_two_nsmul_eq_zero (hβ i)
          (Finset.mem_filter.mp hi).2

/-- A valid tuple admits no nonstandard multiplicity rival, in integer
coefficient form: if `∑ κ = n` and some `κ j ≠ 1`, the shifted
coefficients `κ - 1` cannot have zero weighted sum. -/
lemma validTuple_no_shifted_rival {n : ℕ} {G : Type*} [AddCommGroup G]
    {g : Fin n → G} (hg : ValidTuple g) (κ : Fin n → ℕ)
    (hsum : ∑ i, κ i = n) {j : Fin n} (hj : κ j ≠ 1) :
    ∑ i, ((κ i : ℤ) - 1) • g i ≠ 0 := by
  intro hzero
  apply hj
  have hval : ∑ i, κ i • g i = ∑ i, g i := by
    have hsplit : ∀ i : Fin n, ((κ i : ℤ) - 1) • g i = κ i • g i - g i := by
      intro i
      rw [sub_smul, one_smul, natCast_zsmul]
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
        sub_eq_zero] at hzero
    exact hzero
  exact hg κ hsum hval j

/-- Weighted-sum decomposition over a sheeted tuple: integer part plus
the odd-coefficient bits. -/
lemma shifted_sum_eq {n N : ℕ} (c : Fin n → ℤ) (r : Fin n → ℕ)
    (β : Fin n → ZMod N) (g : Fin n → ZMod N)
    (hβ : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i) :
    ∑ i, c i • g i
      = (((∑ i, c i * (r i : ℤ)) : ℤ) : ZMod N)
        + ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i := by
  have hcongr : ∀ i : Fin n, c i • g i = c i • (((r i : ℕ) : ZMod N) + β i) := by
    intro i; rw [hg i]
  rw [Finset.sum_congr rfl fun i _ => hcongr i,
      zsmul_sum_bit_decomposition c (fun i => ((r i : ℕ) : ZMod N)) β hβ]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [zsmul_eq_mul]

/-- Even natural multiples of a 2-torsion element vanish. -/
lemma nsmul_eq_zero_of_even_of_two_nsmul_eq_zero {G : Type*} [AddCommGroup G]
    {x : G} (hx : 2 • x = 0) {k : ℕ} (hk : Even k) : k • x = 0 := by
  obtain ⟨t, ht⟩ := hk
  calc k • x = (2 * t) • x := by rw [ht]; ring_nf
    _ = t • (2 • x) := by rw [mul_comm, mul_smul]
    _ = 0 := by rw [hx, smul_zero]

/-- Odd natural multiples of a 2-torsion element give the element. -/
lemma nsmul_eq_self_of_odd_of_two_nsmul_eq_zero {G : Type*} [AddCommGroup G]
    {x : G} (hx : 2 • x = 0) {k : ℕ} (hk : Odd k) : k • x = x := by
  obtain ⟨t, ht⟩ := hk
  have : (2 * t) • x = 0 := nsmul_eq_zero_of_even_of_two_nsmul_eq_zero hx ⟨t, by ring⟩
  rw [ht, add_smul, this, zero_add, one_smul]

/-- Sum of a function supported on at most two points. -/
lemma sum_eq_of_two {n : ℕ} {A : Type*} [AddCommMonoid A] (f : Fin n → A)
    (p q : Fin n) (hpq : p ≠ q)
    (h : ∀ i, i ≠ p → i ≠ q → f i = 0) :
    ∑ i, f i = f p + f q := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset (Fin n)))]
  · rw [Finset.sum_insert (by simp [hpq]), Finset.sum_singleton]
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h i hi.1 hi.2

/-- Sum of a function supported on at most three points. -/
lemma sum_eq_of_three {n : ℕ} {A : Type*} [AddCommMonoid A] (f : Fin n → A)
    (p q s : Fin n) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (h : ∀ i, i ≠ p → i ≠ q → i ≠ s → f i = 0) :
    ∑ i, f i = f p + f q + f s := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q, s} : Finset (Fin n)))]
  · rw [Finset.sum_insert (by simp [hpq, hps]), Finset.sum_insert (by simp [hqs]),
        Finset.sum_singleton, add_assoc]
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h i hi.1 hi.2.1 hi.2.2

/-- In a group where `2 • H = 0` and `H ≠ 0`, two elements of `{0, H}`
whose sum is nonzero sum exactly to `H`. -/
lemma pair_sum_eq_of_ne_zero {G : Type*} [AddCommGroup G] {H x y : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H) (hH : 2 • H = 0)
    (hne : x + y ≠ 0) : x + y = H := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp at hne
  · simp
  · simp
  · exfalso; apply hne; rw [← two_nsmul, hH]

/-- Splitting a sum at three distinguished points. -/
lemma sum_split_three {n : ℕ} {A : Type*} [AddCommMonoid A] (f : Fin n → A)
    (p q s : Fin n) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    ∑ i, f i = f p + f q + f s + ∑ i ∈ Finset.univ \ {p, q, s}, f i := by
  classical
  have hsub : ({p, q, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub, Finset.sum_insert (by simp [hpq, hps]),
      Finset.sum_insert (by simp [hqs]), Finset.sum_singleton]
  abel

/-- Complement of `pair_sum_eq_of_ne_zero`: a `{0, H}` pair summing to
anything other than `H` sums to zero. -/
lemma pair_sum_eq_zero_of_ne {G : Type*} [AddCommGroup G] {H x y : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H) (hH : 2 • H = 0)
    (hne : x + y ≠ H) : x + y = 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp
  · exfalso; apply hne; simp
  · exfalso; apply hne; simp
  · rw [← two_nsmul]; exact hH

/-- Rearranging a two-torsion pair equation. -/
lemma eq_add_of_pair_sum {G : Type*} [AddCommGroup G] {x y z : G}
    (hy : 2 • y = 0) (h : x + y = z) : x = z + y := by
  rw [← h, add_assoc, ← two_nsmul, hy, add_zero]

/-- A two-torsion pair summing to zero is equal. -/
lemma eq_of_pair_sum_zero {G : Type*} [AddCommGroup G] {x y : G}
    (hy : 2 • y = 0) (h : x + y = 0) : x = y := by
  have := eq_add_of_pair_sum hy h
  rwa [zero_add] at this

end MinModulus
