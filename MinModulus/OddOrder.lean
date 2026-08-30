/-
# The odd-order lower bound: the base case of the two-adic descent

The descent (`Descent.lean`) halves even moduli; its base case is groups of
odd order, where no involution exists.  This file proves the first set-free
lower bound specific to that case.

**Theorem** (`card_ge_of_odd`).  If doubling is injective on `G`
(equivalently: `G` finite of odd order) and `g : Fin (m+1) → G` is a valid
tuple with `m ≥ 3`, then `|G| ≥ 2^m + 2m`.  Without the hypothesis on `m`,
`|G| ≥ 2^m + m` (`card_ge_of_odd'`).

The proof exhibits `2^m + 2m` elements that validity forces to be pairwise
distinct: the `2^m` subset sums `σ_T` of the differences `hⱼ = g_{j+1} - g₀`,
the `m` doubles `2hᵢ`, and the `m` reflected doubles `σ_[m] - 2hᵢ`.  Every
coincidence yields a witness at `0` with coefficients in `{-1,…,3}`; the
boundary cases use injectivity of `x ↦ x + x`.  In even order the theorem
fails — in the extremal `(ZMod 2)^m` of order `2^m` the doubles collapse to
`0` — so the hypothesis is exactly the odd/even divide of the descent.

**Corollary** (`valid_odd_zmod_bound`, `odd_min_three`, `odd_min_four`).
In `ZMod N` with `N` odd: `N ≥ 2^m + 2m`; combined with parity this pins the
least odd valid modulus to exactly `2^n - 1` for `n = 3` and `n = 4` (the
super-increasing set attains it) — the odd stratum of the stratified
conjecture is a theorem for `n ≤ 4`.
-/
import MinModulus.Descent

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-! ### Witnesses on the differences -/

/-- A nonzero integer vector `d ≥ -1` on the differences with `∑ d ≤ 1` and
`∑ dⱼ • (g_{j+1} - g₀) = 0` contradicts validity: pad with `-∑ d` at `0`. -/
private lemma no_diff_relation (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {d : Fin m → ℤ} (hne : d ≠ 0) (hge : ∀ j, -1 ≤ d j) (hsum : (∑ j, d j) ≤ 1)
    (hval : (∑ j, d j • diff g j) = 0) : False := by
  refine (validTuple_iff_no_zero_witness g).mp hg (Fin.cons (-(∑ j, d j)) d)
    ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    funext j
    have h1 := congrFun h0 j.succ
    rwa [Fin.cons_succ, Pi.zero_apply] at h1
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]; omega
    · rw [Fin.cons_succ]; exact hge j
  · rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    omega
  · rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    have h2 : (∑ j, d j • diff g j) = (∑ j, d j • g j.succ) - (∑ j, d j) • g 0 := by
      unfold diff
      rw [Finset.sum_congr rfl fun j _ => smul_sub (d j) (g j.succ) (g 0),
        Finset.sum_sub_distrib, Finset.sum_smul]
    rw [h2] at hval
    have h3 : (∑ j, d j • g j.succ) = (∑ j, d j) • g 0 := sub_eq_zero.mp hval
    rw [h3, neg_smul, neg_add_cancel]

/-- `∑ⱼ (if j = i then a else 0) • xⱼ = a • xᵢ`. -/
private lemma sum_single_smul (x : Fin m → G) (i : Fin m) (a : ℤ) :
    (∑ j, (if j = i then a else 0) • x j) = a • x i := by
  have h : ∀ j, (if j = i then a else 0) • x j = if j = i then a • x j else 0 := by
    intro j; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq' univ i fun j => a • x j]
  simp

/-- `∑ⱼ (if j ∈ T then 1 else 0) • xⱼ = ∑_{j ∈ T} xⱼ`. -/
private lemma sum_indicator_smul (x : Fin m → G) (T : Finset (Fin m)) :
    (∑ j, (if j ∈ T then (1 : ℤ) else 0) • x j) = ∑ j ∈ T, x j := by
  have h : ∀ j, (if j ∈ T then (1 : ℤ) else 0) • x j = if j ∈ T then x j else 0 := by
    intro j; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_mem, Finset.univ_inter]

/-! ### The six coincidence families -/

section Coincidences

variable (g : Fin (m + 1) → G) (hg : ValidTuple g)
  (hinj : ∀ x y : G, x + x = y + y → x = y)

include hinj in
private lemma eq_zero_of_two_zsmul {x : G} (hx : (2 : ℤ) • x = 0) : x = 0 := by
  refine hinj x 0 ?_
  rw [← two_zsmul, hx]
  simp

include hg in
private lemma diff_ne_zero (i : Fin m) : diff g i ≠ 0 := by
  intro h0
  have h1 : ssum g {i} = ssum g ∅ := by
    rw [ssum, ssum, Finset.sum_singleton, Finset.sum_empty, h0]
  exact absurd (ssum_injective g hg h1) (Finset.singleton_ne_empty i)

include hg hinj in
private lemma two_smul_diff_injective {i j : Fin m}
    (h : (2 : ℤ) • diff g i = (2 : ℤ) • diff g j) : i = j := by
  have h1 : diff g i = diff g j := by
    apply hinj
    have h2 := h
    rw [two_zsmul, two_zsmul] at h2
    exact h2
  have h3 : ssum g {i} = ssum g {j} := by
    rw [ssum, ssum, Finset.sum_singleton, Finset.sum_singleton, h1]
  exact Finset.singleton_injective (ssum_injective g hg h3)

include hg hinj in
/-- A double never equals a subset sum. -/
private lemma ssum_ne_two_smul (T : Finset (Fin m)) (i : Fin m) :
    ssum g T ≠ (2 : ℤ) • diff g i := by
  intro h
  rcases T.eq_empty_or_nonempty with rfl | hT
  · rw [ssum, Finset.sum_empty] at h
    exact diff_ne_zero g hg i (eq_zero_of_two_zsmul hinj h.symm)
  · refine no_diff_relation g hg
      (d := fun j => (if j = i then 2 else 0) - (if j ∈ T then 1 else 0))
      ?_ ?_ ?_ ?_
    · intro h0
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply] at h1
      by_cases h2 : i ∈ T <;> simp [h2] at h1
    · intro j
      show (-1 : ℤ) ≤ (if j = i then 2 else 0) - (if j ∈ T then 1 else 0)
      split_ifs <;> omega
    · have h1 : (∑ j, ((if j = i then (2 : ℤ) else 0) - if j ∈ T then 1 else 0))
          = 2 - (T.card : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' univ i fun _ => (2 : ℤ)]
        simp
      rw [h1]
      have h2 : 1 ≤ T.card := Finset.card_pos.mpr hT
      have h3 : (1 : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast h2
      omega
    · have h1 : ∀ j, ((if j = i then (2 : ℤ) else 0) - if j ∈ T then 1 else 0) • diff g j
          = (if j = i then (2 : ℤ) else 0) • diff g j
            - (if j ∈ T then (1 : ℤ) else 0) • diff g j := fun j => sub_smul _ _ _
      rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_sub_distrib,
        sum_single_smul, sum_indicator_smul]
      rw [← ssum, ← h, sub_self]

include hg hinj in
/-- A reflected double never equals a subset sum. -/
private lemma ssum_ne_reflected (T : Finset (Fin m)) (i : Fin m) :
    ssum g T ≠ ssum g univ - (2 : ℤ) • diff g i := by
  intro h
  by_cases hT : T = univ
  · subst hT
    have h1 : (2 : ℤ) • diff g i = 0 := sub_eq_self.mp h.symm
    exact diff_ne_zero g hg i (eq_zero_of_two_zsmul hinj h1)
  · refine no_diff_relation g hg
      (d := fun j => (if j ∈ T then 1 else 0) + (if j = i then 2 else 0) - 1)
      ?_ ?_ ?_ ?_
    · intro h0
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply] at h1
      by_cases h2 : i ∈ T <;> simp [h2] at h1
    · intro j
      show (-1 : ℤ) ≤ (if j ∈ T then 1 else 0) + (if j = i then 2 else 0) - 1
      split_ifs <;> omega
    · have h1 : (∑ j, ((if j ∈ T then (1 : ℤ) else 0) + (if j = i then 2 else 0) - 1))
          = (T.card : ℤ) + 2 - m := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' univ i fun _ => (2 : ℤ)]
        simp
      rw [h1]
      have h2 : T.card < m := by
        have h3 := Finset.card_lt_card ((Finset.subset_univ T).ssubset_of_ne hT)
        rwa [Finset.card_univ, Fintype.card_fin] at h3
      have h4 : (T.card : ℤ) < m := by exact_mod_cast h2
      omega
    · have h1 : ∀ j, ((if j ∈ T then (1 : ℤ) else 0) + (if j = i then 2 else 0) - 1) • diff g j
          = ((if j ∈ T then (1 : ℤ) else 0) • diff g j
              + (if j = i then (2 : ℤ) else 0) • diff g j) - (1 : ℤ) • diff g j := by
        intro j
        rw [sub_smul, add_smul]
      rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, sum_single_smul, sum_indicator_smul]
      have h2 : (∑ j, (1 : ℤ) • diff g j) = ssum g univ := by
        rw [ssum]
        exact Finset.sum_congr rfl fun j _ => one_smul ℤ (diff g j)
      rw [h2, ← ssum]
      rw [eq_sub_iff_add_eq] at h
      rw [h, sub_self]

include hg in
/-- A double never equals a reflected double (needs `m ≥ 3`). -/
private lemma two_smul_ne_reflected (hm : 3 ≤ m) (i j : Fin m) :
    (2 : ℤ) • diff g i ≠ ssum g univ - (2 : ℤ) • diff g j := by
  intro h
  refine no_diff_relation g hg
    (d := fun k => (if k = i then 2 else 0) + (if k = j then 2 else 0) - 1)
    ?_ ?_ ?_ ?_
  · intro h0
    have h1 := congrFun h0 i
    simp only [Pi.zero_apply] at h1
    by_cases h2 : i = j <;> simp [h2] at h1
  · intro k
    show (-1 : ℤ) ≤ (if k = i then 2 else 0) + (if k = j then 2 else 0) - 1
    split_ifs <;> omega
  · have h1 : (∑ k, ((if k = i then (2 : ℤ) else 0) + (if k = j then 2 else 0) - 1))
        = 2 + 2 - m := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' univ i fun _ => (2 : ℤ),
        Finset.sum_ite_eq' univ j fun _ => (2 : ℤ)]
      simp
    rw [h1]
    have h2 : (3 : ℤ) ≤ m := by exact_mod_cast hm
    omega
  · have h1 : ∀ k, ((if k = i then (2 : ℤ) else 0) + (if k = j then 2 else 0) - 1) • diff g k
        = ((if k = i then (2 : ℤ) else 0) • diff g k
            + (if k = j then (2 : ℤ) else 0) • diff g k) - (1 : ℤ) • diff g k := by
      intro k
      rw [sub_smul, add_smul]
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, sum_single_smul, sum_single_smul]
    have h2 : (∑ k, (1 : ℤ) • diff g k) = ssum g univ := by
      rw [ssum]
      exact Finset.sum_congr rfl fun k _ => one_smul ℤ (diff g k)
    rw [h2]
    rw [eq_sub_iff_add_eq] at h
    rw [h, sub_self]

end Coincidences

/-! ### The lower bounds -/

/-- **Odd-order lower bound.**  If doubling is injective on `G` and `g` is a
valid `(m+1)`-tuple with `m ≥ 3`, then `|G| ≥ 2^m + 2m`: the subset sums, the
doubles `2hᵢ`, and the reflected doubles `σ_[m] - 2hᵢ` are pairwise distinct. -/
theorem card_ge_of_odd [Fintype G] (hm : 3 ≤ m) (g : Fin (m + 1) → G)
    (hg : ValidTuple g) (hinj : ∀ x y : G, x + x = y + y → x = y) :
    2 ^ m + 2 * m ≤ Fintype.card G := by
  classical
  set φ : Finset (Fin m) ⊕ (Fin m ⊕ Fin m) → G :=
    Sum.elim (ssum g) (Sum.elim (fun i => (2 : ℤ) • diff g i)
      (fun i => ssum g univ - (2 : ℤ) • diff g i)) with hφ
  have hφinj : Function.Injective φ := by
    intro x y h
    simp only [hφ] at h
    rcases x with T | i | i <;> rcases y with T' | j | j <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (ssum_injective g hg h)
    · exact absurd h (ssum_ne_two_smul g hg hinj T j)
    · exact absurd h (ssum_ne_reflected g hg hinj T j)
    · exact absurd h.symm (ssum_ne_two_smul g hg hinj T' i)
    · exact congrArg (Sum.inr ∘ Sum.inl) (two_smul_diff_injective g hg hinj h)
    · exact absurd h (two_smul_ne_reflected g hg hm i j)
    · exact absurd h.symm (ssum_ne_reflected g hg hinj T' i)
    · exact absurd h.symm (two_smul_ne_reflected g hg hm j i)
    · have h1 : (2 : ℤ) • diff g i = (2 : ℤ) • diff g j := sub_right_injective h
      exact congrArg (Sum.inr ∘ Sum.inr) (two_smul_diff_injective g hg hinj h1)
  have h1 := Fintype.card_le_of_injective φ hφinj
  simp only [Fintype.card_sum, Fintype.card_finset, Fintype.card_fin] at h1
  omega

/-- Without any hypothesis on `m`: `|G| ≥ 2^m + m`. -/
theorem card_ge_of_odd' [Fintype G] (g : Fin (m + 1) → G)
    (hg : ValidTuple g) (hinj : ∀ x y : G, x + x = y + y → x = y) :
    2 ^ m + m ≤ Fintype.card G := by
  classical
  set φ : Finset (Fin m) ⊕ Fin m → G :=
    Sum.elim (ssum g) (fun i => (2 : ℤ) • diff g i) with hφ
  have hφinj : Function.Injective φ := by
    intro x y h
    simp only [hφ] at h
    rcases x with T | i <;> rcases y with T' | j <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (ssum_injective g hg h)
    · exact absurd h (ssum_ne_two_smul g hg hinj T j)
    · exact absurd h.symm (ssum_ne_two_smul g hg hinj T' i)
    · exact congrArg Sum.inr (two_smul_diff_injective g hg hinj h)
  have h1 := Fintype.card_le_of_injective φ hφinj
  simp only [Fintype.card_sum, Fintype.card_finset, Fintype.card_fin] at h1
  omega

/-! ### The cyclic corollaries -/

/-- Doubling is injective mod odd `N`. -/
private lemma add_self_injective_zmod {N : ℕ} (hN : Odd N) [NeZero N] :
    ∀ x y : ZMod N, x + x = y + y → x = y := by
  intro x y hxy
  have h2 : IsUnit (2 : ZMod N) := by
    have h1 : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_num
    rw [← h1, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr hN
  have h3 : (2 : ZMod N) * x = (2 : ZMod N) * y := by
    rw [two_mul, two_mul]
    exact hxy
  exact h2.mul_left_cancel h3

/-- **Odd moduli.**  A valid `(m+1)`-tuple mod odd `N` with `m ≥ 3` forces
`N ≥ 2^m + 2m`. -/
theorem valid_odd_zmod_bound {N : ℕ} (hN : Odd N) (hm : 3 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g) : 2 ^ m + 2 * m ≤ N := by
  haveI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  have h1 := card_ge_of_odd hm g hg (add_self_injective_zmod hN)
  rwa [ZMod.card] at h1

/-- **The odd stratum for `n = 3`:** the least odd valid modulus is `2^3 - 1`. -/
theorem odd_min_three {N : ℕ} (hN : Odd N) (g : Fin 3 → ZMod N)
    (hg : ValidTuple g) : 7 ≤ N := by
  haveI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  have h1 := card_ge_of_odd' g hg (add_self_injective_zmod hN)
  rw [ZMod.card] at h1
  rcases hN with ⟨k, rfl⟩
  omega

/-- **The odd stratum for `n = 4` (G2, first open case):** the least odd valid
modulus is `2^4 - 1 = 15`, attained by the super-increasing set.  The bound
`N ≥ 2^3 + 6 = 14` plus parity give `N ≥ 15`. -/
theorem odd_min_four {N : ℕ} (hN : Odd N) (g : Fin 4 → ZMod N)
    (hg : ValidTuple g) : 15 ≤ N := by
  have h1 := valid_odd_zmod_bound hN (le_refl 3) g hg
  rcases hN with ⟨k, rfl⟩
  omega

end MinModulus
