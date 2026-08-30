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

/-! ### The chain theorem: the super-increasing relation system pins the order -/

section Chain

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Chain theorem.**  If `lam 0, …, lam (m-1)` satisfy the super-increasing
chain relations `lam (i+1) = 2 • lam i + lam 0` with terminal sink
`2 • lam (m-1) + lam 0 = 0`, and their `2^m` subset sums are pairwise
distinct, then `2^(m+1) - 1 ≤ |G|`.

The base element is squeezed from both sides: the telescoped sink relation
gives `(2^(m+1) - 1) • lam 0 = 0`, so its additive order divides the odd
number `2^(m+1) - 1`; the distinct subset sums give order at least `2^m`;
and every proper divisor of an odd number `< 3 · 2^m` is `< 2^m`.  Hence the
order is exactly `2^(m+1) - 1`, which divides `|G|`. -/
theorem chain_card_bound {m : ℕ} (hm : 1 ≤ m) (lam : ℕ → G)
    (hchain : ∀ i, i + 1 < m → lam (i + 1) = 2 • lam i + lam 0)
    (hsink : 2 • lam (m - 1) + lam 0 = 0)
    (hdis : Function.Injective fun S : Finset (Fin m) => ∑ j ∈ S, lam j.val) :
    2 ^ (m + 1) - 1 ≤ Fintype.card G := by
  have hA : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  -- closed form along the chain
  have hclosed : ∀ i, i < m → lam i = (2 ^ (i + 1) - 1) • lam 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h2 : 2 * (2 ^ (i + 1) - 1) + 1 = 2 ^ (i + 1 + 1) - 1 := by
        have h3 : 1 ≤ 2 ^ (i + 1) := Nat.one_le_two_pow
        rw [pow_succ]
        omega
      rw [hchain i hi, ih (by omega), smul_smul, ← h2, add_smul, one_smul]
  -- the telescoped sink relation
  have hD : (2 ^ (m + 1) - 1) • lam 0 = 0 := by
    have h1 := hclosed (m - 1) (by omega)
    have h2 : 2 * (2 ^ (m - 1 + 1) - 1) + 1 = 2 ^ (m + 1) - 1 := by
      have h3 : m - 1 + 1 = m := by omega
      rw [h3, pow_succ]
      omega
    rw [← h2, add_smul, one_smul, mul_smul, ← h1]
    exact hsink
  set d := addOrderOf (lam 0) with hd
  have hd_pos : 0 < d := addOrderOf_pos (lam 0)
  have hd_dvd : d ∣ 2 ^ (m + 1) - 1 := addOrderOf_dvd_of_nsmul_eq_zero hD
  -- distinct subset sums force 2^m ≤ d
  have hsum : ∀ S : Finset (Fin m),
      (∑ j ∈ S, lam j.val) = (∑ j ∈ S, (2 ^ (j.val + 1) - 1)) • lam 0 := by
    intro S
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => hclosed j.val j.isLt
  have hcard : 2 ^ m ≤ d := by
    have hinj : Function.Injective fun S : Finset (Fin m) =>
        (⟨(∑ j ∈ S, (2 ^ (j.val + 1) - 1)) % d, Nat.mod_lt _ hd_pos⟩ : Fin d) := by
      intro S T h
      have h1 : (∑ j ∈ S, (2 ^ (j.val + 1) - 1)) % d
          = (∑ j ∈ T, (2 ^ (j.val + 1) - 1)) % d := congrArg Fin.val h
      apply hdis
      show (∑ j ∈ S, lam j.val) = ∑ j ∈ T, lam j.val
      rw [hsum S, hsum T]
      calc (∑ j ∈ S, (2 ^ (j.val + 1) - 1)) • lam 0
          = ((∑ j ∈ S, (2 ^ (j.val + 1) - 1)) % d) • lam 0 := by
            rw [hd]; exact (mod_addOrderOf_nsmul _ _).symm
        _ = ((∑ j ∈ T, (2 ^ (j.val + 1) - 1)) % d) • lam 0 := by rw [h1]
        _ = (∑ j ∈ T, (2 ^ (j.val + 1) - 1)) • lam 0 := by
            rw [hd]; exact mod_addOrderOf_nsmul _ _
    have h2 := Fintype.card_le_of_injective _ hinj
    rwa [Fintype.card_finset, Fintype.card_fin, Fintype.card_fin] at h2
  -- divisor gap: d ∣ 2^(m+1) - 1 odd and d ≥ 2^m force equality
  have hd_eq : d = 2 ^ (m + 1) - 1 := by
    obtain ⟨k, hk⟩ := hd_dvd
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    have hodd : Odd (2 ^ (m + 1) - 1) := ⟨2 ^ m - 1, by omega⟩
    have hkodd : Odd k := by
      rcases Nat.even_or_odd k with he | ho
      · exact absurd (hk ▸ hodd)
          (Nat.not_odd_iff_even.mpr (Nat.even_mul.mpr (Or.inr he)))
      · exact ho
    obtain ⟨t, rfl⟩ := hkodd
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · omega
    · exfalso
      have h3 : d * 3 ≤ d * (2 * t + 1) := Nat.mul_le_mul_left d (by omega)
      have h4 : 2 ^ m * 3 ≤ d * 3 := Nat.mul_le_mul_right 3 hcard
      omega
  have hdvd_card : d ∣ Fintype.card G := addOrderOf_dvd_card
  calc 2 ^ (m + 1) - 1 = d := hd_eq.symm
    _ ≤ Fintype.card G := Nat.le_of_dvd Fintype.card_pos hdvd_card

end Chain

/-! ### The bottom-wedge theorem: `2^(m+1) + m ≤ 2|G| + 2` -/

section BottomWedge

variable {G : Type*} [AddCommGroup G] [Fintype G] {m : ℕ}

/-- **Bottom-wedge theorem.**  Let `h : Fin m → G` be dissociated (injective
subset-sum map) in a finite abelian group with injective doubling, admitting
no single-headed witness with head `2` (`hsh2`) or head `3` (`hsh3`).  Then
`2^(m+1) + m ≤ 2|G| + 2`: writing `|G| = 2^m + r`, the family forces
`m ≤ 2(r+1)`.  In particular no such family exists in a group of odd order
`≤ 2^m + (m-3)/2` — the first general-`m` family of window orders excluded.

Mechanism: the `2^m` subset sums miss exactly `|G| - 2^m` elements; for a
fixed `x`, the translate `g ↦ g + 2•h x` sends the value set `H` into
`H ∪ {0} ∪ (complement)` by the four-case target lemma, so at most
`|G| - 2^m + 1` elements escape `H`; and since `hsh2` forbids three-term
arithmetic progressions in `H`, every element escapes within two steps, so
the non-escapees inject into the escapees. -/
theorem bottom_wedge (h : Fin m → G)
    (hinj2 : ∀ x y : G, x + x = y + y → x = y)
    (hdis : Function.Injective fun S : Finset (Fin m) => ∑ j ∈ S, h j)
    (hsh2 : ∀ (x : Fin m) (P M : Finset (Fin m)), x ∉ P → x ∉ M → Disjoint P M →
      P.card + 1 ≤ M.card → 2 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j)
    (hsh3 : ∀ (x : Fin m) (P M : Finset (Fin m)), x ∉ P → x ∉ M → Disjoint P M →
      P.card + 2 ≤ M.card → 3 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j) :
    2 ^ (m + 1) + m ≤ 2 * Fintype.card G + 2 := by
  classical
  set σ : Finset (Fin m) → G := fun S => ∑ j ∈ S, h j with hσ
  have hcard2m : 2 ^ m ≤ Fintype.card G := by
    have h1 := Fintype.card_le_of_injective σ hdis
    rwa [Fintype.card_finset, Fintype.card_fin] at h1
  have hp : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := Fintype.card_pos (α := G)
    omega
  -- basic consequences of dissociation
  have hinj_h : Function.Injective h := by
    intro a b hab
    have h1 : σ {a} = σ {b} := by simp [hσ, hab]
    exact Finset.singleton_injective (hdis h1)
  have h_ne : ∀ a : Fin m, h a ≠ 0 := by
    intro a ha
    have h1 : σ {a} = σ ∅ := by simp [hσ, ha]
    exact absurd (hdis h1) (Finset.singleton_ne_empty a)
  -- no three-term arithmetic progressions among the h's
  have no3AP : ∀ a b c : Fin m, a ≠ b → b ≠ c → a ≠ c → h a + h c ≠ 2 • h b := by
    intro a b c hab hbc hac heq
    refine hsh2 b ∅ {a, c} (Finset.notMem_empty b) (by simp [Ne.symm hab, hbc])
      (Finset.disjoint_empty_left _) (by rw [Finset.card_empty, Finset.card_pair hac]; omega) ?_
    rw [Finset.sum_empty, add_zero, Finset.sum_pair hac]
    exact heq.symm
  -- target lemma, head 2: `2•h x + h y` is never a subset sum over ≥ 2 indices
  have hB2 : ∀ x y : Fin m, x ≠ y → ∀ T : Finset (Fin m), 2 ≤ T.card →
      2 • h x + h y ≠ σ T := by
    intro x y hxy T hT heq
    by_cases hxT : x ∈ T
    · have hs1 : σ T = h x + σ (T.erase x) := (Finset.add_sum_erase T h hxT).symm
      by_cases hyT : y ∈ T
      · have hyT' : y ∈ T.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hyT⟩
        have hs2 : σ (T.erase x) = h y + σ ((T.erase x).erase y) :=
          (Finset.add_sum_erase _ h hyT').symm
        have h1 : h x + (h x + h y) = σ ((T.erase x).erase y) + (h x + h y) := by
          calc h x + (h x + h y) = 2 • h x + h y := by rw [two_nsmul]; abel
            _ = h x + (h y + σ ((T.erase x).erase y)) := by rw [heq, hs1, hs2]
            _ = σ ((T.erase x).erase y) + (h x + h y) := by abel
        have h2 : σ {x} = σ ((T.erase x).erase y) := by
          rw [show σ {x} = h x from by simp [hσ]]
          exact add_right_cancel h1
        have h3 : x ∈ (T.erase x).erase y := (hdis h2) ▸ Finset.mem_singleton_self x
        exact absurd (Finset.mem_of_mem_erase h3) (Finset.notMem_erase x T)
      · have h1 : (h x + h y) + h x = σ (T.erase x) + h x := by
          calc (h x + h y) + h x = 2 • h x + h y := by rw [two_nsmul]; abel
            _ = h x + σ (T.erase x) := by rw [heq, hs1]
            _ = σ (T.erase x) + h x := by abel
        have h2 : σ {x, y} = σ (T.erase x) := by
          rw [show σ {x, y} = h x + h y from by rw [hσ]; exact Finset.sum_pair hxy]
          exact add_right_cancel h1
        have h3 : x ∈ T.erase x := (hdis h2) ▸ Finset.mem_insert_self x {y}
        exact absurd h3 (Finset.notMem_erase x T)
    · by_cases hyT : y ∈ T
      · have hs1 : σ T = h y + σ (T.erase y) := (Finset.add_sum_erase T h hyT).symm
        have h1 : 2 • h x + h y = σ (T.erase y) + h y := by
          calc 2 • h x + h y = σ T := heq
            _ = h y + σ (T.erase y) := hs1
            _ = σ (T.erase y) + h y := by abel
        refine hsh2 x ∅ (T.erase y) (Finset.notMem_empty x)
          (fun hx' => hxT (Finset.mem_of_mem_erase hx'))
          (Finset.disjoint_empty_left _)
          (by rw [Finset.card_empty, Finset.card_erase_of_mem hyT]; omega) ?_
        rw [Finset.sum_empty, add_zero]
        exact add_right_cancel h1
      · refine hsh2 x {y} T (by simp [hxy]) hxT
          (Finset.disjoint_singleton_left.mpr hyT) (by rw [Finset.card_singleton]; omega) ?_
        rw [Finset.sum_singleton]
        exact heq
  -- target lemma, head 3: `3•h x` is never a subset sum over ≥ 2 indices
  have hB3 : ∀ x : Fin m, ∀ T : Finset (Fin m), 2 ≤ T.card → 3 • h x ≠ σ T := by
    intro x T hT heq
    by_cases hxT : x ∈ T
    · have hs1 : σ T = h x + σ (T.erase x) := (Finset.add_sum_erase T h hxT).symm
      have h1 : 2 • h x + h x = σ (T.erase x) + h x := by
        calc 2 • h x + h x = 3 • h x := (succ_nsmul (h x) 2).symm
          _ = h x + σ (T.erase x) := by rw [heq, hs1]
          _ = σ (T.erase x) + h x := by abel
      refine hsh2 x ∅ (T.erase x) (Finset.notMem_empty x) (Finset.notMem_erase x T)
        (Finset.disjoint_empty_left _)
        (by rw [Finset.card_empty, Finset.card_erase_of_mem hxT]; omega) ?_
      rw [Finset.sum_empty, add_zero]
      exact add_right_cancel h1
    · refine hsh3 x ∅ T (Finset.notMem_empty x) hxT (Finset.disjoint_empty_left _)
        (by rw [Finset.card_empty]; omega) ?_
      rw [Finset.sum_empty, add_zero]
      exact heq
  -- the value set, the cube image, and the translation
  set Hs : Finset G := Finset.image h Finset.univ with hHs
  have hHcard : Hs.card = m := by
    rw [hHs, Finset.card_image_of_injective _ hinj_h, Finset.card_univ, Fintype.card_fin]
  set Cimg : Finset G := Finset.image σ Finset.univ with hCimg
  have hCcard : Cimg.card = 2 ^ m := by
    rw [hCimg, Finset.card_image_of_injective _ hdis, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  set x0 : Fin m := ⟨0, hm⟩ with hx0
  set τ : G := 2 • h x0 with hτ
  have hτ0 : τ ≠ 0 := by
    intro h0
    refine h_ne x0 (hinj2 (h x0) 0 ?_)
    rw [← two_nsmul, ← hτ, h0, add_zero]
  have h2τ0 : τ + τ ≠ 0 := fun h0 => hτ0 (hinj2 τ 0 (by rw [h0, add_zero]))
  -- two-step escape: no element of Hs survives two τ-translations inside Hs
  have hstep : ∀ g ∈ Hs, g + τ ∈ Hs → g + τ + τ ∉ Hs := by
    intro g hg hg1 hg2
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hg
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hg1
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hg2
    have hab : a ≠ b := by
      rintro rfl
      rw [ha] at hb
      exact hτ0 (add_left_cancel (show g + 0 = g + τ by rw [add_zero]; exact hb)).symm
    have hbc : b ≠ c := by
      rintro rfl
      rw [hb] at hc
      exact hτ0
        (add_left_cancel (show (g + τ) + 0 = (g + τ) + τ by rw [add_zero]; exact hc)).symm
    have hac : a ≠ c := by
      rintro rfl
      rw [ha, add_assoc] at hc
      exact h2τ0
        (add_left_cancel (show g + 0 = g + (τ + τ) by rw [add_zero]; exact hc)).symm
    refine no3AP a b c hab hbc hac ?_
    rw [ha, hc, hb, two_nsmul]
    abel
  -- split Hs into escapees and non-escapees; non-escapees inject into escapees
  have hsplitc : (Hs.filter fun g => g + τ ∈ Hs).card
      + (Hs.filter fun g => ¬(g + τ ∈ Hs)).card = Hs.card :=
    Finset.card_filter_add_card_filter_not _
  have hBE : (Hs.filter fun g => g + τ ∈ Hs).card
      ≤ (Hs.filter fun g => ¬(g + τ ∈ Hs)).card := by
    refine Finset.card_le_card_of_injOn (fun g => g + τ) ?_ ?_
    · intro g hg
      obtain ⟨hgH, hgin⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨hgin, hstep g hgH hgin⟩
    · intro a _ b _ hab
      exact add_right_cancel hab
  -- escapees inject into {0} ∪ (cube complement)
  have hEW : (Hs.filter fun g => ¬(g + τ ∈ Hs)).card
      ≤ 1 + (Fintype.card G - 2 ^ m) := by
    have hinj_tr : Function.Injective (fun g : G => g + τ) :=
      fun a b hab => add_right_cancel hab
    have himg : (Hs.filter fun g => ¬(g + τ ∈ Hs)).image (fun g => g + τ)
        ⊆ insert (0 : G) (Finset.univ \ Cimg) := by
      intro v hv
      obtain ⟨g, hgE, hgv⟩ := Finset.mem_image.mp hv
      obtain ⟨hgH, hgesc⟩ := Finset.mem_filter.mp hgE
      by_cases hvC : v ∈ Cimg
      · obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hvC
        rcases Nat.lt_or_ge T.card 2 with hTc | hTc
        · have hTc' : T.card = 0 ∨ T.card = 1 := by omega
          rcases hTc' with h0 | h1
          · have hTe : T = ∅ := Finset.card_eq_zero.mp h0
            have hv0 : v = 0 := by rw [← hT, hTe, hσ]; simp
            exact Finset.mem_insert.mpr (Or.inl hv0)
          · exfalso
            obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
            apply hgesc
            rw [hgv, ← hT, hj, show σ {j} = h j from by simp [hσ]]
            exact Finset.mem_image_of_mem h (Finset.mem_univ j)
        · exfalso
          obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hgH
          by_cases hyx : y = x0
          · rw [hyx] at hy
            refine hB3 x0 T hTc ?_
            calc (3 : ℕ) • h x0 = 2 • h x0 + h x0 := by
                  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]
              _ = g + τ := by rw [← hτ, hy]; abel
              _ = v := hgv
              _ = σ T := hT.symm
          · refine hB2 x0 y (Ne.symm hyx) T hTc ?_
            calc 2 • h x0 + h y = g + τ := by rw [← hτ, hy]; abel
              _ = v := hgv
              _ = σ T := hT.symm
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvC⟩)
    have h1 : (Hs.filter fun g => ¬(g + τ ∈ Hs)).card
        = ((Hs.filter fun g => ¬(g + τ ∈ Hs)).image (fun g => g + τ)).card :=
      (Finset.card_image_of_injective _ hinj_tr).symm
    have h2 := Finset.card_le_card himg
    have h3 := Finset.card_insert_le (0 : G) (Finset.univ \ Cimg)
    have h4 : (Finset.univ \ Cimg).card = Fintype.card G - 2 ^ m := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hCcard]
    omega
  omega

end BottomWedge

end MinModulus
