/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneTriple
import MinModulus.StratumOneCancel

/-!
# The stratum-one glue: block vectors become rival multisets

`StratumOneTriple` constructs, for every support `T` with `2 ≤ |T| < d`, a pair
of integer block vectors with coefficient sum `1`, equal value, floor `-1` and
pointwise sum at most `1`.  `StratumOneCancel` shows that three nontrivial
multisets whose multiplicities sum to `3` everywhere cannot all match the target
modulo `M`.

This file is the bridge.  It turns a block vector `δ : ZMod d → ℤ` into an
honest multiplicity function `Fin n → ℕ` on a tuple whose block reduces to the
super-increasing block `2^t - 1` modulo `M = 2^d - 1`, and computes the reduced
target gap in terms of `coeffSum δ` and `value δ`.
-/

namespace MinModulus

namespace StratumOne

open Finset Function

section Split

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

/-- The block positions together with the extra coordinate exhaust the tuple. -/
theorem univ_eq_insert_image (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) :
    (univ : Finset (Fin n)) = insert ext (univ.image emb) := by
  ext j
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_image]
  rcases hcover j with h | ⟨t, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, trivial, ht⟩

/-- The extra coordinate is not a block position. -/
theorem ext_not_mem_image (hext : ∀ t, emb t ≠ ext) :
    ext ∉ (univ.image emb : Finset (Fin n)) := by
  simp only [Finset.mem_image, not_exists]
  intro t
  simp only [not_and]
  intro _
  exact hext t

/-- Splitting a sum over the tuple into the extra coordinate and the block. -/
theorem sum_split {α : Type*} [AddCommMonoid α]
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) (f : Fin n → α) :
    ∑ j, f j = f ext + ∑ t : ZMod d, f (emb t) := by
  rw [univ_eq_insert_image hcover, Finset.sum_insert (ext_not_mem_image hext),
    Finset.sum_image (fun x _ y _ h => hinj h)]

/-- A block plus one extra coordinate has length `d + 1`. -/
theorem card_eq_succ (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) : n = d + 1 := by
  have h := congrArg Finset.card (univ_eq_insert_image (emb := emb) (ext := ext) hcover)
  rw [Finset.card_insert_of_notMem (ext_not_mem_image hext),
    Finset.card_image_of_injective _ hinj] at h
  simpa [Finset.card_univ, ZMod.card d] using h

end Split

section Mult

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n} {δ : ZMod d → ℤ}

/-- The multiplicity vector attached to a block vector `δ`: the prescribed value
`e` at the extra coordinate, and `1 + δ t` at the block position `t`. -/
noncomputable def blockMult (emb : ZMod d → Fin n) (ext : Fin n)
    (δ : ZMod d → ℤ) (e : ℕ) : Fin n → ℕ :=
  fun j => if j = ext then e else (1 + δ (Function.invFun emb j)).toNat

omit [NeZero d] in
@[simp] theorem blockMult_ext (emb : ZMod d → Fin n) (ext : Fin n)
    (δ : ZMod d → ℤ) (e : ℕ) : blockMult emb ext δ e ext = e := by
  simp [blockMult]

omit [NeZero d] in
theorem blockMult_emb (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (e : ℕ) (t : ZMod d) : blockMult emb ext δ e (emb t) = (1 + δ t).toNat := by
  simp only [blockMult, if_neg (hext t), Function.leftInverse_invFun hinj t]

/-- The total multiplicity of a block vector's multiplicity function. -/
theorem sum_blockMult (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) (hδ : ∀ x, -1 ≤ δ x) (e : ℕ) :
    ((∑ j, blockMult emb ext δ e j : ℕ) : ℤ) = (e : ℤ) + d + coeffSum δ := by
  rw [sum_split hinj hext hcover (blockMult emb ext δ e)]
  push_cast
  rw [blockMult_ext]
  have : ∀ t : ZMod d, ((blockMult emb ext δ e (emb t) : ℕ) : ℤ) = 1 + δ t := by
    intro t
    rw [blockMult_emb hinj hext, Int.toNat_of_nonneg (by linarith [hδ t])]
  rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card d, nsmul_eq_mul, mul_one, coeffSum]
  ring

/-- The target gap of a multiplicity vector in an arbitrary abelian group: the
extra coordinate contributes `e - 1` copies of its entry, each block position
its own coefficient. -/
theorem blockMult_gap {A : Type*} [AddCommGroup A]
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) (hδ : ∀ x, -1 ≤ δ x) (e : ℕ)
    (h : Fin n → A) :
    (∑ j, blockMult emb ext δ e j • h j) - (∑ j, h j)
      = ((e : ℤ) - 1) • h ext + ∑ t : ZMod d, δ t • h (emb t) := by
  have hterm : ∀ t : ZMod d, blockMult emb ext δ e (emb t) • h (emb t)
      = h (emb t) + δ t • h (emb t) := by
    intro t
    rw [blockMult_emb hinj hext, ← natCast_zsmul,
      Int.toNat_of_nonneg (by linarith [hδ t] : (0 : ℤ) ≤ 1 + δ t), add_smul, one_smul]
  have hhead : blockMult emb ext δ e ext • h ext = (e : ℤ) • h ext := by
    rw [blockMult_ext, natCast_zsmul]
  rw [sum_split hinj hext hcover (fun j => blockMult emb ext δ e j • h j),
    sum_split hinj hext hcover h, hhead,
    Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
    sub_smul, one_smul]
  abel

/-- **The reduced target gap.**  Modulo `M = 2 ^ d - 1`, a tuple whose block is
the super-increasing block `2 ^ t - 1` turns the multiplicity vector of `δ` into
an explicit expression in `value δ`, `coeffSum δ` and the extra residue. -/
theorem reduced_gap (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j) (hδ : ∀ x, -1 ≤ δ x) (e : ℕ)
    (h : Fin n → ZMod (2 ^ d - 1)) (hblk : ∀ t, h (emb t) = pow2 t - 1) :
    (∑ j, blockMult emb ext δ e j • h j) - (∑ j, h j)
      = ((e : ℤ) - 1) • h ext + value δ - (coeffSum δ) • (1 : ZMod (2 ^ d - 1)) := by
  classical
  have hterm : ∀ t : ZMod d, blockMult emb ext δ e (emb t) • h (emb t)
      = h (emb t) + δ t • h (emb t) := by
    intro t
    rw [blockMult_emb hinj hext, ← natCast_zsmul,
      Int.toNat_of_nonneg (by linarith [hδ t] : (0 : ℤ) ≤ 1 + δ t), add_smul, one_smul]
  have hhead : blockMult emb ext δ e ext • h ext = (e : ℤ) • h ext := by
    rw [blockMult_ext, natCast_zsmul]
  have hdelta : ∑ t : ZMod d, δ t • h (emb t)
      = value δ - (coeffSum δ) • (1 : ZMod (2 ^ d - 1)) := by
    have hpt : ∀ t : ZMod d,
        δ t • h (emb t) = δ t • pow2 t - δ t • (1 : ZMod (2 ^ d - 1)) := by
      intro t; rw [hblk t, smul_sub]
    rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_sub_distrib, ← Finset.sum_smul]
    simp only [value, coeffSum]
  rw [sum_split hinj hext hcover (fun j => blockMult emb ext δ e j • h j),
    sum_split hinj hext hcover h, hhead,
    Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib, hdelta,
    sub_smul, one_smul]
  abel

end Mult

section Exclusion

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

/-- The third member of a cancelling triple of block vectors. -/
def negSum (a b : ZMod d → ℤ) : ZMod d → ℤ := fun x => -(a x + b x)

omit [NeZero d] in
@[simp] theorem negSum_apply (a b : ZMod d → ℤ) (x : ZMod d) :
    negSum a b x = -(a x + b x) := rfl

theorem coeffSum_negSum (a b : ZMod d → ℤ) :
    coeffSum (negSum a b) = -(coeffSum a + coeffSum b) := by
  simp only [coeffSum, negSum_apply, Finset.sum_neg_distrib, Finset.sum_add_distrib]

theorem value_negSum (a b : ZMod d → ℤ) :
    value (negSum a b) = -(value a + value b) := by
  have h : ∀ x : ZMod d, negSum a b x • pow2 x = -(a x • pow2 x + b x • pow2 x) := by
    intro x; rw [negSum_apply, neg_smul, add_smul]
  simp only [value, Finset.sum_congr rfl (fun x _ => h x), Finset.sum_neg_distrib,
    Finset.sum_add_distrib]

/-- **Stratum-one exclusion.**  A tuple modulo `2 * (2 ^ d - 1)` whose block
reduces to the super-increasing block `2 ^ t - 1` and whose extra entry reduces
to `(∑ t ∈ T, 2 ^ (t - 1)) - 1` for a support `T` with `2 ≤ |T| < d` is not
valid: the compatible pair of block vectors assembles into a cancelling triple
of rival multisets. -/
theorem not_validTuple_of_support
    (g : Fin n → ZMod (2 * (2 ^ d - 1)))
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ j : Fin n, j = ext ∨ ∃ t, emb t = j)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g (emb t))
      = pow2 t - 1)
    (T : Finset (ZMod d)) (hs : 2 ≤ T.card) (hsd : T.card < d)
    (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext)
      = (∑ t ∈ T, pow2 (t - 1)) - 1) :
    ¬ ValidTuple g := by
  classical
  intro hg
  set red := ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) with hred
  set V : ZMod (2 ^ d - 1) := ∑ t ∈ T, pow2 (t - 1) with hV
  have hd1 : 1 ≤ d := le_trans (by omega) (le_of_lt hsd)
  have hMpos : 1 ≤ 2 ^ d - 1 := by
    have : 2 ≤ 2 ^ d := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
    omega
  have hn : n = d + 1 := card_eq_succ hinj hext hcover
  obtain ⟨L₁, L₂, hc₁, hc₂, hv₁, hv₂, hlo₁, hlo₂, hcompat⟩ :=
    exists_compatible_pair T hs hsd
  set δ₁ := assemble T L₁ with hδ₁
  set δ₂ := assemble T L₂ with hδ₂
  set δ₃ := negSum δ₁ δ₂ with hδ₃
  have hlo₃ : ∀ x, (-1 : ℤ) ≤ δ₃ x := by
    intro x; have := hcompat x; simp only [hδ₃, negSum_apply]; omega
  have hc₃ : coeffSum δ₃ = -2 := by rw [hδ₃, coeffSum_negSum, hc₁, hc₂]; ring
  have hv₃ : value δ₃ = -(V + V) := by rw [hδ₃, value_negSum, hv₁, hv₂, ← hV]
  -- the three multiplicity vectors
  set k₁ := blockMult emb ext δ₁ 0 with hk₁
  set k₂ := blockMult emb ext δ₂ 0 with hk₂
  set k₃ := blockMult emb ext δ₃ 3 with hk₃
  -- total multiplicities
  have htot : ∀ (δ : ZMod d → ℤ) (e : ℕ), (∀ x, (-1 : ℤ) ≤ δ x) →
      (e : ℤ) + d + coeffSum δ = (n : ℤ) → ∑ j, blockMult emb ext δ e j = n := by
    intro δ e hδ hval
    have := sum_blockMult hinj hext hcover hδ e
    exact Nat.cast_injective (by rw [this, hval])
  have hcard₁ : ∑ j, k₁ j = n := htot _ _ hlo₁ (by rw [hc₁, hn]; push_cast; ring)
  have hcard₂ : ∑ j, k₂ j = n := htot _ _ hlo₂ (by rw [hc₂, hn]; push_cast; ring)
  have hcard₃ : ∑ j, k₃ j = n := htot _ _ hlo₃ (by rw [hc₃, hn]; push_cast; ring)
  -- nontriviality
  have hne₁ : ∃ j, k₁ j ≠ 1 := ⟨ext, by rw [hk₁, blockMult_ext]; omega⟩
  have hne₂ : ∃ j, k₂ j ≠ 1 := ⟨ext, by rw [hk₂, blockMult_ext]; omega⟩
  have hne₃ : ∃ j, k₃ j ≠ 1 := ⟨ext, by rw [hk₃, blockMult_ext]; omega⟩
  -- the multiplicities sum to three at every coordinate
  have hsum : ∀ j, k₁ j + k₂ j + k₃ j = 3 := by
    intro j
    rcases hcover j with rfl | ⟨t, rfl⟩
    · simp [hk₁, hk₂, hk₃]
    · have e₁ := blockMult_emb (δ := δ₁) hinj hext 0 t
      have e₂ := blockMult_emb (δ := δ₂) hinj hext 0 t
      have e₃ := blockMult_emb (δ := δ₃) hinj hext 3 t
      have b₁ := hlo₁ t
      have b₂ := hlo₂ t
      have b₃ := hcompat t
      rw [hk₁, hk₂, hk₃, e₁, e₂, e₃]
      simp only [hδ₃, negSum_apply]
      omega
  -- the reduced target gaps vanish
  have hgap : ∀ (δ : ZMod d → ℤ) (e : ℕ), (∀ x, (-1 : ℤ) ≤ δ x) →
      ((e : ℤ) - 1) • ((∑ t ∈ T, pow2 (t - 1)) - 1 : ZMod (2 ^ d - 1)) + value δ
        - (coeffSum δ) • (1 : ZMod (2 ^ d - 1)) = 0 →
      red ((∑ j, blockMult emb ext δ e j • g j) - ∑ j, g j) = 0 := by
    intro δ e hδ hzero
    rw [map_sub, map_sum, map_sum]
    have hns : ∀ j, red (blockMult emb ext δ e j • g j)
        = blockMult emb ext δ e j • red (g j) := fun j => map_nsmul red _ _
    rw [Finset.sum_congr rfl (fun j _ => hns j)]
    rw [reduced_gap hinj hext hcover hδ e (fun j => red (g j)) hblk, hextra]
    exact hzero
  have hz₁ : red ((∑ j, k₁ j • g j) - ∑ j, g j) = 0 := by
    refine hgap _ _ hlo₁ ?_
    rw [hv₁, hc₁, ← hV]
    simp only [Nat.cast_zero, zero_sub, neg_smul, one_smul]
    ring
  have hz₂ : red ((∑ j, k₂ j • g j) - ∑ j, g j) = 0 := by
    refine hgap _ _ hlo₂ ?_
    rw [hv₂, hc₂, ← hV]
    simp only [Nat.cast_zero, zero_sub, neg_smul, one_smul]
    ring
  have hz₃ : red ((∑ j, k₃ j • g j) - ∑ j, g j) = 0 := by
    refine hgap _ _ hlo₃ ?_
    rw [hv₃, hc₃, ← hV]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  exact no_cancelling_triple hMpos hg k₁ k₂ k₃ hcard₁ hcard₂ hcard₃
    hne₁ hne₂ hne₃ hz₁ hz₂ hz₃ hsum

end Exclusion

section Concrete

variable {d : ℕ} [NeZero d]

/-- The block embedding: block position `t` occupies index `t.val` of `Fin (d + 1)`,
and the extra coordinate is the last one. -/
def blockEmb (d : ℕ) [NeZero d] : ZMod d → Fin (d + 1) :=
  fun t => Fin.castSucc ⟨t.val, ZMod.val_lt t⟩

theorem blockEmb_injective : Function.Injective (blockEmb d) := by
  intro a b hab
  have hv : a.val = b.val := by simpa [blockEmb, Fin.ext_iff] using hab
  have h := congrArg (fun k : ℕ => (k : ZMod d)) hv
  simpa [ZMod.natCast_val, ZMod.cast_id] using h

theorem blockEmb_ne_last (t : ZMod d) : blockEmb d t ≠ Fin.last d := by
  simp [blockEmb, Fin.ext_iff]
  exact Nat.ne_of_lt (ZMod.val_lt t)

theorem blockEmb_cover (j : Fin (d + 1)) :
    j = Fin.last d ∨ ∃ t, blockEmb d t = j := by
  rcases Nat.lt_or_ge (j : ℕ) d with hj | hj
  · refine Or.inr ⟨((j : ℕ) : ZMod d), ?_⟩
    have hv : (((j : ℕ) : ZMod d)).val = (j : ℕ) := ZMod.val_natCast_of_lt hj
    apply Fin.ext
    simp [blockEmb, hv]
  · refine Or.inl (Fin.ext ?_)
    have h2 := j.isLt
    simp only [Fin.val_last]
    omega

omit [NeZero d] in
/-- The first even stratum: `2 * (2 ^ d - 1) = 2 ^ (d + 1) - 2`. -/
theorem two_mul_mersenne : 2 * (2 ^ d - 1) = 2 ^ (d + 1) - 2 := by
  have h : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  rw [pow_succ]
  omega

/-- **Stratum-one exclusion, concrete form.**  Let `d ≥ 1` and let
`g : Fin (d + 1) → ZMod (2 * (2 ^ d - 1))` reduce modulo `M = 2 ^ d - 1` to the
super-increasing block `2 ^ i - 1` on its first `d` coordinates.  If its last
entry reduces to `(∑ t ∈ T, 2 ^ (t - 1)) - 1` for a support `T` of size at least
two and less than `d`, then `g` is not a valid tuple.

The modulus is the first even stratum: `2 * (2 ^ d - 1) = 2 ^ (d + 1) - 2`. -/
theorem not_validTuple_of_superIncreasing_block
    (g : Fin (d + 1) → ZMod (2 * (2 ^ d - 1)))
    (hblk : ∀ i : Fin d, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g i.castSucc) = 2 ^ (i : ℕ) - 1)
    (T : Finset (ZMod d)) (hs : 2 ≤ T.card) (hsd : T.card < d)
    (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g (Fin.last d))
      = (∑ t ∈ T, pow2 (t - 1)) - 1) :
    ¬ ValidTuple g :=
  not_validTuple_of_support g blockEmb_injective blockEmb_ne_last blockEmb_cover
    (fun t => hblk ⟨t.val, ZMod.val_lt t⟩) T hs hsd hextra

end Concrete

end StratumOne

end MinModulus
