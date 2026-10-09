/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneRivals
import MinModulus.StratumOneParity
import MinModulus.G1Triangle

/-!
# The antipodal branch: parity is constant off the pair

When the extra residue is an SI value, `ē = 2 ^ k - 1`, the extra coordinate and
block position `k` reduce to the same residue modulo `M = 2 ^ d - 1`, so they
differ by the sheet: they are an *antipodal pair*.  The rivals that omit both
members of that pair then force the parity vector to be constant on the rest of
the block.

The explicit family is, for each block index `j` other than `k` and `k + 1`,

    δ = e_{k+1} + 2 e_{j-1} - e_j - e_k,

which has coefficient sum `1` and value `2 ^ k`, hence is a rival once the
extra coordinate is omitted, and whose parity vector is `e_{k+1} + e_j + e_k`.
-/

namespace MinModulus

namespace StratumOne

open Finset

section Indicator

variable {d : ℕ} [NeZero d]

/-- The indicator of a block index. -/
def ind (c : ZMod d) : ZMod d → ℤ := fun x => if x = c then 1 else 0

omit [NeZero d] in
theorem ind_nonneg (c x : ZMod d) : (0 : ℤ) ≤ ind c x := by
  unfold ind; split_ifs <;> norm_num

theorem sum_ind_smul {A : Type*} [AddCommGroup A] (c : ZMod d) (h : ZMod d → A) :
    ∑ x : ZMod d, ind c x • h x = h c := by
  classical
  have hpt : ∀ x : ZMod d, ind c x • h x = if x = c then h x else 0 := by
    intro x; unfold ind; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite_eq' Finset.univ c h]
  simp

theorem sum_ind (c : ZMod d) : ∑ x : ZMod d, ind c x = 1 := by
  have := sum_ind_smul (A := ℤ) c (fun _ => (1 : ℤ))
  simpa using this

end Indicator

section Anti

variable {d : ℕ} [NeZero d]

/-- The spanning rival of the antipodal case, as a full block vector: it omits
block position `k` (coefficient `-1`), so together with the omitted extra
coordinate it omits the whole antipodal pair. -/
def antiVec (k j : ZMod d) : ZMod d → ℤ :=
  fun x => ind (k + 1) x + ind (j - 1) x + ind (j - 1) x - ind j x - ind k x

theorem coeffSum_antiVec (k j : ZMod d) : coeffSum (antiVec k j) = 1 := by
  simp only [coeffSum, antiVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_ind]
  ring

omit [NeZero d] in
theorem antiVec_ge {k j : ZMod d} (hjk : j ≠ k) (x : ZMod d) : -1 ≤ antiVec k j x := by
  have h1 := ind_nonneg (k + 1) x
  have h2 := ind_nonneg (j - 1) x
  have h3 : ind j x + ind k x ≤ 1 := by
    unfold ind
    by_cases hx : x = j
    · subst hx; rw [if_pos rfl, if_neg hjk]; norm_num
    · rw [if_neg hx]; split_ifs <;> norm_num
  unfold antiVec
  linarith

/-- Successor multiplies the cyclic power map by two. -/
theorem pow2_succ (hd : 1 < d) (x : ZMod d) :
    pow2 (x + 1) = pow2 x + pow2 x := by
  have h1 : pow2 (1 : ZMod d) = 2 := by
    unfold pow2
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hd]
    ring
  rw [pow2_add, h1]
  ring

theorem value_antiVec (hd : 1 < d) (k j : ZMod d) : value (antiVec k j) = pow2 k := by
  have hj : pow2 j = pow2 (j - 1) + pow2 (j - 1) := by
    have := pow2_succ hd (j - 1)
    rwa [sub_add_cancel] at this
  have hk : pow2 (k + 1) = pow2 k + pow2 k := pow2_succ hd k
  have hpt : ∀ x : ZMod d, antiVec k j x • pow2 x
      = ind (k + 1) x • pow2 x + ind (j - 1) x • pow2 x + ind (j - 1) x • pow2 x
        - ind j x • pow2 x - ind k x • pow2 x := by
    intro x; unfold antiVec; simp only [sub_smul, add_smul]
  simp only [value, Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_ind_smul]
  rw [hj, hk]
  abel

/-- The parity vector of the spanning rival is `e_{k+1} + e_j + e_k`. -/
theorem antiVec_parity_sum {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
    (k j : ZMod d) (h : ZMod d → A) :
    ∑ x : ZMod d, antiVec k j x • h x = h (k + 1) + h j + h k := by
  have hpt : ∀ x : ZMod d, antiVec k j x • h x
      = ind (k + 1) x • h x + ind (j - 1) x • h x + ind (j - 1) x • h x
        - ind j x • h x - ind k x • h x := by
    intro x; unfold antiVec; simp only [sub_smul, add_smul]
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_ind_smul]
  have hneg : ∀ a : A, -a = a := fun a => by
    have := hA a; linear_combination (norm := abel) -this
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hneg]
  have hz : h (j - 1) + h (j - 1) = 0 := hA _
  calc h (k + 1) + h (j - 1) + h (j - 1) + h j + h k
      = (h (j - 1) + h (j - 1)) + (h (k + 1) + h j + h k) := by abel
    _ = h (k + 1) + h j + h k := by rw [hz, zero_add]

end Anti

section Pair

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

omit [NeZero d] in
/-- The sheet of the first even stratum is odd. -/
theorem mersenne_odd (hd : 1 ≤ d) : Odd (2 ^ d - 1) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
  subst hm
  rw [Nat.odd_iff, pow_add, pow_one]
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

omit [NeZero d] in
/-- Two coordinates with the same residue modulo the sheet differ by the sheet. -/
theorem antipodal_pair {g : Fin n → ZMod (2 * (2 ^ d - 1))} (hg : ValidTuple g)
    (hM : 1 ≤ 2 ^ d - 1) {a b : Fin n} (hab : a ≠ b)
    (hres : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g a)
      = ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g b)) :
    g a = g b + ((2 ^ d - 1 : ℕ) : ZMod (2 * (2 ^ d - 1))) := by
  have hker : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g a - g b) = 0 := by rw [map_sub, hres, sub_self]
  rcases kernel_two_mul hM _ hker with h | h
  · exact absurd (validTuple_injective g hg (sub_eq_zero.mp h)) hab
  · exact sub_eq_iff_eq_add'.mp h

omit [NeZero d] in
/-- An antipodal pair has opposite parities. -/
theorem antipodal_parity {g : Fin n → ZMod (2 * (2 ^ d - 1))} (hd : 1 ≤ d) {a b : Fin n}
    (hpair : g a = g b + ((2 ^ d - 1 : ℕ) : ZMod (2 * (2 ^ d - 1)))) :
    parityHom (2 ^ d - 1) (g a) = parityHom (2 ^ d - 1) (g b) + 1 := by
  have h := congrArg (parityHom (2 ^ d - 1)) hpair
  rwa [map_add, map_natCast, natCast_odd_eq_one (mersenne_odd hd)] at h

/-- **The antipodal branch.**  Let `g` be a valid tuple at the first even stratum
whose block reduces to the super-increasing block modulo `M = 2 ^ d - 1` and
whose extra entry reduces to the SI value `2 ^ k - 1`.  Then the extra
coordinate and block position `k` are an antipodal pair, and the parity vector is
constant on the rest of the block: every block position other than `k` has the
same parity as `k + 1`. -/
theorem antipodal_parity_const
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hg : ValidTuple g) (hd : 1 < d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1)
    {k : ZMod d} (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g ext) = pow2 k - 1)
    {j : ZMod d} (hjk : j ≠ k) :
    parityHom (2 ^ d - 1) (g (emb (k + 1))) = parityHom (2 ^ d - 1) (g (emb j)) := by
  classical
  have hd1 : 1 ≤ d := le_of_lt hd
  have h2d : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hM : 1 ≤ 2 ^ d - 1 := by omega
  have hodd : Odd (2 ^ d - 1) := mersenne_odd hd1
  have hn : n = d + 1 := card_eq_succ hinj hext hcover
  -- the antipodal pair
  have hres : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext)
      = ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g (emb k)) := by
    rw [hextra, hblk k]
  have hbpair := antipodal_parity (g := g) hd1
    (antipodal_pair hg hM (fun h => hext k h.symm) hres)
  -- the rival omitting both members of the pair
  have hlo : ∀ x, (-1 : ℤ) ≤ antiVec k j x := antiVec_ge hjk
  have hcard : ∑ i, blockMult emb ext (antiVec k j) 0 i = n := by
    have hs := sum_blockMult hinj hext hcover hlo 0
    have hval : ((0 : ℕ) : ℤ) + (d : ℤ) + coeffSum (antiVec k j) = (n : ℤ) := by
      rw [coeffSum_antiVec, hn]; push_cast; ring
    exact Nat.cast_injective (by rw [hs, hval])
  have hnt : ∃ i, blockMult emb ext (antiVec k j) 0 i ≠ 1 :=
    ⟨ext, by rw [blockMult_ext]; omega⟩
  have hmod : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      ((∑ i, blockMult emb ext (antiVec k j) 0 i • g i) - ∑ i, g i) = 0 := by
    rw [map_sub, map_sum, map_sum,
      Finset.sum_congr rfl (fun i _ =>
        map_nsmul (ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))) _ (g i)),
      reduced_gap hinj hext hcover hlo 0
        (fun i => ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g i)) hblk,
      hextra, value_antiVec hd, coeffSum_antiVec]
    simp only [Nat.cast_zero, zero_sub, neg_smul, one_smul]
    ring
  have hpar := sheet_parity_of_valid hM hodd hg hcard hnt hmod
  -- read the identity in the parity factor
  have hgap := blockMult_gap hinj hext hcover hlo 0
    (fun i => parityHom (2 ^ d - 1) (g i))
  have hsum : ∑ t : ZMod d, antiVec k j t • parityHom (2 ^ d - 1) (g (emb t))
      = parityHom (2 ^ d - 1) (g (emb (k + 1))) + parityHom (2 ^ d - 1) (g (emb j))
        + parityHom (2 ^ d - 1) (g (emb k)) :=
    antiVec_parity_sum (by decide) k j (fun t => parityHom (2 ^ d - 1) (g (emb t)))
  rw [hsum] at hgap
  rw [hpar] at hgap
  simp only [Nat.cast_zero, zero_sub, neg_one_zsmul, add_sub_cancel_left] at hgap
  have key : ∀ x y z w : ZMod 2, (1 : ZMod 2) = -w + (x + y + z) → w = z + 1 → x = y := by
    decide
  exact key _ _ _ _ hgap hbpair

/-- **Parity is constant off the antipodal pair.**  Under the hypotheses of
`antipodal_parity_const`, any two block positions other than `k` carry the same
parity.  Together with the opposite parities of the pair itself, this is the
singleton-parity-fibre shape of the stratum-one classification. -/
theorem parity_const_off_pair
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hg : ValidTuple g) (hd : 1 < d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1)
    {k : ZMod d} (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g ext) = pow2 k - 1)
    {j₁ j₂ : ZMod d} (h₁ : j₁ ≠ k) (h₂ : j₂ ≠ k) :
    parityHom (2 ^ d - 1) (g (emb j₁)) = parityHom (2 ^ d - 1) (g (emb j₂)) :=
  (antipodal_parity_const g hg hd hinj hext hcover hblk hextra h₁).symm.trans
    (antipodal_parity_const g hg hd hinj hext hcover hblk hextra h₂)

end Pair

section Reflected

variable {d : ℕ} [NeZero d]

/-- The rival of the reflected case: doubling block position `t` and omitting
its successor has value zero. -/
def zeroVec (t : ZMod d) : ZMod d → ℤ :=
  fun x => ind t x + ind t x - ind (t + 1) x

theorem coeffSum_zeroVec (t : ZMod d) : coeffSum (zeroVec t) = 1 := by
  simp only [coeffSum, zeroVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_ind]
  ring

omit [NeZero d] in
theorem zeroVec_ge (t : ZMod d) (x : ZMod d) : -1 ≤ zeroVec t x := by
  have h1 := ind_nonneg t x
  have h2 : ind (t + 1) x ≤ 1 := by unfold ind; split_ifs <;> norm_num
  unfold zeroVec
  linarith

theorem value_zeroVec (hd : 1 < d) (t : ZMod d) : value (zeroVec t) = 0 := by
  have hpt : ∀ x : ZMod d, zeroVec t x • pow2 x
      = ind t x • pow2 x + ind t x • pow2 x - ind (t + 1) x • pow2 x := by
    intro x; unfold zeroVec; simp only [sub_smul, add_smul]
  simp only [value, Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_ind_smul]
  rw [pow2_succ hd t]
  abel

/-- The parity vector of the reflected rival is `e_{t+1}`. -/
theorem zeroVec_parity_sum {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
    (t : ZMod d) (h : ZMod d → A) :
    ∑ x : ZMod d, zeroVec t x • h x = h (t + 1) := by
  have hpt : ∀ x : ZMod d, zeroVec t x • h x
      = ind t x • h x + ind t x • h x - ind (t + 1) x • h x := by
    intro x; unfold zeroVec; simp only [sub_smul, add_smul]
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_ind_smul]
  have hneg : ∀ a : A, -a = a := fun a => by
    have := hA a; linear_combination (norm := abel) -this
  rw [sub_eq_add_neg, hneg, hA (h t), zero_add]

end Reflected

section ReflectedPair

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

/-- **The reflected branch.**  If the extra residue is `-1`, every block entry
has parity opposite to the extra coordinate. -/
theorem reflected_parity
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hg : ValidTuple g) (hd : 1 < d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1)
    (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext) = -1)
    (j : ZMod d) :
    parityHom (2 ^ d - 1) (g (emb j)) = parityHom (2 ^ d - 1) (g ext) + 1 := by
  classical
  have hd1 : 1 ≤ d := le_of_lt hd
  have h2d : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hM : 1 ≤ 2 ^ d - 1 := by omega
  have hodd : Odd (2 ^ d - 1) := mersenne_odd hd1
  have hn : n = d + 1 := card_eq_succ hinj hext hcover
  set t : ZMod d := j - 1 with ht
  have htj : t + 1 = j := by rw [ht]; ring
  have hlo : ∀ x, (-1 : ℤ) ≤ zeroVec t x := zeroVec_ge t
  have hcard : ∑ i, blockMult emb ext (zeroVec t) 0 i = n := by
    have hs := sum_blockMult hinj hext hcover hlo 0
    have hval : ((0 : ℕ) : ℤ) + (d : ℤ) + coeffSum (zeroVec t) = (n : ℤ) := by
      rw [coeffSum_zeroVec, hn]; push_cast; ring
    exact Nat.cast_injective (by rw [hs, hval])
  have hnt : ∃ i, blockMult emb ext (zeroVec t) 0 i ≠ 1 :=
    ⟨ext, by rw [blockMult_ext]; omega⟩
  have hmod : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      ((∑ i, blockMult emb ext (zeroVec t) 0 i • g i) - ∑ i, g i) = 0 := by
    rw [map_sub, map_sum, map_sum,
      Finset.sum_congr rfl (fun i _ =>
        map_nsmul (ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))) _ (g i)),
      reduced_gap hinj hext hcover hlo 0
        (fun i => ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g i)) hblk,
      hextra, value_zeroVec hd, coeffSum_zeroVec]
    simp only [Nat.cast_zero, zero_sub, neg_smul, one_smul]
    ring
  have hpar := sheet_parity_of_valid hM hodd hg hcard hnt hmod
  have hgap := blockMult_gap hinj hext hcover hlo 0
    (fun i => parityHom (2 ^ d - 1) (g i))
  have hsum : ∑ x : ZMod d, zeroVec t x • parityHom (2 ^ d - 1) (g (emb x))
      = parityHom (2 ^ d - 1) (g (emb (t + 1))) :=
    zeroVec_parity_sum (by decide) t (fun x => parityHom (2 ^ d - 1) (g (emb x)))
  rw [hsum, htj, hpar] at hgap
  simp only [Nat.cast_zero, zero_sub, neg_one_zsmul, add_sub_cancel_left] at hgap
  have key : ∀ x w : ZMod 2, (1 : ZMod 2) = -w + x → x = w + 1 := by decide
  exact key _ _ hgap

end ReflectedPair

end StratumOne

end MinModulus
