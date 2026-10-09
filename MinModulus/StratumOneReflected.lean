/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneAntipodal
import MinModulus.StratumOneWeight

/-!
# The reflected branch needs `n` even

The branch `ē = -1` of the stratum-one dichotomy is the reflected family, and it
is valid only when `n` is even.  The witness is as simple as it could be: the
multiset consisting of `n` copies of the extra coordinate.

Modulo `M = 2 ^ d - 1` it always matches the target, because the block sums to
`(2 ^ d - 1) - d ≡ -d` and the extra contributes `-1`, while `n` copies of the
extra contribute `-n = -(d + 1)`.  In the parity factor it matches exactly when
`d` is even, since the block entries all have parity opposite to the extra.  So
for `d` even -- that is, `n` odd -- the two sides agree in both CRT factors and
the tuple is not valid.
-/

namespace MinModulus

namespace StratumOne

open Finset

/-- The cyclic powers of two sum to zero modulo the Mersenne number. -/
theorem sum_pow2_univ (d : ℕ) [NeZero d] : ∑ t : ZMod d, pow2 t = 0 := by
  classical
  have hinj : Function.Injective (fun i : Fin d => ((i : ℕ) : ZMod d)) := by
    intro i j hij
    have h := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at h
    exact Fin.ext h
  have hbij : Function.Bijective (fun i : Fin d => ((i : ℕ) : ZMod d)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp [ZMod.card]⟩
  have key : ∑ i : Fin d, pow2 ((i : ℕ) : ZMod d) = ∑ t : ZMod d, pow2 t :=
    Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
  have hterm : ∀ i : Fin d,
      pow2 ((i : ℕ) : ZMod d) = ((2 ^ (i : ℕ) : ℕ) : ZMod (2 ^ d - 1)) := by
    intro i; rw [pow2_natCast]; push_cast; ring
  rw [← key, Finset.sum_congr rfl (fun i _ => hterm i), ← Nat.cast_sum, sum_univ_two_pow,
    ZMod.natCast_self]

/-- **CRT determination.**  At the first even stratum with `M` odd, an element is
determined by its residue and its parity. -/
theorem crt_unique {M : ℕ} (hM : 1 ≤ M) (hodd : Odd M) {x y : ZMod (2 * M)}
    (hres : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x
          = ZMod.castHom (dvd_mul_left M 2) (ZMod M) y)
    (hpar : parityHom M x = parityHom M y) : x = y := by
  have hker : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (x - y) = 0 := by
    rw [map_sub, hres, sub_self]
  rcases kernel_two_mul hM _ hker with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hc := congrArg (parityHom M) h
    rw [map_sub, hpar, sub_self, map_natCast, natCast_odd_eq_one hodd] at hc
    exact zero_ne_one hc

section Reflected

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

/-- **The reflected branch forces `n` even.**  If the extra residue is `-1` and
`d` is even, so that `n = d + 1` is odd, the tuple is not valid: `n` copies of
the extra coordinate already match the target. -/
theorem reflected_not_valid_of_even_dim
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hd : 1 < d) (hdeven : Even d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1)
    (hextra : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext) = -1) :
    ¬ ValidTuple g := by
  classical
  intro hg
  set red := ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) with hred
  have hd1 : 1 ≤ d := le_of_lt hd
  have h2d : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hM : 1 ≤ 2 ^ d - 1 := by omega
  have hodd : Odd (2 ^ d - 1) := mersenne_odd hd1
  have hn : n = d + 1 := card_eq_succ hinj hext hcover
  have hd2 : ((d : ℕ) : ZMod 2) = 0 := by
    calc ((d : ℕ) : ZMod 2) = ((d % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod d 2).symm
      _ = 0 := by rw [Nat.even_iff.mp hdeven]; norm_num
  have hpar := reflected_parity g hg hd hinj hext hcover hblk hextra
  -- the rival: `n` copies of the extra coordinate
  set k : Fin n → ℕ := fun i => if i = ext then n else 0 with hk
  have hkext : k ext = n := by simp [hk]
  have hkemb : ∀ t, k (emb t) = 0 := fun t => by simp [hk, hext t]
  have hcard : ∑ i, k i = n := by
    rw [sum_split hinj hext hcover k, hkext, Finset.sum_congr rfl (fun t _ => hkemb t)]
    simp
  have hrival : ∑ i, k i • g i = ∑ i, g i := by
    refine crt_unique hM hodd ?_ ?_
    · -- residues
      have hblksum : ∑ t : ZMod d, red (g (emb t)) = -(d : ZMod (2 ^ d - 1)) := by
        rw [Finset.sum_congr rfl (fun t _ => hblk t), Finset.sum_sub_distrib, sum_pow2_univ,
          Finset.sum_const, Finset.card_univ, ZMod.card d, nsmul_eq_mul, mul_one]
        ring
      have hrhs : ∑ i, red (g i) = -(d : ZMod (2 ^ d - 1)) - 1 := by
        rw [sum_split hinj hext hcover (fun i => red (g i)), hextra, hblksum]
        ring
      have hlhs : ∑ i, red (k i • g i) = (n : ℕ) • (-1 : ZMod (2 ^ d - 1)) := by
        rw [sum_split hinj hext hcover (fun i => red (k i • g i))]
        simp only [map_nsmul, hkext, hkemb, zero_smul, map_zero, Finset.sum_const_zero,
          add_zero, hextra]
      rw [map_sum, map_sum, hlhs, hrhs, hn]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    · -- parities
      have hrhs : ∑ i, parityHom (2 ^ d - 1) (g i)
          = parityHom (2 ^ d - 1) (g ext) + (d : ℕ) • (parityHom (2 ^ d - 1) (g ext) + 1) := by
        rw [sum_split hinj hext hcover (fun i => parityHom (2 ^ d - 1) (g i)),
          Finset.sum_congr rfl (fun t _ => hpar t), Finset.sum_const, Finset.card_univ,
          ZMod.card d]
      have hlhs : ∑ i, parityHom (2 ^ d - 1) (k i • g i)
          = (n : ℕ) • parityHom (2 ^ d - 1) (g ext) := by
        rw [sum_split hinj hext hcover (fun i => parityHom (2 ^ d - 1) (k i • g i))]
        simp only [map_nsmul, hkext, hkemb, zero_smul, map_zero, Finset.sum_const_zero, add_zero]
      rw [map_sum, map_sum, hlhs, hrhs, hn]
      simp only [nsmul_eq_mul]
      push_cast
      rw [hd2]
      ring
  exact absurd (hg k hcard hrival ext) (by rw [hkext, hn]; omega)

end Reflected

end StratumOne

end MinModulus
