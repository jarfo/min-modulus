/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneWeight
import MinModulus.StratumOneAntipodal

/-!
# The stratum-one dichotomy

Assembling the two branches.  Let `g` be a valid tuple modulo
`2 * (2 ^ d - 1) = 2 ^ (d + 1) - 2` whose block reduces to the
super-increasing block `2 ^ t - 1` modulo `M = 2 ^ d - 1`, and let `ē` be the
residue of its extra entry.  Write `u = ē + 1`.

* `u` of binary weight at least two is impossible (`StratumOneWeight`);
* `u = 0`, i.e. `ē = -1`, is the reflected case;
* `u = 2 ^ k`, i.e. `ē = 2 ^ k - 1`, forces an antipodal pair and a parity
  vector constant off that pair (`StratumOneAntipodal`).

So only the last two survive, and that is the dichotomy below.
-/

namespace MinModulus

namespace StratumOne

open Finset

variable {d n : ℕ} [NeZero d] {emb : ZMod d → Fin n} {ext : Fin n}

/-- **The stratum-one dichotomy.**  A valid tuple at the first even stratum
whose block reduces to the super-increasing block has an extra residue of
binary weight at most one: either `ē = -1`, or `ē = 2 ^ k - 1` for some `k`, in
which case the extra coordinate and block position `k` form an antipodal pair
and every block position other than `k` carries the same parity. -/
theorem stratum_one_dichotomy
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hg : ValidTuple g) (hd : 1 < d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1) :
    ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext) = -1
    ∨ ∃ k : ZMod d,
        ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext)
          = pow2 k - 1
        ∧ g ext = g (emb k) + ((2 ^ d - 1 : ℕ) : ZMod (2 * (2 ^ d - 1)))
        ∧ ∀ j₁ j₂ : ZMod d, j₁ ≠ k → j₂ ≠ k →
            parityHom (2 ^ d - 1) (g (emb j₁)) = parityHom (2 ^ d - 1) (g (emb j₂)) := by
  classical
  have hd1 : 1 ≤ d := le_of_lt hd
  have h2d : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hM : 1 ≤ 2 ^ d - 1 := by omega
  obtain ⟨S, hcard, hsum⟩ := exists_pow2_support
    (ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext) + 1)
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · -- weight at most one: the two surviving cases
    interval_cases hc : S.card
    · left
      rw [Finset.card_eq_zero.mp hc] at hsum
      simp only [Finset.sum_empty] at hsum
      linear_combination -hsum
    · right
      obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
      rw [hk, Finset.sum_singleton] at hsum
      have hres : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g ext)
          = pow2 k - 1 := by linear_combination -hsum
      refine ⟨k, hres, ?_, ?_⟩
      · exact antipodal_pair hg hM (fun h => hext k h.symm) (by rw [hres, hblk k])
      · exact fun j₁ j₂ h₁ h₂ =>
          parity_const_off_pair g hg hd hinj hext hcover hblk hres h₁ h₂
  · -- weight at least two is excluded
    exact absurd hg (not_validTuple_of_support g hinj hext hcover hblk
      (S.image (fun s => s + 1)) (by rwa [card_image_add_one])
      (by rwa [card_image_add_one]) (by rw [sum_pow2_pred_image, hsum]; ring))

omit [NeZero d] in
/-- `1 ≠ 0` in `ZMod d` once `d ≥ 2`. -/
theorem succ_ne_self (hd : 1 < d) (k : ZMod d) : k + 1 ≠ k := by
  intro h
  have h1 : (1 : ZMod d) = 0 := by
    have : k + 1 = k + 0 := by rw [add_zero]; exact h
    exact add_left_cancel this
  have hv : (1 : ZMod d).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hd]
  rw [h1, ZMod.val_zero] at hv
  exact absurd hv (by norm_num)

/-- **The singleton parity fibre.**  A valid tuple at the first even stratum
whose block reduces to the super-increasing block has one coordinate whose
parity differs from every other coordinate's.  This is the hypothesis the
parity-fibre half descent consumes, and it holds in both branches of the
dichotomy. -/
theorem singleton_parity_fibre
    (g : Fin n → ZMod (2 * (2 ^ d - 1))) (hg : ValidTuple g) (hd : 1 < d)
    (hinj : Function.Injective emb) (hext : ∀ t, emb t ≠ ext)
    (hcover : ∀ i : Fin n, i = ext ∨ ∃ t, emb t = i)
    (hblk : ∀ t, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (emb t)) = pow2 t - 1) :
    ∃ i₀ : Fin n, ∀ i : Fin n, i ≠ i₀ →
      parityHom (2 ^ d - 1) (g i) = parityHom (2 ^ d - 1) (g i₀) + 1 := by
  classical
  have hd1 : 1 ≤ d := le_of_lt hd
  rcases stratum_one_dichotomy g hg hd hinj hext hcover hblk with hrefl | ⟨k, _, hpair, hconst⟩
  · -- the reflected branch: the extra coordinate is alone
    refine ⟨ext, fun i hi => ?_⟩
    rcases hcover i with rfl | ⟨t, rfl⟩
    · exact absurd rfl hi
    · exact reflected_parity g hg hd hinj hext hcover hblk hrefl t
  · -- the antipodal branch: either the extra or its partner is alone
    have hbpair : parityHom (2 ^ d - 1) (g ext)
        = parityHom (2 ^ d - 1) (g (emb k)) + 1 := antipodal_parity hd1 hpair
    by_cases hpq : parityHom (2 ^ d - 1) (g (emb (k + 1)))
        = parityHom (2 ^ d - 1) (g (emb k))
    · refine ⟨ext, fun i hi => ?_⟩
      rcases hcover i with rfl | ⟨t, rfl⟩
      · exact absurd rfl hi
      · by_cases htk : t = k
        · subst htk
          have key : ∀ q : ZMod 2, q = (q + 1) + 1 := by decide
          rw [hbpair]; exact key _
        · have h1 := hconst t (k + 1) htk (succ_ne_self hd k)
          rw [h1, hpq, hbpair]
          have key : ∀ q : ZMod 2, q = (q + 1) + 1 := by decide
          exact key _
    · refine ⟨emb k, fun i hi => ?_⟩
      have hstep : ∀ p q : ZMod 2, p ≠ q → p = q + 1 := by decide
      rcases hcover i with rfl | ⟨t, rfl⟩
      · exact hbpair
      · have htk : t ≠ k := fun h => hi (by rw [h])
        rw [hconst t (k + 1) htk (succ_ne_self hd k)]
        exact hstep _ _ hpq

end StratumOne

end MinModulus
