import MinModulus.StratumOneTriple

/-!
# Why a cancelling triple kills a stratum-one lift

At the first even stratum the modulus is `N = 2M`.  A multiset `κ` of size
`n` that matches the target *modulo `M`* but not modulo `N` must miss it by
exactly the sheet `M`, because the kernel of `ZMod (2M) → ZMod M` is
`{0, M}` and validity forbids the value `0`.

So three such multisets whose multiplicities sum to `3` everywhere give

    3 • ∑ g  =  ∑_i ∑_j κ^i_j • g_j  =  3 • ∑ g + 3 • M,

whence `3M = 0` in `ZMod 2M`.  But `M + M = 0` there, so `3M = M ≠ 0`.
That contradiction is the whole content of the cancelling triple: no
parity vector can separate an odd number of mod-`M` rivals whose
multiplicities cancel.
-/

namespace MinModulus

open Finset

namespace StratumOne

/-- The sheet `M` is nonzero modulo `2M`. -/
theorem sheet_ne_zero {M : ℕ} (hM : 1 ≤ M) :
    ((M : ℕ) : ZMod (2 * M)) ≠ 0 := by
  haveI : NeZero (2 * M) := ⟨by omega⟩
  intro h
  have hval : ((M : ℕ) : ZMod (2 * M)).val = M % (2 * M) := by
    rw [ZMod.val_natCast]
  rw [h] at hval
  simp only [ZMod.val_zero] at hval
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  omega

/-- The sheet is `2`-torsion. -/
theorem sheet_add_self {M : ℕ} :
    ((M : ℕ) : ZMod (2 * M)) + ((M : ℕ) : ZMod (2 * M)) = 0 := by
  have h : ((M : ℕ) : ZMod (2 * M)) + ((M : ℕ) : ZMod (2 * M))
      = ((2 * M : ℕ) : ZMod (2 * M)) := by push_cast; ring
  rw [h, ZMod.natCast_self]

/-- **The cancelling triple is absurd.**  Three size-`n` multisets whose
multiplicities sum to `3` at every coordinate cannot all miss the target by
the sheet. -/
theorem three_cancel_absurd {n M : ℕ} (hM : 1 ≤ M)
    (g : Fin n → ZMod (2 * M)) (k₁ k₂ k₃ : Fin n → ℕ)
    (hsum : ∀ j, k₁ j + k₂ j + k₃ j = 3)
    (h₁ : ∑ j, k₁ j • g j = ∑ j, g j + ((M : ℕ) : ZMod (2 * M)))
    (h₂ : ∑ j, k₂ j • g j = ∑ j, g j + ((M : ℕ) : ZMod (2 * M)))
    (h₃ : ∑ j, k₃ j • g j = ∑ j, g j + ((M : ℕ) : ZMod (2 * M))) : False := by
  classical
  -- expand the coordinatewise sum two ways
  have hR : ∑ j, (k₁ j + k₂ j + k₃ j) • g j
      = (∑ j, k₁ j • g j) + (∑ j, k₂ j • g j) + (∑ j, k₃ j • g j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_smul, add_smul])
  have hL : ∑ j, (k₁ j + k₂ j + k₃ j) • g j
      = (∑ j, g j) + (∑ j, g j) + (∑ j, g j) := by
    have hpt : ∀ j : Fin n, (k₁ j + k₂ j + k₃ j) • g j = g j + g j + g j := by
      intro j
      rw [hsum j]
      show (3 : ℕ) • g j = _
      rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, add_smul, add_smul, one_smul]
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hL, h₁, h₂, h₃] at hR
  -- cancel `3 • ∑ g`, leaving `3M = 0`
  have hthree : ((M : ℕ) : ZMod (2 * M)) + ((M : ℕ) : ZMod (2 * M))
      + ((M : ℕ) : ZMod (2 * M)) = 0 := by
    have hcancel : (∑ j, g j) + (∑ j, g j) + (∑ j, g j)
        + (((M : ℕ) : ZMod (2 * M)) + ((M : ℕ) : ZMod (2 * M))
          + ((M : ℕ) : ZMod (2 * M)))
        = (∑ j, g j) + (∑ j, g j) + (∑ j, g j) + 0 := by
      rw [add_zero]
      conv_rhs => rw [hR]
      ring
    exact add_left_cancel hcancel
  rw [sheet_add_self, zero_add] at hthree
  exact sheet_ne_zero hM hthree

/-- The kernel of `ZMod (2M) → ZMod M` is `{0, M}`. -/
theorem kernel_two_mul {M : ℕ} (hM : 1 ≤ M) (x : ZMod (2 * M))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x = 0) :
    x = 0 ∨ x = ((M : ℕ) : ZMod (2 * M)) := by
  haveI : NeZero (2 * M) := ⟨by omega⟩
  haveI : NeZero M := ⟨by omega⟩
  have hval : ((x.val : ℕ) : ZMod (2 * M)) = x := ZMod.natCast_rightInverse x
  have hred : ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((x.val : ℕ) : ZMod (2 * M))
      = ((x.val : ℕ) : ZMod M) := map_natCast _ _
  rw [hval, hx] at hred
  have hdvd : M ∣ x.val := (ZMod.natCast_eq_zero_iff _ _).mp hred.symm
  obtain ⟨c, hc⟩ := hdvd
  have hlt : x.val < 2 * M := ZMod.val_lt x
  have hc2 : c < 2 := by
    by_contra hcon
    have h2 : M * 2 ≤ M * c := Nat.mul_le_mul_left _ (Nat.not_lt.mp hcon)
    omega
  interval_cases c
  · left; rw [← hval, hc]; simp
  · right; rw [← hval, hc, mul_one]

/-- A nontrivial multiset matching the target modulo `M` misses it by
exactly the sheet, because validity rules out the other kernel element. -/
theorem sheet_gap_of_valid {n M : ℕ} (hM : 1 ≤ M) {g : Fin n → ZMod (2 * M)}
    (hg : ValidTuple g) {k : Fin n → ℕ} (hcard : ∑ j, k j = n)
    (hne : ∃ j, k j ≠ 1)
    (hmod : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((∑ j, k j • g j) - ∑ j, g j) = 0) :
    ∑ j, k j • g j = ∑ j, g j + ((M : ℕ) : ZMod (2 * M)) := by
  rcases kernel_two_mul hM _ hmod with h | h
  · exfalso
    obtain ⟨j, hj⟩ := hne
    exact hj (hg k hcard (sub_eq_zero.mp h) j)
  · exact sub_eq_iff_eq_add'.mp h

/-- **No cancelling triple.**  A valid tuple at the first even stratum admits
no three nontrivial size-`n` multisets that all match the target modulo `M`
and whose multiplicities sum to `3` at every coordinate.

This is the exact mechanism behind the stratum-one exclusion: the three
multisets each miss by the sheet, so the sheet is tripled to zero, which it
is not. -/
theorem no_cancelling_triple {n M : ℕ} (hM : 1 ≤ M) {g : Fin n → ZMod (2 * M)}
    (hg : ValidTuple g) (k₁ k₂ k₃ : Fin n → ℕ)
    (hc₁ : ∑ j, k₁ j = n) (hc₂ : ∑ j, k₂ j = n) (hc₃ : ∑ j, k₃ j = n)
    (hn₁ : ∃ j, k₁ j ≠ 1) (hn₂ : ∃ j, k₂ j ≠ 1) (hn₃ : ∃ j, k₃ j ≠ 1)
    (hm₁ : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((∑ j, k₁ j • g j) - ∑ j, g j) = 0)
    (hm₂ : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((∑ j, k₂ j • g j) - ∑ j, g j) = 0)
    (hm₃ : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((∑ j, k₃ j • g j) - ∑ j, g j) = 0)
    (hsum : ∀ j, k₁ j + k₂ j + k₃ j = 3) : False :=
  three_cancel_absurd hM g k₁ k₂ k₃ hsum
    (sheet_gap_of_valid hM hg hc₁ hn₁ hm₁)
    (sheet_gap_of_valid hM hg hc₂ hn₂ hm₂)
    (sheet_gap_of_valid hM hg hc₃ hn₃ hm₃)

end StratumOne

end MinModulus
