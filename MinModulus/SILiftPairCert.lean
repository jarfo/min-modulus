import MinModulus.SILiftRival

/-!
# Sheet-free exclusion certificates

To exclude every lift of a child class one would naively have to run over
all `2 ^ (m+1)` sheet patterns.  That is unnecessary.

A rival `κ` avoiding the extra forces

    e = (∑ κ i • A i - ∑ A i) + τ • sheet,   τ = ∑ κ i * b i - ∑ b i,

and `τ` depends on `b` only through its PARITY.  So if two rivals `κ`,
`κ'` have the same multiplicity parities — `κ i ≡ κ' i (mod 2)` for every
`i` — they share the same `τ`, whatever `b` is.  If in addition their
values differ by exactly the sheet, the two extras they exclude are

    {ρ + τ·sheet, ρ + sheet + τ·sheet} = {ρ, ρ + sheet},

both lifts of `ρ`, in either case for `τ`.  The sheet pattern has dropped
out completely: ONE pair of rivals excludes BOTH lifts of one child
residue, for every `b` at once.
-/

namespace MinModulus

open Finset

section PairCert

variable {m t : ℕ}

/-- A coin family on the block, with the right total and the rival
equation, refutes validity.  The extended family is zero at the extra
coordinate, so it differs from the all-ones family automatically. -/
theorem siLiftParent_not_valid_of_rival
    (A : Fin (m + 1) → ZMod (siFull m t)) (b : ℕ → ℕ)
    (e : ZMod (siFull m t)) (κ₀ : Fin (m + 1) → ℕ)
    (hsum : ∑ i : Fin (m + 1), κ₀ i = m + 2)
    (heq : (∑ i : Fin (m + 1), κ₀ i • A i)
        + (∑ i : Fin (m + 1), κ₀ i * b i.val) • siSheet m t
      = (∑ i : Fin (m + 1), A i)
        + (∑ i : Fin (m + 1), b i.val) • siSheet m t + e) :
    ¬ ValidTuple (siLiftParent m t A b e) := by
  intro hv
  classical
  set κ : Fin (m + 2) → ℕ := Fin.lastCases 0 κ₀ with hκdef
  have hlast : κ (Fin.last (m + 1)) = 0 := by simp [hκdef]
  have hcast : ∀ i : Fin (m + 1), κ i.castSucc = κ₀ i := by
    intro i; simp [hκdef]
  have hs : ∑ i, κ i = m + 2 := by
    rw [Fin.sum_univ_castSucc, hlast, add_zero,
      Finset.sum_congr rfl (fun i _ => hcast i)]
    exact hsum
  have hval : ∑ i, κ i • siLiftParent m t A b e i
      = ∑ i, siLiftParent m t A b e i := by
    rw [siLiftParent_rival_iff A b e κ hlast]
    simp only [hcast]
    exact heq
  have h1 := hv κ hs hval (Fin.last (m + 1))
  rw [hlast] at h1
  exact absurd h1 (by norm_num)

/-- Multiplying the sheet by naturals of opposite parity differs by the
sheet. -/
lemma nsmul_siSheet_flip (hmt : t ≤ m) {x y : ℕ} (h : x % 2 ≠ y % 2) :
    x • siSheet m t = y • siSheet m t + siSheet m t := by
  rw [nsmul_siSheet hmt x, nsmul_siSheet hmt y]
  by_cases hx : x % 2 = 0
  · rw [hx, show y % 2 = 1 from by omega, zero_smul, one_smul,
      siSheet_add_self hmt]
  · rw [show x % 2 = 1 from by omega, show y % 2 = 0 from by omega,
      zero_smul, one_smul, zero_add]

/-- **The pair certificate.**  Two rivals with matching multiplicity
parities whose values differ by the sheet exclude BOTH lifts of their
common residue — for every sheet pattern at once, since the pattern enters
only through a parity the two rivals share. -/
theorem pair_cert_not_valid (hmt : t ≤ m)
    (A : Fin (m + 1) → ZMod (siFull m t)) (b : ℕ → ℕ)
    (e V : ZMod (siFull m t)) (κ κ' : Fin (m + 1) → ℕ)
    (hsum : ∑ i : Fin (m + 1), κ i = m + 2)
    (hsum' : ∑ i : Fin (m + 1), κ' i = m + 2)
    (hpar : ∀ i : Fin (m + 1), κ i % 2 = κ' i % 2)
    (hV : (∑ i : Fin (m + 1), κ i • A i)
      = (∑ i : Fin (m + 1), A i) + V)
    (hV' : (∑ i : Fin (m + 1), κ' i • A i)
      = (∑ i : Fin (m + 1), A i) + V + siSheet m t)
    (he : e = V ∨ e = V + siSheet m t) :
    ¬ ValidTuple (siLiftParent m t A b e) := by
  -- the two rivals share the sheet parity
  have hss : (∑ i : Fin (m + 1), κ i * b i.val) % 2
      = (∑ i : Fin (m + 1), κ' i * b i.val) % 2 := by
    have h : ∀ i : Fin (m + 1),
        (κ i * b i.val) % 2 = (κ' i * b i.val) % 2 := by
      intro i; rw [Nat.mul_mod, Nat.mul_mod (κ' i), hpar i]
    calc (∑ i : Fin (m + 1), κ i * b i.val) % 2
        = (∑ i : Fin (m + 1), (κ i * b i.val) % 2) % 2 :=
          Finset.sum_nat_mod _ _ _
      _ = (∑ i : Fin (m + 1), (κ' i * b i.val) % 2) % 2 :=
          congrArg (· % 2) (Finset.sum_congr rfl fun i _ => h i)
      _ = (∑ i : Fin (m + 1), κ' i * b i.val) % 2 :=
          (Finset.sum_nat_mod _ _ _).symm
  by_cases hτ : (∑ i : Fin (m + 1), κ i * b i.val) % 2
      = (∑ i : Fin (m + 1), b i.val) % 2
  · -- the rivals hit `V` and `V + sheet` in that order
    have hτ' : (∑ i : Fin (m + 1), κ' i * b i.val) % 2
        = (∑ i : Fin (m + 1), b i.val) % 2 := by rw [← hss]; exact hτ
    rcases he with h | h
    · rw [h]
      refine siLiftParent_not_valid_of_rival A b V κ hsum ?_
      rw [hV, nsmul_siSheet_congr hmt hτ]
      abel
    · rw [h]
      refine siLiftParent_not_valid_of_rival A b _ κ' hsum' ?_
      rw [hV', nsmul_siSheet_congr hmt hτ']
      abel
  · -- the sheet parity is flipped, so they hit them the other way round
    have hfl : (∑ i : Fin (m + 1), κ i * b i.val) • siSheet m t
        = (∑ i : Fin (m + 1), b i.val) • siSheet m t + siSheet m t :=
      nsmul_siSheet_flip hmt hτ
    have hfl' : (∑ i : Fin (m + 1), κ' i * b i.val) • siSheet m t
        = (∑ i : Fin (m + 1), b i.val) • siSheet m t + siSheet m t :=
      nsmul_siSheet_flip hmt (by rw [← hss]; exact hτ)
    have h2 := siSheet_add_self (m := m) (t := t) hmt
    rcases he with h | h
    · rw [h]
      refine siLiftParent_not_valid_of_rival A b V κ' hsum' ?_
      rw [hV', hfl']
      calc (∑ i : Fin (m + 1), A i) + V + siSheet m t
              + ((∑ i : Fin (m + 1), b i.val) • siSheet m t + siSheet m t)
          = (∑ i : Fin (m + 1), A i)
              + (∑ i : Fin (m + 1), b i.val) • siSheet m t + V
              + (siSheet m t + siSheet m t) := by abel
        _ = (∑ i : Fin (m + 1), A i)
              + (∑ i : Fin (m + 1), b i.val) • siSheet m t + V := by
            rw [h2, add_zero]
    · rw [h]
      refine siLiftParent_not_valid_of_rival A b _ κ hsum ?_
      rw [hV, hfl]
      abel

end PairCert

end MinModulus
