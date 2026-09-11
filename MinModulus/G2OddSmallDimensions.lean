import MinModulus.OddSmallCertificate

/-!
# G2 below dimension six

Every odd modulus admitting a valid `n`-tuple with `n ≤ 5` is at least
`2^n - 1`.  Dimensions at most two follow from the abelian bound and parity.
For `n = 3, 4, 5` the abelian bound leaves finitely many odd moduli below
`2^n - 1`; each is excluded by a kernel-checked rival certificate after the
proved normalizations.  Consequently the odd-stratum input `OddStratumLowerBound`
is equivalent to its restriction `OddStratumLowerBoundFrom 6` to dimensions at
least six.  No new assumption is introduced; G2 itself remains open.
-/

namespace MinModulus
open Finset OddSmallCertificate

/-- No valid three-tuple exists modulo an odd number below `2^3 - 1`. -/
theorem not_validTuple_three_of_odd_lt_seven {N : ℕ} (hN : Odd N) (hlt : N < 7)
    (g : Fin 3 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have hb : 4 ≤ N := by simpa only [ZMod.card, Nat.reducePow] using card_ge g hg
  have hcase : N = 5 := by
    rcases hN with ⟨k, rfl⟩
    omega
  subst hcase
  exact not_validTuple_three_of_certificate certificate_three g hg

/-- No valid four-tuple exists modulo an odd number below `2^4 - 1`. -/
theorem not_validTuple_four_of_odd_lt_fifteen {N : ℕ} (hN : Odd N) (hlt : N < 15)
    (g : Fin 4 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have hb : 8 ≤ N := by simpa only [ZMod.card, Nat.reducePow] using card_ge g hg
  have hcases : N = 9 ∨ N = 11 ∨ N = 13 := by
    rcases hN with ⟨k, rfl⟩
    omega
  rcases hcases with rfl | rfl | rfl
  · exact not_validTuple_four_of_certificate certificate_four_nine g hg
  · exact not_validTuple_four_of_certificate certificate_four_eleven g hg
  · exact not_validTuple_four_of_certificate certificate_four_thirteen g hg

/-- No valid five-tuple exists modulo an odd number below `2^5 - 1`. -/
theorem not_validTuple_five_of_odd_lt_thirty_one {N : ℕ} (hN : Odd N) (hlt : N < 31)
    (g : Fin 5 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have hb : 16 ≤ N := by simpa only [ZMod.card, Nat.reducePow] using card_ge g hg
  have hcases : N = 17 ∨ N = 19 ∨ N = 21 ∨ N = 23 ∨ N = 25 ∨ N = 27 ∨ N = 29 := by
    rcases hN with ⟨k, rfl⟩
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_seventeen.1 certificate_five_seventeen.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_nineteen.1 certificate_five_nineteen.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_twenty_one.1 certificate_five_twenty_one.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_twenty_three.1 certificate_five_twenty_three.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_twenty_five.1 certificate_five_twenty_five.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_twenty_seven.1 certificate_five_twenty_seven.2 g hg
  · exact not_validTuple_five_of_certificates (by decide)
      certificate_five_twenty_nine.1 certificate_five_twenty_nine.2 g hg

/-- The odd-stratum obligation above an explicit dimension cutoff. -/
def OddStratumLowerBoundFrom (k : ℕ) : Prop :=
  ∀ {n N : ℕ}, k ≤ n → Odd N → AdmitsValidTuple n N → 2 ^ n - 1 ≤ N

/-- The odd-stratum input is equivalent to its restriction to dimensions at
least six: every smaller dimension is proved unconditionally. -/
theorem oddStratumLowerBound_iff_from_six :
    OddStratumLowerBound ↔ OddStratumLowerBoundFrom 6 := by
  constructor
  · intro h n N _ hN hv
    exact h hN hv
  · intro h n N hN hv
    by_cases hn : 6 ≤ n
    · exact h hn hN hv
    · obtain ⟨g, hg⟩ := hv
      haveI : NeZero N := ⟨hN.pos.ne'⟩
      by_contra hlt
      push_neg at hlt
      have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at hlt
      · have hpos := hN.pos
        simp at hlt
        omega
      · have hb : 2 ≤ N := by simpa only [ZMod.card, Nat.reducePow] using card_ge g hg
        rcases hN with ⟨k, rfl⟩
        omega
      · exact not_validTuple_three_of_odd_lt_seven hN hlt g hg
      · exact not_validTuple_four_of_odd_lt_fifteen hN hlt g hg
      · exact not_validTuple_five_of_odd_lt_thirty_one hN hlt g hg

end MinModulus
