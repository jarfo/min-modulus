import research.QuadraticOneEscapeTransfer
import MinModulus.AlmostDoubling

set_option autoImplicit false
namespace MinModulus.Research

/-- The existing generic one-escape theorem strengthens quadratic containment:
n-1 hits already imply the sharp odd modulus bound. -/
theorem odd_lower_bound_of_almost_full_quadratic_translate {n N : ℕ} [NeZero N]
    (hn : 5 ≤ n) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : ∀ i, t ≠ g i)
    (hlarge : n-1 ≤ (quadraticTranslateHits g t).card) : 2^n-1 ≤ N := by
  obtain ⟨a,ha⟩ := one_escape_of_large_quadratic_translate hn g hg t ht hlarge
  exact odd_lower_bound_of_valid_one_escape_doubling hN g hg a (-t)
    (by simpa only [sub_eq_add_neg] using ha)

/-- Every hypothetical odd counterexample has two distinct escapes from
every outside quadratic translate. -/
theorem two_quadratic_escapes_of_odd_counterexample {n N : ℕ} [NeZero N]
    (hn : 5 ≤ n) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2^n-1) (t : ZMod N) (ht : ∀ i, t ≠ g i) :
    ∃ i j : Fin n, i ≠ j ∧ g i+t ∉ actualFibreCoinCover g 2 ∧
      g j+t ∉ actualFibreCoinCover g 2 := by
  apply two_quadratic_escapes_of_one_escape_exclusion hn g hg t ht
  intro a ha
  have hb := odd_lower_bound_of_valid_one_escape_doubling hN g hg a (-t)
    (by simpa only [sub_eq_add_neg] using ha)
  omega

end MinModulus.Research
