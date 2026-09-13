import research.QuadraticEscapeCounts
import MinModulus.CollisionEscapeThreshold

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- In a hypothetical odd counterexample, the number of quadratic escapes
at every outside shift obeys the existing quadratic-logarithmic constraint
for affine escapes. The count therefore cannot stay bounded as n grows. -/
theorem quadratic_escapes_quadratic_log_of_odd_counterexample
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1)
    (t : ZMod N) (ht : ∀ i, t ≠ g i) :
    let r := n-(quadraticTranslateHits g t).card
    n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  classical
  let r := n-(quadraticTranslateHits g t).card
  change n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1)
  by_cases hfour : 4 ≤ (quadraticTranslateHits g t).card
  · have heq := quadratic_hit_card_eq_affine_hit_card_of_four_hits hN g hg t ht hfour
    have htotal := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun j ↦ ∃ i, g i=2 • g j-t)
    simp only [Finset.card_univ,Fintype.card_fin] at htotal
    have hcount : (Finset.univ.filter (fun j ↦ ¬ ∃ i, g i=2 • g j+(-t))).card=r := by
      simp only [← sub_eq_add_neg]
      dsimp [r]
      omega
    have hquant := quantitative_escapes_of_stratum_counterexample_with_collision
      (n := n) (s := 0) (q := N) hN hn
    rw [show (2 : ℕ)^0*N=N by simp] at hquant
    have hcrit : N < stratumBound n 0 := by simpa [stratumBound] using hsmall
    exact (hquant g hg hcrit (-t) r hcount).2
  · have hlinear : n < 3*(r+1) := by dsimp [r]; omega
    omega

end MinModulus.Research
