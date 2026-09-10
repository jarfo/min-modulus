import MinModulus.G3QuantitativeEscape
import MinModulus.SILiftSmallBases

namespace MinModulus

/-- The quantitative exceptional obstruction after discharging the sole
non-power-of-two dimension below five. -/
def LargeExceptionalQuantitativeEscapeObstruction : Prop :=
  ∀ n : ℕ, 5 ≤ n → 2 ^ Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2 * globalBound (n - 1)), ValidTuple g →
      (∀ (b : ZMod (2 * globalBound (n - 1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j = 2 • g i + b)).card = r →
        2 ^ ((n + r) / (r + 1) - 3) < (n + r).choose (r + 1) ∧
          n < (r + 1) ^ 2 * (Nat.log 2 n + 1) + 3 * (r + 1)) →
      False

/-- The known three-coordinate base removes the conditional small-dimension
premise from the quantitative G3 frontier without adding an assumption. -/
theorem exceptionalQuantitativeEscapeObstruction_iff_large :
    ExceptionalQuantitativeEscapeObstruction ↔
      LargeExceptionalQuantitativeEscapeObstruction := by
  constructor
  · intro h n hn hnpow g hg hquant
    exact h n (by omega) hnpow g hg (fun _ ↦ hquant)
  · intro h n hn hnpow g hg hquant
    by_cases hn5 : 5 ≤ n
    · exact h n hn5 hnpow g hg (hquant (by omega))
    · have hn3 : n = 3 := by
        interval_cases n <;> norm_num at *
      subst n
      exact not_validTuple_three_mod_four g hg

end MinModulus

