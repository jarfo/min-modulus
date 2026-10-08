import MinModulus.RLiftSmallK2
import MinModulus.RLiftSmallK4
import MinModulus.RLiftSmallK6

/-!
# Small-k assembly and the all-even-size exclusion
-/

namespace MinModulus

/-- **The full R-lift extra exclusion**: for every even `L ≥ 2`, every
extra `e`, and every sheeted lift, the parent of the reflected child is
invalid modulo `4M`. -/
theorem rliftParentE_not_valid_even (L e : ℕ) (hL2 : 2 ≤ L) (hLe : Even L)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) :
        ZMod (2 ^ (L + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  have hc : L = 2 ∨ L = 4 ∨ L = 6 ∨ 8 ≤ L := by
    obtain ⟨c, hc⟩ := hLe
    omega
  rcases hc with h | h | h | h
  · subst h; exact rliftSmallK2_not_valid_all e hβ hg
  · subst h; exact rliftSmallK4_not_valid_all e hβ hg
  · subst h; exact rliftSmallK6_not_valid_all e hβ hg
  · obtain ⟨w, rfl⟩ : ∃ w, L = w + 6 := ⟨L - 6, by omega⟩
    have hwe : Even w := by
      obtain ⟨c, hc⟩ := hLe
      exact ⟨c - 3, by omega⟩
    exact rliftParentE_not_valid_all w e (by omega) hwe hβ hg

end MinModulus
