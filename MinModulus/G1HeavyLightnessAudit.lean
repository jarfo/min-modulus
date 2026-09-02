/-
# Lightness audit for the genuine-heavy frontier

The genuine-heavy escape package contains a half witness with a tail
coefficient at least two.  It is therefore disjoint from the global
all-tail-light branch.  Recording this explicitly prevents local theorems
proved under `AllHalfWitnessesTailLight` from being composed vacuously with
the genuine-heavy roadmap.
-/
import MinModulus.G1ProfileSingletonDescent

namespace MinModulus

/-- A genuine-heavy two-step escape is incompatible with global tail
lightness, by its displayed heavy source witness. -/
theorem CriticalGenuineHeavyTwoStepEscape.not_allHalfWitnessesTailLight
    {n s q : ℕ}
    {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ¬ AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
  rintro hallLight
  obtain ⟨c, hc, ⟨k, hk⟩, _hno, _hescape⟩ := hescape
  have hle := hallLight c hc k
  omega

end MinModulus
