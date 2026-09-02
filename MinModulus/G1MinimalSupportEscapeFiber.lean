/-
# Concentrated escape fibers for bounded minimal support deletion

Choose one coefficient-floor escape for every private witness of a minimal
support transversal.  In the all-tail-light branch, exact omissions of the
protected quarter witness force every chosen coordinate into the anchor plus
the quarter omission set.  For a balanced pair this target set has at most
three elements, so one fiber contains at least one third of the private
layers.
-/
import MinModulus.G1MinimalSupportCriticalCrossing
import Mathlib.Combinatorics.Pigeonhole

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A canonically selected coefficient-floor escape for the private witness
at `b`. -/
noncomputable def minimalSupportPrivateEscapeCoordinate
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (b : {b : Fin (m + 1) // b ∈ B}) : Fin (m + 1) :=
  Classical.choose
    (exists_minimalSupportPrivateEscape
      g hg ht hq hmin hqzero b)

/-- The selected coordinate really is an escape incidence. -/
theorem minimalSupportPrivateEscapeCoordinate_mem
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    (b, minimalSupportPrivateEscapeCoordinate
      g hg ht hq hmin hqzero b) ∈
        minimalSupportPrivateEscapePairs g h q hmin :=
  Classical.choose_spec
    (exists_minimalSupportPrivateEscape
      g hg ht hq hmin hqzero b)

/-- In the all-tail-light branch, a selected escape lies at the anchor or in
the exact omission set of the protected quarter vector. -/
theorem minimalSupportPrivateEscapeCoordinate_mem_anchor_insert_omissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    minimalSupportPrivateEscapeCoordinate
        g hg ht hq hmin hqzero b ∈ insert 0 Q := by
  have hloc := minimalSupportPrivateEscape_eq_anchor_or_mem_exactOmissions
    g hq hQ hmin hallLight b
      (minimalSupportPrivateEscapeCoordinate g hg ht hq hmin hqzero b)
      (minimalSupportPrivateEscapeCoordinate_mem
        g hg ht hq hmin hqzero b)
  simpa using hloc

/-- The fiber of private transversal coordinates assigned to one selected
escape coordinate. -/
noncomputable def minimalSupportPrivateEscapeFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (z : Fin (m + 1)) : Finset {b : Fin (m + 1) // b ∈ B} := by
  classical
  exact B.attach.filter (fun b ↦
    minimalSupportPrivateEscapeCoordinate
      g hg ht hq hmin hqzero b = z)

@[simp] theorem mem_minimalSupportPrivateEscapeFiber_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (z : Fin (m + 1)) (b : {b : Fin (m + 1) // b ∈ B}) :
    b ∈ minimalSupportPrivateEscapeFiber
        g hg ht hq B hmin hqzero z ↔
      minimalSupportPrivateEscapeCoordinate
        g hg ht hq hmin hqzero b = z := by
  classical
  simp [minimalSupportPrivateEscapeFiber]

/-- If the quarter omission set has cardinality at most two, one anchor-or-
omission coordinate carries at least one third (rounded down) of all private
layers. -/
theorem exists_large_minimalSupportPrivateEscapeFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hQcard : Q.card ≤ 2)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h) :
    ∃ z ∈ insert 0 Q,
      B.card / 3 ≤
        (minimalSupportPrivateEscapeFiber
          g hg ht hq B hmin hqzero z).card := by
  classical
  let S : Finset {b : Fin (m + 1) // b ∈ B} := B.attach
  let T : Finset (Fin (m + 1)) := insert 0 Q
  let f : {b : Fin (m + 1) // b ∈ B} → Fin (m + 1) :=
    minimalSupportPrivateEscapeCoordinate g hg ht hq hmin hqzero
  have hmap : ∀ b ∈ S, f b ∈ T := by
    intro b _hb
    exact minimalSupportPrivateEscapeCoordinate_mem_anchor_insert_omissions
      g hg ht hq hQ hmin hqzero hallLight b
  have hTnonempty : T.Nonempty := ⟨0, by simp [T]⟩
  have hTcard : T.card ≤ 3 := by
    have hins : T.card ≤ Q.card + 1 := by
      simpa [T, Nat.add_comm] using Finset.card_insert_le 0 Q
    omega
  have hfloor : 3 * (B.card / 3) ≤ B.card := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self B.card 3
  have hn : T.card * (B.card / 3) ≤ S.card := by
    have hmul := Nat.mul_le_mul_right (B.card / 3) hTcard
    have : T.card * (B.card / 3) ≤ B.card := hmul.trans hfloor
    simpa [S] using this
  obtain ⟨z, hzT, hzcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := S) (t := T) (f := f) hmap hTnonempty hn
  refine ⟨z, hzT, ?_⟩
  simpa [minimalSupportPrivateEscapeFiber, S, f] using hzcard

end MinModulus
