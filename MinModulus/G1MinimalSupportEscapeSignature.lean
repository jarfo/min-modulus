/-
# Uniform coefficient signatures inside concentrated escape fibers

At a non-anchor exact omission of the protected quarter witness, an escape
coefficient of a tail-light private witness is forced to be either zero or
one.  Splitting a concentrated omission fiber by these two values retains at
least half of that fiber.  Combined with the anchor/omission concentration,
this gives a dimension-uniform anchor-or-signature alternative.
-/
import MinModulus.G1MinimalSupportEscapeFiber

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- At a non-anchor exact omission, every private witness assigned to that
escape coordinate has coefficient exactly zero or one. -/
theorem minimalSupportPrivateEscapeCoefficient_eq_zero_or_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q B : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0)
    (b : {b : Fin (m + 1) // b ∈ B})
    (hb : b ∈ minimalSupportPrivateEscapeFiber
      g hg ht hq B hmin hqzero z) :
    minimalSupportPrivateWitness g h hmin b z = 0 ∨
      minimalSupportPrivateWitness g h hmin b z = 1 := by
  have hzneg : q z = -1 := (hQ z).2 hzQ
  have hselected := minimalSupportPrivateEscapeCoordinate_mem
    g hg ht hq hmin hqzero b
  have hbcoord := (mem_minimalSupportPrivateEscapeFiber_iff
    g hg ht hq B hmin hqzero z b).1 hb
  have hfloor := (mem_minimalSupportPrivateEscapePairs_iff
    g h q hmin b
      (minimalSupportPrivateEscapeCoordinate
        g hg ht hq hmin hqzero b)).1 hselected
  rw [hbcoord, hzneg] at hfloor
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hz0
  have hceil := hallLight
    (minimalSupportPrivateWitness g h hmin b)
    (minimalSupportPrivateWitness_isWitness g h hmin b) j
  omega

/-- The subfiber on which the private witness has a fixed coefficient at the
selected escape coordinate. -/
noncomputable def minimalSupportPrivateEscapeSignatureFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (z : Fin (m + 1)) (ε : ℤ) :
    Finset {b : Fin (m + 1) // b ∈ B} := by
  classical
  exact (minimalSupportPrivateEscapeFiber
    g hg ht hq B hmin hqzero z).filter (fun b ↦
      minimalSupportPrivateWitness g h hmin b z = ε)

@[simp] theorem mem_minimalSupportPrivateEscapeSignatureFiber_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (z : Fin (m + 1)) (ε : ℤ)
    (b : {b : Fin (m + 1) // b ∈ B}) :
    b ∈ minimalSupportPrivateEscapeSignatureFiber
        g hg ht hq B hmin hqzero z ε ↔
      minimalSupportPrivateEscapeCoordinate
          g hg ht hq hmin hqzero b = z ∧
        minimalSupportPrivateWitness g h hmin b z = ε := by
  classical
  simp [minimalSupportPrivateEscapeSignatureFiber]

/-- Splitting a non-anchor omission escape fiber by coefficients zero and one
retains at least half of the fiber in one signature class. -/
theorem exists_large_minimalSupportPrivateEscapeSignatureFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (z : Fin (m + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0) :
    ∃ ε ∈ ({0, 1} : Finset ℤ),
      (minimalSupportPrivateEscapeFiber
        g hg ht hq B hmin hqzero z).card / 2 ≤
      (minimalSupportPrivateEscapeSignatureFiber
        g hg ht hq B hmin hqzero z ε).card := by
  classical
  let S : Finset {b : Fin (m + 1) // b ∈ B} :=
    minimalSupportPrivateEscapeFiber g hg ht hq B hmin hqzero z
  let T : Finset ℤ := {0, 1}
  let f : {b : Fin (m + 1) // b ∈ B} → ℤ := fun b ↦
    minimalSupportPrivateWitness g h hmin b z
  have hmap : ∀ b ∈ S, f b ∈ T := by
    intro b hb
    have hcoeff := minimalSupportPrivateEscapeCoefficient_eq_zero_or_one
      g hg ht hq hQ hmin hqzero hallLight z hzQ hz0 b hb
    simpa [T, f] using hcoeff
  have hTnonempty : T.Nonempty := ⟨0, by simp [T]⟩
  have hTcard : T.card = 2 := by norm_num [T]
  have hn : T.card * (S.card / 2) ≤ S.card := by
    rw [hTcard]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self S.card 2
  obtain ⟨ε, hεT, hεcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := S) (t := T) (f := f) hmap hTnonempty hn
  refine ⟨ε, ?_, ?_⟩
  · simpa [T] using hεT
  · simpa [minimalSupportPrivateEscapeSignatureFiber, S, f] using hεcard

/-- Dimension-uniform residual alternative: either at least one third of all
private layers escape at the anchor, or at least half of such a one-third
class shares one non-anchor omission and one coefficient in `{0,1}`. -/
theorem large_anchor_or_omission_signatureFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} {q : Fin (m + 1) → ℤ}
    (ht : t + t = h) (hq : Witness g t q)
    {Q : Finset (Fin (m + 1))} (hQ : ExactOmissions q Q)
    (hQcard : Q.card ≤ 2)
    (B : Finset (Fin (m + 1)))
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (hallLight : AllHalfWitnessesTailLight g h) :
    B.card / 3 ≤
        (minimalSupportPrivateEscapeFiber
          g hg ht hq B hmin hqzero 0).card ∨
      ∃ z ∈ Q, z ≠ 0 ∧ ∃ ε ∈ ({0, 1} : Finset ℤ),
        (B.card / 3) / 2 ≤
          (minimalSupportPrivateEscapeSignatureFiber
            g hg ht hq B hmin hqzero z ε).card := by
  obtain ⟨z, hz, hzlarge⟩ :=
    exists_large_minimalSupportPrivateEscapeFiber
      g hg ht hq hQ hQcard B hmin hqzero hallLight
  by_cases hz0 : z = 0
  · subst z
    exact Or.inl hzlarge
  · right
    have hzQ : z ∈ Q := by
      rcases Finset.mem_insert.mp hz with hz' | hz'
      · exact False.elim (hz0 hz')
      · exact hz'
    obtain ⟨ε, hε, hεlarge⟩ :=
      exists_large_minimalSupportPrivateEscapeSignatureFiber
        g hg ht hq hQ B hmin hqzero hallLight z hzQ hz0
    refine ⟨z, hzQ, hz0, ε, hε, ?_⟩
    omega

end MinModulus
