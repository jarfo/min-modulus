/-
# Local light/heavy split inside a shared-omission vertex fiber

The large vertex fiber obtained from common-omission counting need not be
globally tail-light.  Split only the canonical private witnesses in that
fiber.  Failure exposes another explicit tail-heavy private witness.  In the
light arm, the fiber injects into canonical reduced collisions, and every
collision retains the shared non-anchor coordinate on one of its two sides.
-/
import MinModulus.G1PrivateHeavyTransversalOmissionVertexFibers

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Tail-lightness restricted to private witnesses in one omission vertex
fiber. -/
def MinimalSupportPrivateOmissionVerticesTailLight
    (g : Fin (n + 1) → G) (h : G)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1)) : Prop :=
  ∀ b : ↥B, b ∈ minimalSupportPrivateOmissionVertices g hmin z →
    ∀ k : Fin n, minimalSupportPrivateWitness g h hmin b k.succ ≤ 1

omit [DecidableEq G] in
/-- The exact local split: either all private witnesses sharing `z` are
tail-light, or one member of that same fiber is explicitly tail-heavy. -/
theorem minimalSupportPrivateOmissionVertices_tailLight_or_exists_tailHeavy
    (g : Fin (n + 1) → G) (h : G)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1)) :
    MinimalSupportPrivateOmissionVerticesTailLight g h hmin z ∨
      ∃ b : ↥B,
        b ∈ minimalSupportPrivateOmissionVertices g hmin z ∧
        ∃ k : Fin n,
          2 ≤ minimalSupportPrivateWitness g h hmin b k.succ := by
  by_cases hlight :
      MinimalSupportPrivateOmissionVerticesTailLight g h hmin z
  · exact Or.inl hlight
  · right
    unfold MinimalSupportPrivateOmissionVerticesTailLight at hlight
    push Not at hlight
    obtain ⟨b, hb, k, hk⟩ := hlight
    exact ⟨b, hb, k, by omega⟩

/-- The reduced collision encoded by one locally tail-light private witness
in the shared-omission fiber. -/
noncomputable def minimalSupportPrivateOmissionReducedCollision
    (g : Fin (n + 1) → G) (h : G)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    ReducedSubsetSumCollision g h :=
  reducedCollisionOfTailLightWitness g
    (minimalSupportPrivateWitness_isWitness g h hmin b.val)
    (hlight b.val b.property)

omit [DecidableEq G] in
theorem minimalSupportPrivateOmissionReducedCollision_coeffs
    (g : Fin (n + 1) → G) (h : G)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    subsetCollisionCoeffs
        (minimalSupportPrivateOmissionReducedCollision
          g h hmin z hlight b).val.1
        (minimalSupportPrivateOmissionReducedCollision
          g h hmin z hlight b).val.2 =
      minimalSupportPrivateWitness g h hmin b.val :=
  reducedCollisionOfTailLightWitness_coeffs g
    (minimalSupportPrivateWitness_isWitness g h hmin b.val)
    (hlight b.val b.property)

/-- Canonical orientation of one locally light member of the omission
vertex fiber. -/
noncomputable def minimalSupportPrivateOmissionCanonicalCollision
    (g : Fin (n + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (minimalSupportPrivateOmissionReducedCollision
      g h hmin z hlight b)

theorem minimalSupportPrivateOmissionCanonicalCollision_isCanonical
    (g : Fin (n + 1) → G) (h : G) (hh : h + h = 0) (hh0 : h ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin z)) :
    IsCanonicalReducedCollision hh
      (minimalSupportPrivateOmissionCanonicalCollision
        g h hh hmin z hlight b) :=
  canonicalizeReducedCollision_isCanonical hh hh0 _

/-- Canonical collisions selected by distinct vertices of the locally light
fiber remain distinct. -/
theorem minimalSupportPrivateOmissionCanonicalCollision_injective
    (g : Fin (n + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (n + 1))
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight g h hmin z) :
    Function.Injective
      (minimalSupportPrivateOmissionCanonicalCollision
        g h hh hmin z hlight) := by
  intro b u hcan
  by_contra hbu
  let rb := minimalSupportPrivateOmissionReducedCollision
    g h hmin z hlight b
  let ru := minimalSupportPrivateOmissionReducedCollision
    g h hmin z hlight u
  have hrawNe : rb ≠ ru := by
    intro hraw
    apply hbu
    apply Subtype.ext
    apply minimalSupportPrivateWitness_injective g h hmin
    calc
      minimalSupportPrivateWitness g h hmin b.val =
          subsetCollisionCoeffs rb.val.1 rb.val.2 :=
        (minimalSupportPrivateOmissionReducedCollision_coeffs
          g h hmin z hlight b).symm
      _ = subsetCollisionCoeffs ru.val.1 ru.val.2 := by rw [hraw]
      _ = minimalSupportPrivateWitness g h hmin u.val :=
        minimalSupportPrivateOmissionReducedCollision_coeffs
          g h hmin z hlight u
  have hrawSwap : rb ≠ reducedSubsetSumCollisionSwapEquiv hh ru := by
    intro hswap
    apply minimalSupportPrivateWitness_ne_neg g h hmin b.val u.val
    calc
      minimalSupportPrivateWitness g h hmin b.val =
          subsetCollisionCoeffs rb.val.1 rb.val.2 :=
        (minimalSupportPrivateOmissionReducedCollision_coeffs
          g h hmin z hlight b).symm
      _ = subsetCollisionCoeffs
          (reducedSubsetSumCollisionSwapEquiv hh ru).val.1
          (reducedSubsetSumCollisionSwapEquiv hh ru).val.2 := by rw [hswap]
      _ = subsetCollisionCoeffs ru.val.2 ru.val.1 := by rfl
      _ = -subsetCollisionCoeffs ru.val.1 ru.val.2 :=
        subsetCollisionCoeffs_swap _ _
      _ = -minimalSupportPrivateWitness g h hmin u.val := by
        rw [minimalSupportPrivateOmissionReducedCollision_coeffs
          g h hmin z hlight u]
  exact (canonicalizeReducedCollision_ne_of_ne_of_ne_swap
    hh rb ru hrawNe hrawSwap) hcan

/-- When the common omission is a non-anchor coordinate `k.succ`, every
canonical collision in the light fiber retains `k` on one of its two sides.
Canonical orientation may swap which side contains it. -/
theorem minimalSupportPrivateOmissionCanonicalCollision_shared_mem
    (g : Fin (n + 1) → G) (h : G) (hh : h + h = 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (k : Fin n)
    (hlight : MinimalSupportPrivateOmissionVerticesTailLight
      g h hmin k.succ)
    (b : ↥(minimalSupportPrivateOmissionVertices g hmin k.succ)) :
    k ∈ (minimalSupportPrivateOmissionCanonicalCollision
          g h hh hmin k.succ hlight b).val.1 ∨
      k ∈ (minimalSupportPrivateOmissionCanonicalCollision
          g h hh hmin k.succ hlight b).val.2 := by
  have hcoeff :
      minimalSupportPrivateWitness g h hmin b.val k.succ = -1 :=
    (mem_minimalSupportPrivateOmissionVertices_iff
      g hmin k.succ b.val).mp b.property
  have hkraw : k ∈
      (minimalSupportPrivateOmissionReducedCollision
        g h hmin k.succ hlight b).val.2 := by
    simpa [minimalSupportPrivateOmissionReducedCollision,
      reducedCollisionOfTailLightWitness, witnessNegativeTail] using hcoeff
  by_cases hcan : IsCanonicalReducedCollision hh
      (minimalSupportPrivateOmissionReducedCollision
        g h hmin k.succ hlight b)
  · exact Or.inr (by
      simpa [minimalSupportPrivateOmissionCanonicalCollision,
        canonicalizeReducedCollision, hcan] using hkraw)
  · left
    simp only [minimalSupportPrivateOmissionCanonicalCollision,
      canonicalizeReducedCollision, hcan, if_false]
    change k ∈
      (minimalSupportPrivateOmissionReducedCollision
        g h hmin k.succ hlight b).val.2
    exact hkraw

end MinModulus
