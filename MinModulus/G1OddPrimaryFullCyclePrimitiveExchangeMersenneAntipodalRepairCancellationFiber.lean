/-
# At most one exact repair cancellation in an antipodal owner fiber

If a pure external edge cancels with the repair at `m`, its target equals the
root-to-`m` leaf difference.  Two such cancellations with a common pure-edge
center and root would give

  g(b₁) + g(f(m₂)) = g(b₂) + g(f(m₁)).

Validity identifies the two coordinate pairs.  Since both external owners
lie off the leaf, this forces `b₁=b₂`.  Hence every antipodal external owner
fiber contains at most one exact cancellation, uniformly in its size.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairIncidenceMass

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Two off-leaf pure edges with the same center and root cannot represent
root-to-leaf differences at distinct external owners. -/
theorem pureEdge_primaryDifference_owner_eq
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (f : Fin d → Fin n) (center r b₁ b₂ : Fin n) (m₁ m₂ : Fin d)
    (hb₁ : b₁ ∉ (Finset.univ : Finset (Fin d)).image f)
    (hb₂ : b₂ ∉ (Finset.univ : Finset (Fin d)).image f)
    (h₁ : Witness g (g r - g (f m₁))
      (pureEdgeCoeffs center b₁ r))
    (h₂ : Witness g (g r - g (f m₂))
      (pureEdgeCoeffs center b₂ r)) :
    b₁ = b₂ := by
  classical
  have ht₁ := witness_target_eq_of_coeff_eq_pureEdgeCoeffs
    g h₁ center b₁ r rfl
  have ht₂ := witness_target_eq_of_coeff_eq_pureEdgeCoeffs
    g h₂ center b₂ r rfl
  have hb₁eq :
      g b₁ = 2 • g center - g r - (g r - g (f m₁)) := by
    rw [ht₁]
    abel
  have hb₂eq :
      g b₂ = 2 • g center - g r - (g r - g (f m₂)) := by
    rw [ht₂]
    abel
  have hpairs : g b₁ + g (f m₂) = g b₂ + g (f m₁) := by
    rw [hb₁eq, hb₂eq]
    abel
  have hb₁m₂ : b₁ ≠ f m₂ := by
    intro h
    apply hb₁
    exact Finset.mem_image.mpr ⟨m₂, Finset.mem_univ _, h.symm⟩
  have hb₂m₁ : b₂ ≠ f m₁ := by
    intro h
    apply hb₂
    exact Finset.mem_image.mpr ⟨m₁, Finset.mem_univ _, h.symm⟩
  let e : Fin n ↪ Fin n := Function.Embedding.refl _
  have hsets : ({b₁, f m₂} : Finset (Fin n)) = {b₂, f m₁} := by
    apply validTuple_subsetSum_eq_of_card_eq g hg e
    · simp [hb₁m₂, hb₂m₁]
    · simpa only [e, Function.Embedding.coe_refl, id_eq,
        Finset.sum_pair hb₁m₂, Finset.sum_pair hb₂m₁] using hpairs
  have hb₁Right : b₁ ∈ ({b₂, f m₁} : Finset (Fin n)) := by
    rw [← hsets]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb₁Right
  rcases hb₁Right with hb₁b₂ | hb₁m₁
  · exact hb₁b₂
  · exfalso
    apply hb₁
    exact Finset.mem_image.mpr ⟨m₁, Finset.mem_univ _, hb₁m₁.symm⟩

/-- Exact cancellation data for an off-leaf antipodal private row. -/
def AntipodalRepairCancellation
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (b : ↥B) : Prop :=
  p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
    ∃ m : Fin d, ∃ repaired : Fin n → ℤ,
      Witness g (g r - g (f m)) repaired ∧ repaired = p.coeff b

/-- The (classically selected) set of cancelling owners inside an external
fiber. -/
noncomputable def antipodalRepairCancellationOwners
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B) : Finset ↥B := by
  classical
  exact E.filter (AntipodalRepairCancellation g y B p f center r)

/-- Exact repair cancellation is owner-injective inside one off-leaf pure-edge
fiber. -/
theorem antipodalRepairCancellation_owner_injective
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n)
    (b₁ b₂ : ↥B)
    (hb₁ : (b₁ : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f)
    (hb₂ : (b₂ : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f)
    (h₁ : AntipodalRepairCancellation g y B p f center r b₁)
    (h₂ : AntipodalRepairCancellation g y B p f center r b₂) :
    b₁ = b₂ := by
  rcases h₁ with ⟨hshape₁, m₁, repaired₁, hrepair₁, hcancel₁⟩
  rcases h₂ with ⟨hshape₂, m₂, repaired₂, hrepair₂, hcancel₂⟩
  have hpure₁ : Witness g (g r - g (f m₁))
      (pureEdgeCoeffs center (b₁ : Fin n) r) := by
    simpa only [hcancel₁, hshape₁] using hrepair₁
  have hpure₂ : Witness g (g r - g (f m₂))
      (pureEdgeCoeffs center (b₂ : Fin n) r) := by
    simpa only [hcancel₂, hshape₂] using hrepair₂
  exact Subtype.ext (pureEdge_primaryDifference_owner_eq
    g hg f center r (b₁ : Fin n) (b₂ : Fin n) m₁ m₂
      hb₁ hb₂ hpure₁ hpure₂)

/-- An arbitrary off-leaf antipodal owner fiber contains at most one exact
repair cancellation. -/
theorem card_antipodalRepairCancellation_le_one
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f) :
    (antipodalRepairCancellationOwners
      g y B p f center r E).card ≤ 1 := by
  classical
  rw [antipodalRepairCancellationOwners]
  rw [Finset.card_le_one]
  intro b₁ hb₁ b₂ hb₂
  have hb₁Data := Finset.mem_filter.mp hb₁
  have hb₂Data := Finset.mem_filter.mp hb₂
  exact antipodalRepairCancellation_owner_injective
    g hg y B p f center r b₁ b₂
      (hoff b₁ hb₁Data.1) (hoff b₂ hb₂Data.1)
        hb₁Data.2 hb₂Data.2

/-- All but at most one owner in an off-leaf antipodal fiber are
noncancelling. -/
theorem card_pred_antipodalRepairNoncancellation
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f) :
    E.card - 1 ≤ (E \ antipodalRepairCancellationOwners
      g y B p f center r E).card := by
  classical
  have hcancel := card_antipodalRepairCancellation_le_one
    g hg y B p f center r E hoff
  rw [antipodalRepairCancellationOwners] at hcancel
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := E) (AntipodalRepairCancellation g y B p f center r)
  have hdiff : E \ E.filter
      (AntipodalRepairCancellation g y B p f center r) =
      E.filter (fun b ↦
        ¬ AntipodalRepairCancellation g y B p f center r b) := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [antipodalRepairCancellationOwners, hdiff]
  omega

/-- In particular, a secondary antipodal fiber of size at least three has at
least two noncancelling owners. -/
theorem two_le_card_antipodalRepairNoncancellation_of_three_le
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (center r : Fin n) (E : Finset ↥B)
    (hoff : ∀ b : ↥B, b ∈ E →
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image f)
    (hE : 3 ≤ E.card) :
    2 ≤ (E \ antipodalRepairCancellationOwners
      g y B p f center r E).card := by
  have hpred := card_pred_antipodalRepairNoncancellation
    g hg y B p f center r E hoff
  omega

end MinModulus
