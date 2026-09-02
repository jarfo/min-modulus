/-
# Escape refinement of the private-heavy profile residual

A private-heavy protected descent already contains more structure than its
basic residual type records.  Privacy locates the heavy tail coordinate at
the owner or outside the deletion set.  Applying validity to `2q-c` also
produces an explicit coefficient-floor escape, and privacy gives the same
owner-or-external localization for that escape.  This module retains both
facts for the remaining global deletion problem.
-/
import MinModulus.G1ProfileLocalLightDescent

namespace MinModulus

open Finset

/-- A private-heavy protected descent enriched by the locations of both its
heavy tail coordinate and one explicit `2q-c` coefficient-floor escape. -/
def ProfilePrivateHeavyEscapeDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    ∃ B : Finset (Fin (n + 1)),
      MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
      t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧
      ∃ owner : {b : Fin (n + 1) // b ∈ B},
        ∃ c : Fin (n + 1) → ℤ, ∃ k : Fin n, ∃ i : Fin (n + 1),
          Witness g (M : ZMod N) c ∧ c owner ≠ 0 ∧
          (∀ a ∈ B, a ≠ owner → c a = 0) ∧
          2 ≤ c k.succ ∧
          (k.succ = owner ∨ k.succ ∉ B) ∧
          2 * qv i + 2 ≤ c i ∧
          (i = owner ∨ i ∉ B) ∧
          (k.succ = owner → i = owner)

/-- Privacy localizes every heavy coordinate of an explicit private witness:
it is the owner itself or lies outside the deletion set. -/
theorem privateHeavyCoordinate_eq_owner_or_external
    {m : ℕ}
    {B : Finset (Fin (m + 1))}
    (owner : {b : Fin (m + 1) // b ∈ B})
    (c : Fin (m + 1) → ℤ)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m) (hk : 2 ≤ c k.succ) :
    k.succ = owner ∨ k.succ ∉ B := by
  by_cases hko : k.succ = owner
  · exact Or.inl hko
  · right
    intro hkB
    have hkzero := hprivate k.succ hkB hko
    omega

/-- A coefficient-floor escape of an explicit private witness is likewise at
the owner or outside the deletion set, provided the protected vector vanishes
on the deletion set. -/
theorem privateCoefficientEscape_eq_owner_or_external
    {m : ℕ}
    {B : Finset (Fin m)}
    (owner : {b : Fin m // b ∈ B})
    (qv c : Fin m → ℤ)
    (hqzero : ∀ a ∈ B, qv a = 0)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (i : Fin m) (hi : 2 * qv i + 2 ≤ c i) :
    i = owner ∨ i ∉ B := by
  by_cases hio : i = owner
  · exact Or.inl hio
  · right
    intro hiB
    have hqizero := hqzero i hiB
    have hcizero := hprivate i hiB hio
    omega

/-- Every private-heavy residual canonically refines to one retaining an
explicit escape and owner-or-external localization for both distinguished
coordinates. -/
theorem privateHeavyEscape_of_privateTailHeavy
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hprivateHeavy : ProfilePrivateTailHeavyDescentResidual
      (N := N) (M := M) (K := K) g) :
    ProfilePrivateHeavyEscapeDescentResidual
      (N := N) (M := M) (K := K) g := by
  classical
  obtain ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, hc, hcowner, hprivate, hk⟩ := hprivateHeavy
  have hqzero : ∀ a ∈ B, qv a = 0 := by
    intro a haB
    have haOutside := hBsub haB
    have haNotSupport := (Finset.mem_sdiff.mp haOutside).2
    by_contra hqa
    exact haNotSupport ((mem_coefficientSupport_iff qv a).2 hqa)
  have hkLocation :=
    privateHeavyCoordinate_eq_owner_or_external owner c hprivate k hk
  rcases hkLocation with hkowner | hkexternal
  · have hownerEscape : 2 * qv owner + 2 ≤ c owner := by
      have hqowner := hqzero owner owner.property
      rw [hkowner] at hk
      omega
    exact ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, owner, hc, hcowner, hprivate, hk,
      Or.inl hkowner, hownerEscape, Or.inl rfl, fun _ ↦ rfl⟩
  · have hc' : Witness g (t + t) c := by
      rwa [ht]
    obtain ⟨i, hi⟩ := exists_twice_quarter_coefficientEscape
      g hg hqv hc' (hqzero owner owner.property) hcowner
    have hiLocation := privateCoefficientEscape_eq_owner_or_external
      owner qv c hqzero hprivate i hi
    exact ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, i, hc, hcowner, hprivate, hk,
      Or.inr hkexternal, hi, hiLocation,
      fun hkowner ↦ False.elim
        (hkexternal (by rw [hkowner]; exact owner.property))⟩

end MinModulus
