/-
# Transversal shift forced by a private-heavy avoidance state

The exact-profile private-heavy branch is reached under failure of common
touch.  An avoiding witness at the private owner must still meet the minimal
support transversal, hence it meets a different deleted coordinate.  The
private-heavy witness vanishes at that new coordinate.  This produces a
directed internal shift on the deletion set while retaining the heavy/escape
data and recursive tuple.
-/
import MinModulus.G1PrivateHeavyEscape

namespace MinModulus

open Finset

/-- The remaining exact-profile residual with its ambient no-common-touch
hypothesis retained instead of discarded. -/
def ProfilePrivateHeavyAvoidanceEscapeDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  (¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0) ∧
    ProfilePrivateHeavyEscapeDescentResidual
      (N := N) (M := M) (K := K) g

/-- Under failure of common touch, an avoiding witness at a private owner
must move to a distinct coordinate of the same support transversal.  At that
new coordinate the original private witness is zero. -/
theorem exists_privateTransversalShift_of_noCommonTouch
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (owner : {b : Fin m // b ∈ B})
    (c : Fin m → ℤ)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0) :
    ∃ r : Fin m → ℤ, ∃ u : {a : Fin m // a ∈ B},
      Witness g h r ∧ r owner = 0 ∧ u ≠ owner ∧
      r u ≠ 0 ∧ c u = 0 := by
  have havoid : ¬ ∀ r : Fin m → ℤ,
      Witness g h r → r owner ≠ 0 := by
    intro hall
    exact hno ⟨owner, hall⟩
  push Not at havoid
  obtain ⟨r, hr, hrowner⟩ := havoid
  obtain ⟨u, huB, hru⟩ := hmin.1 r hr
  have huowner : u ≠ owner := by
    intro huo
    subst u
    exact hru hrowner
  exact ⟨r, ⟨u, huB⟩, hr, hrowner, by
    intro huo
    exact huowner (congrArg Subtype.val huo), hru,
    hprivate u huB huowner⟩

/-- Every avoidance-enriched private-heavy residual contains an explicit
internal transversal shift at the same private owner and witness. -/
theorem ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_shift
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g) :
    ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
      ∃ B : Finset (Fin (n + 1)),
        MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
        t + t = (M : ZMod N) ∧ Witness g t qv ∧
        B ⊆ Finset.univ \ coefficientSupport qv ∧
        AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
        2 ≤ B.card ∧
        ∃ owner : {b : Fin (n + 1) // b ∈ B},
          ∃ c r : Fin (n + 1) → ℤ,
            ∃ u : {a : Fin (n + 1) // a ∈ B},
              Witness g (M : ZMod N) c ∧ c owner ≠ 0 ∧
              (∀ a ∈ B, a ≠ owner → c a = 0) ∧
              Witness g (M : ZMod N) r ∧ r owner = 0 ∧
              u ≠ owner ∧ r u ≠ 0 ∧ c u = 0 := by
  obtain ⟨hno, t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
    owner, c, _k, _i, hc, hcowner, hprivate, _hk, _hkLocation,
    _hi, _hiLocation, _hownerCoincide⟩ := hres
  obtain ⟨r, u, hr, hrowner, huowner, hru, hcu⟩ :=
    exists_privateTransversalShift_of_noCommonTouch
      g hno hmin owner c hprivate
  exact ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
    owner, c, r, u, hc, hcowner, hprivate,
    hr, hrowner, huowner, hru, hcu⟩

end MinModulus
