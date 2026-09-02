/-
# Rejoining the protected private-heavy payload to the target collapse

The target structural residual retains its canonical source/target witness
data, while the enclosing private-heavy descent retains the protected quarter
witness, localized heavy and escape coordinates, and the already constructed
recursive tuple.  This file joins the two layers without projecting either
one away.

First factor the latter data into a named payload and prove that it exactly
reconstructs the original avoidance/escape residual.  Then split on the
critical transversal depth.  A small transversal is retained explicitly; a
large transversal gives either critical crossing or the provenance-rich
target structural residual paired with the very same protected payload.
-/
import MinModulus.G1PrivateHeavyTransversalStructuralProvenance

namespace MinModulus

open Finset

/-- All protected data of the private-heavy escape residual after fixing its
actual minimal transversal. -/
def ProfilePrivateHeavyProtectedPayload
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N)
    (B : Finset (Fin (n + 1))) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧
      ∃ owner : ↥B, ∃ c : Fin (n + 1) → ℤ,
        ∃ k : Fin n, ∃ i : Fin (n + 1),
          Witness g (M : ZMod N) c ∧ c owner ≠ 0 ∧
          (∀ a ∈ B, a ≠ owner → c a = 0) ∧
          2 ≤ c k.succ ∧
          (k.succ = owner ∨ k.succ ∉ B) ∧
          2 * qv i + 2 ≤ c i ∧
          (i = owner ∨ i ∉ B) ∧
          (k.succ = owner → i = owner)

/-- Exact factorization of the original residual into no-common-touch, its
actual transversal, minimality, and the protected payload. -/
theorem profilePrivateHeavyAvoidanceEscape_iff_exists_protectedPayload
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} :
    ProfilePrivateHeavyAvoidanceEscapeDescentResidual
        (N := N) (M := M) (K := K) g ↔
      ∃ _hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
          Witness g (M : ZMod N) c → c e ≠ 0,
        ∃ B : Finset (Fin (n + 1)),
          ∃ _hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
            ProfilePrivateHeavyProtectedPayload
              (N := N) (M := M) (K := K) g B := by
  constructor
  · intro hres
    obtain ⟨hno, t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
      hi, hiLocation, hownerCoincide⟩ := hres
    exact ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
      hi, hiLocation, hownerCoincide⟩
  · rintro ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
      hi, hiLocation, hownerCoincide⟩
    exact ⟨hno, t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
      owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
      hi, hiLocation, hownerCoincide⟩

/-- The lossless small-transversal outcome. -/
def ProfilePrivateHeavySmallTransversalProtectedResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) (D : ℕ) : Prop :=
  ∃ _hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0,
    ∃ B : Finset (Fin (n + 1)),
      ∃ _hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
        ProfilePrivateHeavyProtectedPayload
            (N := N) (M := M) (K := K) g B ∧
          B.card ≤ D + 1

/-- The lossless large-transversal structural outcome. -/
def ProfilePrivateHeavyTargetStructuralProtectedResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0) : Prop :=
  ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0,
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
        ProfilePrivateHeavyProtectedPayload
            (N := N) (M := M) (K := K) g B ∧
          MinimalSupportTransversalHeavyTargetStructuralResidual
            g hg hh hno hmin

/-- The small outcome still contains the original private-heavy residual. -/
theorem ProfilePrivateHeavySmallTransversalProtectedResidual.privateHeavy
    {n N M K D : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hsmall : ProfilePrivateHeavySmallTransversalProtectedResidual
      (N := N) (M := M) (K := K) g D) :
    ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g := by
  obtain ⟨hno, B, hmin, hpayload, _hB⟩ := hsmall
  exact profilePrivateHeavyAvoidanceEscape_iff_exists_protectedPayload.mpr
    ⟨hno, B, hmin, hpayload⟩

/-- The structural outcome still contains the original private-heavy
residual; no protected field was consumed by the target collapse. -/
theorem ProfilePrivateHeavyTargetStructuralProtectedResidual.privateHeavy
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hstruct : ProfilePrivateHeavyTargetStructuralProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g := by
  obtain ⟨hno, B, hmin, hpayload, _hstruct⟩ := hstruct
  exact profilePrivateHeavyAvoidanceEscape_iff_exists_protectedPayload.mpr
    ⟨hno, B, hmin, hpayload⟩

/-- Lossless critical split of the private-heavy residual.  The two
non-crossing outputs retain every field of the input, and the large-
transversal output additionally carries the exact target-private structural
package from the preceding milestone. -/
theorem critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetStructural
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
      (K := 2 ^ (s - 1) * q) g) :
    ProfilePrivateHeavySmallTransversalProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g
        (min (s + 1) (Nat.log 2 (n + 1)) - 1) ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ProfilePrivateHeavyTargetStructuralProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g hg
          (half_add_half (by rw [pow_succ]; ring)) := by
  obtain ⟨hno, B, hmin, hpayload⟩ :=
    profilePrivateHeavyAvoidanceEscape_iff_exists_protectedPayload.mp hres
  let D := min (s + 1) (Nat.log 2 (n + 1)) - 1
  by_cases hB : D + 2 ≤ B.card
  · rcases critical_largeCross_or_transversalHeavyTargetStructuralResidual
        hq g hg hno hmin (by simpa [D] using hB) with hlarge | hstruct
    · exact Or.inr (Or.inl hlarge)
    · exact Or.inr (Or.inr ⟨hno, B, hmin, hpayload, hstruct⟩)
  · left
    exact ⟨hno, B, hmin, hpayload, by
      change B.card ≤ D + 1
      omega⟩

end MinModulus
