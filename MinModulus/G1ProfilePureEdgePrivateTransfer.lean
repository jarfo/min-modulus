/-
# Transferring a pure-edge-heavy residual to private heavy structure

A half witness must meet every support transversal.  Apply this to the
tail-heavy pure edge retained by the profile descent.  If the edge meets the
minimal transversal in exactly one coordinate, it is itself a private heavy
witness and transfers to the private-heavy residual.  The only remaining
pure-edge case is a double hit: at least two of its three support coordinates
belong to the deletion set.
-/
import MinModulus.G1ProfileLocalLightDescent

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The coefficient support of a pure edge is exactly its center and two
endpoints. -/
theorem coefficientSupport_pureEdgeCoeffs
    (x a b : Fin m) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    coefficientSupport (pureEdgeCoeffs x a b) = {x, a, b} := by
  classical
  ext i
  simp only [mem_coefficientSupport_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hi
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (pureEdgeCoeffs_ne_zero_mem x a b i hi)
  · intro hi
    rcases hi with rfl | rfl | rfl
    · simp [pureEdgeCoeffs, hxa, hxb]
    · simp [pureEdgeCoeffs, Ne.symm hxa, hab]
    · simp [pureEdgeCoeffs, Ne.symm hxb, Ne.symm hab]

/-- The genuinely new pure-edge-heavy case after transferring every
single-hit edge to the private-heavy residual. -/
def ProfilePureEdgeDoubleHitDescentResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) : Prop :=
  ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
    ∃ B : Finset (Fin (n + 1)),
      MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
      t + t = (M : ZMod N) ∧ Witness g t qv ∧
      B ⊆ Finset.univ \ coefficientSupport qv ∧
      AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
      2 ≤ B.card ∧
      ∃ c : Fin (n + 1) → ℤ, ∃ x a b : Fin (n + 1), ∃ k : Fin n,
        Witness g (M : ZMod N) c ∧ x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
        c = pureEdgeCoeffs x a b ∧ x = k.succ ∧ c k.succ = 2 ∧
        2 ≤ (B ∩ {x, a, b}).card

/-- A protected tail-heavy pure edge is either already a private heavy
witness for its unique transversal hit, or its three-coordinate support has
at least two hits in the minimal transversal. -/
theorem privateTailHeavy_or_pureEdgeDoubleHit_of_pureEdgeTailHeavy
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hpure : ProfilePureEdgeTailHeavyDescentResidual
      (N := N) (M := M) (K := K) g) :
    ProfilePrivateTailHeavyDescentResidual
        (N := N) (M := M) (K := K) g ∨
      ProfilePureEdgeDoubleHitDescentResidual
        (N := N) (M := M) (K := K) g := by
  classical
  obtain ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard, hedge⟩ :=
    hpure
  obtain ⟨c, x, a, b, k, hc, hxa, hxb, hab,
    hcPure, hxk, hck⟩ := hedge.exists_center_tail
  obtain ⟨z, hzB, hcz⟩ := hmin.1 c hc
  have hzSupport : z ∈ ({x, a, b} : Finset (Fin (n + 1))) := by
    have hzCoeff : z ∈ coefficientSupport c :=
      (mem_coefficientSupport_iff c z).mpr hcz
    rw [hcPure, coefficientSupport_pureEdgeCoeffs x a b hxa hxb hab]
      at hzCoeff
    exact hzCoeff
  let E : Finset (Fin (n + 1)) := B ∩ {x, a, b}
  have hzE : z ∈ E := Finset.mem_inter.mpr ⟨hzB, hzSupport⟩
  by_cases hdouble : 2 ≤ E.card
  · exact Or.inr
      ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
        c, x, a, b, k, hc, hxa, hxb, hab, hcPure, hxk, hck,
        by simpa [E] using hdouble⟩
  · have hprivateZero : ∀ u ∈ B, u ≠ z → c u = 0 := by
      intro u huB huz
      by_contra hcu
      have huSupport : u ∈ ({x, a, b} : Finset (Fin (n + 1))) := by
        have huCoeff : u ∈ coefficientSupport c :=
          (mem_coefficientSupport_iff c u).mpr hcu
        rw [hcPure, coefficientSupport_pureEdgeCoeffs x a b hxa hxb hab]
          at huCoeff
        exact huCoeff
      have huE : u ∈ E := Finset.mem_inter.mpr ⟨huB, huSupport⟩
      have : 1 < E.card :=
        Finset.one_lt_card.mpr ⟨z, hzE, u, huE, Ne.symm huz⟩
      omega
    exact Or.inl
      ⟨t, qv, B, hmin, ht, hqv, hBsub, hrec, hBcard,
        ⟨z, hzB⟩, c, k, hc, hcz, hprivateZero, by omega⟩

end MinModulus
