/-
# Heavy-witness omission escape

The canonical-profile branch is closed, leaving large crossing mass and a
genuinely heavy half-witness as the two alternatives to common touch.  This
file extracts the first global structure from the heavy branch.

Fix a witness `c` with one coefficient at least two.  Witness combination
shows that every other half-witness shares an omitted coordinate with `c`:
otherwise it would equal `-c`, whose coefficient at the heavy coordinate is
at most `-2`.  If common touch fails, each omission of `c` has a witness that
vanishes there.  Such a witness must therefore share a *different* omission
of `c`.  Thus the heavy branch carries a finite omission transversal together
with an escape at every point of that transversal.
-/
import MinModulus.G1LargeNegativeRootClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A witness with a coefficient at least two has an omission in common with
every witness at the same involution.  This is the generic hitting-set form
of `witness_combination`. -/
theorem exists_common_omission_of_heavyWitness
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {c : Fin m → ℤ} (hc : Witness g h c) {k : Fin m} (hk : 2 ≤ c k)
    {c' : Fin m → ℤ} (hc' : Witness g h c') :
    ∃ i : Fin m, c i = -1 ∧ c' i = -1 := by
  by_contra hnone
  have hshare : ∀ i, ¬ (c i = -1 ∧ c' i = -1) := by
    intro i hi
    exact hnone ⟨i, hi⟩
  have hneg := witness_combination g hg hh hc hc' hshare
  have hge := hc'.2.1 k
  have hcoeff := congrFun hneg k
  simp only [Pi.neg_apply] at hcoeff
  omega

/-- The strengthened heavy alternative retained after common-touch failure:
one heavy witness supplies an omission transversal for all witnesses, and
every one of its omissions can be avoided only by escaping through a
different omission of the same witness. -/
def CriticalHeavyOmissionEscape
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ∃ c : Fin (n + 1) → ℤ,
    Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      (∃ k : Fin n, 2 ≤ c k.succ) ∧
      (∀ c' : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c' →
          ∃ i : Fin (n + 1), c i = -1 ∧ c' i = -1) ∧
      ∀ b : Fin (n + 1), c b = -1 →
        ∃ c' : Fin (n + 1) → ℤ,
          Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c' ∧
            c' b = 0 ∧
            ∃ a : Fin (n + 1), a ≠ b ∧ c a = -1 ∧ c' a = -1

/-- A critical heavy half-witness and failure of common touch produce the
full omission-transversal escape package. -/
theorem criticalHeavyOmissionEscape_of_not_commonTouched
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hheavy : CriticalHeavyHalfWitness g)
    (hno : ¬ CriticalCommonTouched g) :
    CriticalHeavyOmissionEscape g := by
  obtain ⟨c, hc, k, hk⟩ := hheavy
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hh :
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) +
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) = 0 :=
    half_add_half hN
  have htrans : ∀ c' : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c' →
        ∃ i : Fin (n + 1), c i = -1 ∧ c' i = -1 := by
    intro c' hc'
    exact exists_common_omission_of_heavyWitness g hg hh hc hk hc'
  refine ⟨c, hc, ⟨k, hk⟩, htrans, ?_⟩
  intro b hcb
  have havoid : ∃ c' : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c' ∧
        c' b = 0 := by
    by_contra hnone
    apply hno
    refine ⟨b, ?_⟩
    intro c' hc'
    by_contra hzero
    apply hnone
    exact ⟨c', hc', hzero⟩
  obtain ⟨c', hc', hcb'⟩ := havoid
  obtain ⟨a, hca, hca'⟩ := htrans c' hc'
  refine ⟨c', hc', hcb', a, ?_, hca, hca'⟩
  intro hab
  subst a
  omega

/-- The heavy escape package contains two distinct omissions in its root
witness.  This is the first nontrivial hypergraph layer forced by heaviness
and no common touch. -/
theorem criticalHeavyOmissionEscape_two_distinct_omissions
    {n s q : ℕ} {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    (hescape : CriticalHeavyOmissionEscape g) :
    ∃ c : Fin (n + 1) → ℤ, ∃ a b : Fin (n + 1),
      a ≠ b ∧ c a = -1 ∧ c b = -1 := by
  obtain ⟨c, hc, _hheavy, htrans, hesc⟩ := hescape
  obtain ⟨b, hcb, _⟩ := htrans c hc
  obtain ⟨c', _hc', _hzero, a, hab, hca, _hca'⟩ := hesc b hcb
  exact ⟨c, a, b, hab, hca, hcb⟩

/-- After the canonical residual is eliminated, the raw heavy alternative
can be sharpened to a recursive omission-transversal escape. -/
theorem critical_largeCross_or_commonTouched_or_heavyOmissionEscape
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyOmissionEscape g := by
  rcases critical_largeCross_or_commonTouched_or_heavy
      hn hqodd g hg hcritical with hcross | htouch | hheavy
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · by_cases htouch : CriticalCommonTouched g
    · exact Or.inr (Or.inl htouch)
    · exact Or.inr (Or.inr
        (criticalHeavyOmissionEscape_of_not_commonTouched
          g hg hheavy htouch))

end MinModulus
