import MinModulus.GlobalRoadmap

/-!
# The index-pair pigeonhole for the stratum-one triple

At the first even stratum `N = 2^n - 2 = 2M`, `M = 2^(n-1) - 1`, the
cancelling triple that kills a lift whose extra residue is not
super-increasing is built from two block vectors indexed by a pair
`(a, b)` drawn from the binary support `T` of `2u`.  Compatibility of the
two vectors holds exactly when

* `b - 1` lies in the run `{a-1, …, a+s-3}` of negatives,
* `b - 1 ∉ T`, and
* `a + (s-2) ∉ T.erase b`,

where `s = T.card`.  Taking `b = a` collapses this to the single condition
`a + (s-2) ∉ T.erase a`; otherwise one takes `b = a + (s-2)`.

This file proves that one of the two choices is always available, for an
arbitrary shift `c` in place of `s - 2`.  The mechanism is that a finite
set closed under two translations differing by `1` is closed under `+1`,
hence is everything — which a proper subset cannot be.

Nothing here mentions tuples or validity: it is pure arithmetic in
`ZMod d`.
-/

namespace MinModulus

open Finset

section Pigeonhole

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- A finite subset of `ZMod d` closed under translation by `c` is closed
under translation by `-c` as well: translation is injective, so it permutes
the set. -/
theorem sub_mem_of_add_mem {T : Finset (ZMod d)} {c : ZMod d}
    (h : ∀ x ∈ T, x + c ∈ T) : ∀ x ∈ T, x - c ∈ T := by
  have hsub : T.image (· + c) ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact h x hx
  have hinj : Set.InjOn (· + c) T := by
    intro p _ q _ hpq
    simpa using hpq
  have hcard : T.card ≤ (T.image (· + c)).card :=
    le_of_eq (Finset.card_image_of_injOn hinj).symm
  have himg : T.image (· + c) = T := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx
  rw [← himg] at hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
  have hxy : x - c = y := by rw [← hyx]; ring
  rwa [hxy]

/-- A nonempty finite subset of `ZMod d` closed under two translations whose
difference is `1` is closed under `+1`, hence the whole group. -/
theorem eq_univ_of_add_invariant {T : Finset (ZMod d)} (hne : T.Nonempty)
    {c : ZMod d} (hc : ∀ x ∈ T, x + c ∈ T)
    (hc' : ∀ x ∈ T, x + (c - 1) ∈ T) : T = Finset.univ := by
  have hstep : ∀ x ∈ T, x + 1 ∈ T := by
    intro x hx
    have h1 : x + c ∈ T := hc x hx
    have h2 : (x + c) - (c - 1) ∈ T := sub_mem_of_add_mem hc' _ h1
    have hrw : (x + c) - (c - 1) = x + 1 := by ring
    rwa [hrw] at h2
  obtain ⟨a, ha⟩ := hne
  have hall : ∀ k : ℕ, a + (k : ZMod d) ∈ T := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
        have hk := hstep _ ih
        have hrw : a + (k : ZMod d) + 1 = a + ((k + 1 : ℕ) : ZMod d) := by
          push_cast; ring
        rwa [hrw] at hk
  apply Finset.eq_univ_of_forall
  intro y
  have hy : ((y - a).val : ZMod d) = y - a := ZMod.natCast_rightInverse _
  have := hall (y - a).val
  rwa [hy, add_sub_cancel] at this

/-- **The index pair.**  For a nonempty proper subset `T` of `ZMod d` and any
shift `c`, either some `a ∈ T` has `a + c` outside `T.erase a`, or some
`a ∈ T` has `a + c ∈ T` while `a + c - 1 ∉ T`.

The first alternative is the "concentrated = distributed" choice `b = a`; the
second supplies `b = a + c`, whose predecessor `a + c - 1` is then the last
element of the negative run and lies outside `T`, exactly as the
compatibility computation requires. -/
theorem exists_stratum_one_index_pair (T : Finset (ZMod d)) (hne : T.Nonempty)
    (hlt : T.card < d) (c : ZMod d) :
    (∃ a ∈ T, a + c ∉ T.erase a) ∨
      (∃ a ∈ T, a + (c - 1) ∉ T ∧ a + c ∈ T.erase a) := by
  by_cases hA : ∃ a ∈ T, a + c ∉ T.erase a
  · exact Or.inl hA
  push Not at hA
  -- every `a ∈ T` has `a + c ∈ T`
  have hce : ∀ x ∈ T, x + c ∈ T.erase x := hA
  have hc : ∀ x ∈ T, x + c ∈ T := fun x hx => Finset.mem_of_mem_erase (hA x hx)
  by_cases hB : ∀ x ∈ T, x + (c - 1) ∈ T
  · exfalso
    have := eq_univ_of_add_invariant hne hc hB
    rw [this, Finset.card_univ, ZMod.card] at hlt
    exact lt_irrefl _ hlt
  · push Not at hB
    obtain ⟨a, ha, hfail⟩ := hB
    exact Or.inr ⟨a, ha, hfail, hce a ha⟩

end Pigeonhole

end MinModulus
