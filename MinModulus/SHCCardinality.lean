/-
# Cardinality bounds from doubles and reflected doubles

An SHC family already forces two elementary layers outside its subset-sum
cube.  This module is kept separate from `QuadraticWedge.lean` so adding the
general bounds does not invalidate the large certificate corpus downstream
of the core `SHC` definition.
-/
import MinModulus.QuadraticWedge

namespace MinModulus

open Finset

section SHCCardinality

variable {G : Type*} [AddCommGroup G] {m : ℕ}

private lemma shc_card_inj {h : Fin m → G} (hs : SHC h) : Function.Injective h := by
  intro a b hab
  have : (∑ j ∈ ({a} : Finset (Fin m)), h j) = ∑ j ∈ ({b} : Finset (Fin m)), h j := by
    simp [hab]
  exact Finset.singleton_injective (hs.dis this)

private lemma shc_card_ne {h : Fin m → G} (hs : SHC h) (a : Fin m) : h a ≠ 0 := by
  intro ha
  have : (∑ j ∈ ({a} : Finset (Fin m)), h j) = ∑ j ∈ (∅ : Finset (Fin m)), h j := by
    simp [ha]
  exact absurd (hs.dis this) (Finset.singleton_ne_empty a)

/-- The subset-sum cube and the coordinate doubles are disjoint in an SHC
family.  Thus an `m`-coordinate SHC family with injective doubling occupies
at least `2^m + m` ambient elements.  This is the SHC analogue of
`card_ge_of_odd'`, but requires no underlying valid tuple. -/
theorem shc_card_ge_cube_add_doubles [Fintype G] (h : Fin m → G) (hs : SHC h) :
    2 ^ m + m ≤ Fintype.card G := by
  classical
  let σ : Finset (Fin m) → G := fun S ↦ ∑ j ∈ S, h j
  have houtside : ∀ (T : Finset (Fin m)) (x : Fin m), σ T ≠ 2 • h x := by
    intro T x heq
    by_cases hT : T = ∅
    · subst T
      have hdouble : 2 • h x = 0 := by simpa [σ] using heq.symm
      apply shc_card_ne hs x
      apply hs.inj2 (h x) 0
      simpa [two_nsmul] using hdouble
    · have hcard : (∅ : Finset (Fin m)).card < T.card := by
        simpa using Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
      have hneq := shc_shift_target_card_gt hs x ∅ T hcard
      simp only [Finset.sum_empty, add_zero] at hneq
      exact hneq heq.symm
  let φ : Finset (Fin m) ⊕ Fin m → G :=
    Sum.elim σ (fun x ↦ 2 • h x)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases x with T | i <;> rcases y with T' | j <;>
      simp only [φ, Sum.elim_inl, Sum.elim_inr] at hxy
    · exact congrArg Sum.inl (hs.dis hxy)
    · exact absurd hxy (houtside T j)
    · exact absurd hxy.symm (houtside T' i)
    · have hij : h i = h j := hs.inj2 (h i) (h j) (by
        simpa [two_nsmul] using hxy)
      exact congrArg Sum.inr (shc_card_inj hs hij)
  have hcard := Fintype.card_le_of_injective φ hφinj
  simp only [Fintype.card_sum, Fintype.card_finset, Fintype.card_fin] at hcard
  exact hcard

/-- For at least three coordinates, the reflected doubles
`(∑ i, h i) - 2 • h x` give a second disjoint `m`-element family outside the
subset-sum cube.  A double cannot equal a reflected double: for distinct
heads this would be a subset-sum collision, while equal heads would be a
forbidden head-3 relation.  Consequently `|G| ≥ 2^m + 2m`. -/
theorem shc_card_ge_cube_add_two_doubles [Fintype G] (hm : 3 ≤ m)
    (h : Fin m → G) (hs : SHC h) : 2 ^ m + 2 * m ≤ Fintype.card G := by
  classical
  let σ : Finset (Fin m) → G := fun S ↦ ∑ j ∈ S, h j
  let total : G := σ Finset.univ
  have houtside : ∀ (T : Finset (Fin m)) (x : Fin m), σ T ≠ 2 • h x := by
    intro T x heq
    by_cases hT : T = ∅
    · subst T
      have hdouble : 2 • h x = 0 := by simpa [σ] using heq.symm
      apply shc_card_ne hs x
      apply hs.inj2 (h x) 0
      simpa [two_nsmul] using hdouble
    · have hcard : (∅ : Finset (Fin m)).card < T.card := by
        simpa using Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
      have hneq := shc_shift_target_card_gt hs x ∅ T hcard
      simp only [Finset.sum_empty, add_zero] at hneq
      exact hneq heq.symm
  have houtside_reflected : ∀ (T : Finset (Fin m)) (x : Fin m),
      σ T ≠ total - 2 • h x := by
    intro T x heq
    have hTne : T ≠ Finset.univ := by
      intro hT
      subst T
      have heq' : total = total - 2 • h x := by simpa [total] using heq
      have hadd := congrArg (fun z : G ↦ z + 2 • h x) heq'
      have hdouble : 2 • h x = 0 := by
        apply add_left_cancel (a := total)
        calc
          total + 2 • h x = (total - 2 • h x) + 2 • h x := hadd
          _ = total + 0 := by simp
      apply shc_card_ne hs x
      apply hs.inj2 (h x) 0
      simpa [two_nsmul] using hdouble
    have hcard_univ : T.card < Finset.univ.card :=
      Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hTne⟩)
    have hcard : T.card < m := by simpa using hcard_univ
    have hneq := shc_shift_target_card_gt hs x T Finset.univ (by simpa using hcard)
    apply hneq
    have heq' : (∑ j ∈ T, h j) = (∑ j ∈ Finset.univ, h j) - 2 • h x := by
      simpa [σ, total] using heq
    rw [heq']
    abel
  have hdouble_ne_reflected : ∀ i j : Fin m, 2 • h i ≠ total - 2 • h j := by
    intro i j heq
    have hsum : 2 • h i + 2 • h j = total := by rw [heq]; abel
    by_cases hij : i = j
    · subst j
      have hsplit : total = h i + σ (Finset.univ.erase i) := by
        simp only [total, σ]
        exact (Finset.add_sum_erase Finset.univ h (Finset.mem_univ i)).symm
      have hrel : 3 • h i = σ (Finset.univ.erase i) := by
        rw [hsplit] at hsum
        have hcancel : h i + 3 • h i = h i + σ (Finset.univ.erase i) := by
          calc
            h i + 3 • h i = 2 • h i + 2 • h i := by
              rw [three_nsmul, two_nsmul]
              abel
            _ = h i + σ (Finset.univ.erase i) := hsum
        exact add_left_cancel hcancel
      refine hs.sh3 i ∅ (Finset.univ.erase i) (Finset.notMem_empty i)
        (Finset.notMem_erase i Finset.univ) (Finset.disjoint_empty_left _) ?_ ?_
      · simp only [Finset.card_empty, zero_add, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        omega
      · simpa [σ] using hrel
    · let P : Finset (Fin m) := {i, j}
      have hpair : σ P = h i + h j := by
        simp [σ, P, hij]
      have hpartition : total = σ P + σ (Finset.univ \ P) := by
        have hpart := Finset.sum_sdiff (Finset.subset_univ P) (f := h)
        simp only [total, σ]
        rw [← hpart]
        abel
      have htwice : (h i + h j) + (h i + h j) =
          (h i + h j) + σ (Finset.univ \ P) := by
        calc
          (h i + h j) + (h i + h j) = 2 • h i + 2 • h j := by
            rw [two_nsmul, two_nsmul]
            abel
          _ = total := hsum
          _ = σ P + σ (Finset.univ \ P) := hpartition
          _ = (h i + h j) + σ (Finset.univ \ P) := by rw [hpair]
      have heqsum : σ P = σ (Finset.univ \ P) := by
        rw [hpair]
        exact add_left_cancel htwice
      have hsets : P = Finset.univ \ P := hs.dis heqsum
      have hi : i ∈ Finset.univ \ P := hsets ▸ (by simp [P])
      simp [P] at hi
  let φ : Finset (Fin m) ⊕ (Fin m ⊕ Fin m) → G :=
    Sum.elim σ (Sum.elim (fun i ↦ 2 • h i) (fun i ↦ total - 2 • h i))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases x with T | i | i <;> rcases y with T' | j | j <;>
      simp only [φ, Sum.elim_inl, Sum.elim_inr] at hxy
    · exact congrArg Sum.inl (hs.dis hxy)
    · exact absurd hxy (houtside T j)
    · exact absurd hxy (houtside_reflected T j)
    · exact absurd hxy.symm (houtside T' i)
    · have hij : h i = h j := hs.inj2 (h i) (h j) (by
        simpa [two_nsmul] using hxy)
      exact congrArg (Sum.inr ∘ Sum.inl) (shc_card_inj hs hij)
    · exact absurd hxy (hdouble_ne_reflected i j)
    · exact absurd hxy.symm (houtside_reflected T' i)
    · exact absurd hxy.symm (hdouble_ne_reflected j i)
    · have hdouble : 2 • h i = 2 • h j := sub_right_injective hxy
      have hij : h i = h j := hs.inj2 (h i) (h j) (by
        simpa [two_nsmul] using hdouble)
      exact congrArg (Sum.inr ∘ Sum.inr) (shc_card_inj hs hij)
  have hcard := Fintype.card_le_of_injective φ hφinj
  simp only [Fintype.card_sum, Fintype.card_finset, Fintype.card_fin] at hcard
  omega

end SHCCardinality

end MinModulus
