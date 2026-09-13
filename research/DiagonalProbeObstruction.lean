import research.ValidTupleOddExtension
import research.AnchoredIntersectionCounterexample

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- If every in-support repeat is a doubled pair, a diagonal probe cannot
see a coefficient supported on that cubic outside the doubled pair cover. -/
theorem diagonal_probe_vanishes_on_doubled_pair_support
    {n N : ℕ} [NeZero N] {K : Type*} [Semiring K]
    (g : Fin n → ZMod N) (T : Finset (Fin n))
    (hpair : ∀ a ∈ T, ∃ u v : Fin n,
      2 • g a+(∑ i ∈ T.erase a, g i)=2 • (g u+g v))
    (M : Fin n → Fin n → K) (hdiag : ∀ a b, a ≠ b → M a b=0)
    (y : ZMod N) (hy : y ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x))
    (c : K) :
    weightedSingleRepeatProbe g 3 M y (fun U ↦ if U=T then c else 0)=0 := by
  classical
  unfold weightedSingleRepeatProbe
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : a=b
  · subst b
    apply mul_eq_zero_of_right
    unfold singleRepeatProbe
    apply Finset.sum_eq_zero
    intro U _
    by_cases hUT : U=T
    · subst U
      have hno : ¬ (a ∈ T ∧ 2 • g a+(∑ i ∈ T.erase a,g i)=y) := by
        rintro ⟨ha,he⟩
        obtain ⟨u,v,hp⟩ := hpair a ha
        apply hy
        apply Finset.mem_image.mpr
        refine ⟨g u+g v,?_,hp.symm.trans he⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,u ::ₘ v ::ₘ 0,by simp,by simp⟩
      simp only [if_neg hno]
    · simp [hUT]
  · simp [hdiag a b hab]

/-- The invisible cubic of the fixed valid four-coordinate control
survives every additive transport and index embedding. -/
theorem transported_control_has_diagonal_invisible_cubic
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (e : Fin 4 ↪ Fin n) (φ : ZMod 15 →+ G)
    (hp : ∀ i, g (e i)=φ (anchoredIntersectionControl i)) :
    ∃ T : Finset (Fin n), T.card=3 ∧ ∀ a ∈ T, ∃ u v : Fin n,
      2 • g a+(∑ i ∈ T.erase a, g i)=2 • (g u+g v) := by
  classical
  let T : Finset (Fin n) := {e 0,e 1,e 3}
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h0 : 2 • anchoredIntersectionControl 0+anchoredIntersectionControl 1+
      anchoredIntersectionControl 3=2 • (anchoredIntersectionControl 2+anchoredIntersectionControl 2) := by decide
  have h1 : 2 • anchoredIntersectionControl 1+anchoredIntersectionControl 0+
      anchoredIntersectionControl 3=2 • (anchoredIntersectionControl 3+anchoredIntersectionControl 2) := by decide
  have h3 : 2 • anchoredIntersectionControl 3+anchoredIntersectionControl 0+
      anchoredIntersectionControl 1=2 • (anchoredIntersectionControl 1+anchoredIntersectionControl 2) := by decide
  refine ⟨T,by simp [T,h01,h03,h13],?_⟩
  intro a ha
  have ha : a=e 0 ∨ a=e 1 ∨ a=e 3 := by simpa [T] using ha
  rcases ha with rfl | rfl | rfl
  · refine ⟨e 2,e 2,?_⟩
    have hm := congrArg φ h0
    simp only [map_add,map_nsmul] at hm
    simp [T,h01,h03,h13,hp]
    convert hm using 1 <;> abel
  · refine ⟨e 3,e 2,?_⟩
    have hm := congrArg φ h1
    simp only [map_add,map_nsmul] at hm
    simp [T,h01,h03,h13,hp]
    convert hm using 1 <;> abel
  · refine ⟨e 1,e 2,?_⟩
    have hm := congrArg φ h3
    simp only [map_add,map_nsmul] at hm
    simp [T,h01,h03,h13,hp]
    convert hm using 1 <;> abel

/-- In every dimension at least four there is a valid odd cyclic tuple
with an invisible cubic for all diagonal probe matrices. This is a
counterexample to diagonal recovery, not to the min-modulus conjecture. -/
theorem exists_diagonal_invisible_cubic_in_every_larger_dimension (r : ℕ) :
    ∃ N : ℕ, Odd N ∧ ∃ g : Fin (4+r) → ZMod N, ValidTuple g ∧
      ∃ T : Finset (Fin (4+r)), T.card=3 ∧ ∀ a ∈ T, ∃ u v : Fin (4+r),
        2 • g a+(∑ i ∈ T.erase a, g i)=2 • (g u+g v) := by
  obtain ⟨N,hN,g,hg,e,φ,hφ,hp⟩ := exists_odd_cyclic_valid_extension
    (by decide : Odd 15) anchoredIntersectionControl anchoredIntersectionControl_valid r
  obtain ⟨T,hT,hpair⟩ := transported_control_has_diagonal_invisible_cubic g e φ hp
  exact ⟨N,hN,g,hg,T,hT,hpair⟩

/-- An invisible cubic supplies a nonzero kernel vector for every
diagonal weighted probe, over any nontrivial coefficient semiring. -/
theorem diagonal_probe_recovery_fails_of_invisible_cubic
    {n N : ℕ} [NeZero N] {K : Type*} [Semiring K] [Nontrivial K]
    (g : Fin n → ZMod N) (T : Finset (Fin n)) (hT : T.card=3)
    (hpair : ∀ a ∈ T, ∃ u v : Fin n,
      2 • g a+(∑ i ∈ T.erase a, g i)=2 • (g u+g v))
    (M : Fin n → Fin n → K) (hdiag : ∀ a b, a ≠ b → M a b=0) :
    ¬ (∀ f h : Finset (Fin n) → K,
      (∀ y : ZMod N, y ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x) →
        weightedSingleRepeatProbe g 3 M y f=weightedSingleRepeatProbe g 3 M y h) →
      ∀ U : Finset (Fin n), U.card=3 → f U=h U) := by
  classical
  intro hdecode
  have hz (y : ZMod N) : weightedSingleRepeatProbe g 3 M y (fun _ ↦ (0 : K))=0 := by
    simp [weightedSingleRepeatProbe,singleRepeatProbe]
  have he := hdecode (fun U ↦ if U=T then 1 else 0) (fun _ ↦ 0) (by
    intro y hy
    rw [diagonal_probe_vanishes_on_doubled_pair_support g T hpair M hdiag y hy 1,hz]) T hT
  simpa using he

end MinModulus.Research
