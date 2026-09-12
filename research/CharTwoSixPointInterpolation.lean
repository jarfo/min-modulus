import Mathlib

/-!
# A six-point obstruction to an unrestricted characteristic-two rank route

A cyclic character interpolation associated to an odd-modulus valid tuple
has additional orbit structure. Dropping that structure does not justify a
2^n-1 lower bound: six distinct torus points already extract the squarefree
cubic coefficient in characteristic two. This is not a min-modulus
counterexample.
-/

namespace MinModulus.Research
open Finset
open scoped CharTwo

/-- Six affine points used by a characteristic-two cubic interpolation. -/
def sixCubicPoints {K : Type*} [Field K] (w : K) : Fin 6 → Fin 3 → K :=
  ![![1,1,1], ![1,w,1], ![1,w+1,w+1], ![1,w+1,w], ![1,w,w+1], ![1,1,w]]

/-- Reduction identities for a primitive cube root in characteristic two. -/
theorem cube_root_char_two_identities
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0) :
    w ≠ 0 ∧ w ≠ 1 ∧ w+1 ≠ 0 ∧ w+1 ≠ 1 ∧
      w^2=w+1 ∧ w^3=1 ∧ (w+1)^2=w ∧ (w+1)^3=1 := by
  have h0 : w ≠ 0 := by intro h; subst w; norm_num at hw
  have h1 : w ≠ 1 := by intro h; subst w; simp at hw
  have h20 : w+1 ≠ 0 := by
    intro h
    have he : w = -1 := eq_neg_of_add_eq_zero_left h
    exact h1 (by simpa only [CharTwo.neg_eq] using he)
  have h21 : w+1 ≠ 1 := by
    intro h
    apply h0
    exact add_right_cancel (by simpa using h : w+1=0+1)
  have h2 : w^2=w+1 := by
    have he : w^2 = -(w+1) := eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hw)
    simpa only [CharTwo.neg_eq] using he
  have h3 : w^3=1 := by
    calc
      _ = (w-1)*(w^2+w+1)+1 := by ring
      _ = 1 := by rw [hw]; ring
  have hb2 : (w+1)^2=w := by
    rw [add_sq,h2]
    simp
  have hb3 : (w+1)^3=1 := by
    rw [pow_succ,hb2]
    calc
      w*(w+1)=w^2+w := by ring
      _=1 := by rw [h2,add_right_comm,CharTwo.add_self_eq_zero,zero_add]
  exact ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩

/-- The six points have no zero coordinate. -/
theorem sixCubicPoints_ne_zero
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0)
    (i : Fin 6) (j : Fin 3) : sixCubicPoints w i j ≠ 0 := by
  obtain ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩ := cube_root_char_two_identities w hw
  fin_cases i <;> fin_cases j <;> simp [sixCubicPoints,h0,h20]

/-- The six normalized affine points are pairwise distinct. -/
theorem sixCubicPoints_injective
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0) :
    Function.Injective (sixCubicPoints w) := by
  obtain ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩ := cube_root_char_two_identities w hw
  intro i j he
  have ha := congrFun he (1 : Fin 3)
  have hb := congrFun he (2 : Fin 3)
  fin_cases i <;> fin_cases j <;> simp_all [sixCubicPoints]

/-- These six evaluations, with the common nonzero weight w, agree
with squarefree-coefficient extraction on every degree-three monomial. -/
theorem sixCubicPoints_moments
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0)
    (a b c : ℕ) (hdegree : a+b+c=3) :
    w*(∑ i : Fin 6, (sixCubicPoints w i 0)^a *
      (sixCubicPoints w i 1)^b * (sixCubicPoints w i 2)^c)=
      if a=1 ∧ b=1 ∧ c=1 then 1 else 0 := by
  obtain ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩ := cube_root_char_two_identities w hw
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num at hdegree <;> norm_num <;>
    simp [Fin.sum_univ_succ,sixCubicPoints,h2,h3,hb2,hb3] <;>
    ring_nf <;> simp [h2,h3,add_assoc]


/-- The exponent vector for the squarefree cubic. -/
noncomputable def cubicTopExponent : Fin 3 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1

/-- Six evaluations extract the squarefree coefficient of every homogeneous cubic. -/
theorem sixCubicPoints_interpolation
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0)
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3) :
    w * (∑ i : Fin 6, MvPolynomial.eval (sixCubicPoints w i) f) =
      f.coeff cubicTopExponent := by
  classical
  have hmon (d : Fin 3 →₀ ℕ) (hd : d ∈ f.support) :
      w * (∑ i : Fin 6, ∏ j : Fin 3, sixCubicPoints w i j ^ d j) =
        if d = cubicTopExponent then 1 else 0 := by
    have hdeg : d 0 + d 1 + d 2 = 3 := by
      have hh := hf.degree_eq_sum_deg_support hd
      have hs : (∑ j ∈ d.support, d j) = ∑ j : Fin 3, d j := by
        exact Finset.sum_subset (Finset.subset_univ _) (by
          intro j _ hj
          exact Finsupp.notMem_support_iff.mp hj)
      rw [hs] at hh
      simpa [Fin.sum_univ_succ, add_assoc] using hh.symm
    have he : d = cubicTopExponent ↔ d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 1 := by
      constructor
      · intro h; subst d; simp [cubicTopExponent]
      · rintro ⟨h0,h1,h2⟩
        ext j
        fin_cases j <;> simp [cubicTopExponent,h0,h1,h2]
    simpa [Fin.prod_univ_succ, mul_assoc, he] using
      sixCubicPoints_moments w hw (d 0) (d 1) (d 2) hdeg
  simp_rw [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ d ∈ f.support, f.coeff d * (if d = cubicTopExponent then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum]
      calc
        _ = f.coeff d * (w * (∑ i : Fin 6, ∏ j : Fin 3, sixCubicPoints w i j ^ d j)) := by ring
        _ = _ := by rw [hmon d hd]
    _ = f.coeff cubicTopExponent := by
      simp only [mul_ite, mul_one, mul_zero]
      by_cases h : cubicTopExponent ∈ f.support
      · simp [h]
      · simp [h, MvPolynomial.notMem_support_iff.mp h]

/-- The required nontrivial cube root exists in the field with four elements. -/
theorem exists_cubic_root_galois_field_four :
    ∃ w : GaloisField 2 2, w^2+w+1=0 := by
  classical
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 (n := 2) (by decide)
  have hex : ∃ w : GaloisField 2 2, w ≠ 0 ∧ w ≠ 1 := by
    by_contra! h
    have hsub : (Finset.univ : Finset (GaloisField 2 2)) ⊆ {0,1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have hc := Finset.card_le_card hsub
    simp [hcard] at hc
  obtain ⟨w,h0,h1⟩ := hex
  refine ⟨w, ?_⟩
  have hp : w^4=w := by simpa [hcard] using FiniteField.pow_card w
  have hm : w*(w-1)*(w^2+w+1)=0 := by
    calc
      _ = w^4-w := by ring
      _ = 0 := by rw [hp]; ring
  exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero h0 (sub_ne_zero.mpr h1))

/-- A concrete counterexample to a seven-point lower bound for unrestricted
characteristic-two coefficient extraction, including nonzero coordinates. -/
theorem six_point_cubic_counterexample :
    ∃ (w : GaloisField 2 2) (P : Fin 6 → Fin 3 → GaloisField 2 2),
      w ≠ 0 ∧ Function.Injective P ∧ (∀ i j, P i j ≠ 0) ∧
      (∀ f : MvPolynomial (Fin 3) (GaloisField 2 2), f.IsHomogeneous 3 →
        w * (∑ i : Fin 6, MvPolynomial.eval (P i) f) = f.coeff cubicTopExponent) ∧
      6 < 2^3 - 1 := by
  obtain ⟨w,hw⟩ := exists_cubic_root_galois_field_four
  exact ⟨w, sixCubicPoints w, (cube_root_char_two_identities w hw).1,
    sixCubicPoints_injective w hw, sixCubicPoints_ne_zero w hw,
    sixCubicPoints_interpolation w hw, by decide⟩

end MinModulus.Research
