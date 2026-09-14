import research.CharTwoSixPointInterpolation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MinModulus.Research
open Finset
open scoped CharTwo

/-- Three conjugate pairs of torus points, with a common unit weight. -/
def frobeniusCubicPoints {K : Type*} [Field K] (w : K) : Fin 6 → Fin 3 → K :=
  ![![1,w,1], ![1,w+1,1], ![1,1,w], ![1,1,w+1],
    ![1,w,w], ![1,w+1,w+1]]

/-- Distinct torus points of exponent three, closed under Frobenius. -/
theorem frobeniusCubicPoints_properties
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0) :
    Function.Injective (frobeniusCubicPoints w) ∧
      (∀ i j, frobeniusCubicPoints w i j ≠ 0) ∧
      (∀ i j, (frobeniusCubicPoints w i j)^3=1) ∧
      (∀ i, ∃ l, ∀ j, (frobeniusCubicPoints w i j)^2=
        frobeniusCubicPoints w l j) := by
  obtain ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩ := cube_root_char_two_identities w hw
  have hne : w ≠ w+1 := by intro h; have := add_left_cancel (by simpa using h : w+0=w+1); exact zero_ne_one this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i l he
    have ha := congrFun he (1 : Fin 3)
    have hb := congrFun he (2 : Fin 3)
    fin_cases i <;> fin_cases l <;> simp_all [frobeniusCubicPoints]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [frobeniusCubicPoints,h0,h20]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [frobeniusCubicPoints,h3,hb3]
  · intro i
    fin_cases i
    · refine ⟨1, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,h2]
    · refine ⟨0, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,hb2]
    · refine ⟨3, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,h2]
    · refine ⟨2, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,hb2]
    · refine ⟨5, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,h2]
    · refine ⟨4, ?_⟩; intro j; fin_cases j <;> simp [frobeniusCubicPoints,hb2]

/-- Unit-weight moments extract the squarefree cubic coefficient. -/
theorem frobeniusCubicPoints_moments
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0)
    (a b c : ℕ) (hdegree : a+b+c=3) :
    (∑ i : Fin 6, (frobeniusCubicPoints w i 0)^a *
      (frobeniusCubicPoints w i 1)^b * (frobeniusCubicPoints w i 2)^c)=
      if a=1 ∧ b=1 ∧ c=1 then 1 else 0 := by
  obtain ⟨h0,h1,h20,h21,h2,h3,hb2,hb3⟩ := cube_root_char_two_identities w hw
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num at hdegree <;> norm_num <;>
    simp [Fin.sum_univ_succ,frobeniusCubicPoints,h2,h3,hb2,hb3] <;>
    ring_nf <;> simp [h2,h3,add_assoc]

/-- Every homogeneous cubic is handled, not just the monomial basis. -/
theorem frobeniusCubicPoints_interpolation
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0)
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3) :
    (∑ i : Fin 6, MvPolynomial.eval (frobeniusCubicPoints w i) f) =
      f.coeff cubicTopExponent := by
  classical
  have hmon (d : Fin 3 →₀ ℕ) (hd : d ∈ f.support) :
      (∑ i : Fin 6, ∏ j : Fin 3, frobeniusCubicPoints w i j ^ d j) =
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
      frobeniusCubicPoints_moments w hw (d 0) (d 1) (d 2) hdeg
  simp_rw [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  calc
    _ = ∑ d ∈ f.support, f.coeff d * (if d = cubicTopExponent then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum, hmon d hd]
    _ = f.coeff cubicTopExponent := by
      simp only [mul_ite, mul_one, mul_zero]
      by_cases h : cubicTopExponent ∈ f.support
      · simp [h]
      · simp [h, MvPolynomial.notMem_support_iff.mp h]

/-- These six points cannot be one full multiplicative cyclic orbit,
even after reordering and allowing an arbitrary starting point. -/
theorem frobeniusCubicPoints_not_cyclic_enumeration
    {K : Type*} [Field K] [CharP K 2] (w : K) (hw : w^2+w+1=0) :
    ¬ ∃ (u b : Fin 3 → K) (e : Equiv.Perm (Fin 6)),
      ∀ (i : Fin 6) (j : Fin 3), frobeniusCubicPoints w (e i) j=b j*(u j)^i.val := by
  rintro ⟨u,b,e,he⟩
  obtain ⟨hinj,hzero,hcube,hfrob⟩ := frobeniusCubicPoints_properties w hw
  have hb (j : Fin 3) : (b j)^3=1 := by
    have h := hcube (e 0) j
    simpa [he] using h
  have hu (j : Fin 3) : (u j)^3=1 := by
    have h := hcube (e 1) j
    simpa [he,mul_pow,hb] using h
  have hpoints : frobeniusCubicPoints w (e 3)=frobeniusCubicPoints w (e 0) := by
    funext j
    simp [he,hu]
  have h := e.injective (hinj hpoints)
  exact (by decide : (3 : Fin 6) ≠ 0) h

/-- Frobenius stability, torus coordinates and unit weights still do not
imply an unrestricted seven-point bound. Cyclic-orbit structure is absent. -/
theorem frobenius_stable_six_point_counterexample :
    ∃ P : Fin 6 → Fin 3 → GaloisField 2 2,
      Function.Injective P ∧ (∀ i j, P i j ≠ 0) ∧
      (∀ i, ∃ l, ∀ j, (P i j)^2=P l j) ∧
      (∀ f : MvPolynomial (Fin 3) (GaloisField 2 2), f.IsHomogeneous 3 →
        (∑ i : Fin 6, MvPolynomial.eval (P i) f)=f.coeff cubicTopExponent) ∧
      (¬ ∃ (u b : Fin 3 → GaloisField 2 2) (e : Equiv.Perm (Fin 6)),
        ∀ (i : Fin 6) (j : Fin 3), P (e i) j=b j*(u j)^i.val) ∧
      6 < 2^3-1 := by
  obtain ⟨w,hw⟩ := exists_cubic_root_galois_field_four
  obtain ⟨hi,h0,hcube,hfrob⟩ := frobeniusCubicPoints_properties w hw
  exact ⟨frobeniusCubicPoints w,hi,h0,hfrob,
    frobeniusCubicPoints_interpolation w hw,
    frobeniusCubicPoints_not_cyclic_enumeration w hw,by decide⟩

end MinModulus.Research
