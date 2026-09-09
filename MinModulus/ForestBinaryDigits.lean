import MinModulus.BoundaryProfileCount

namespace MinModulus
open Finset
open scoped Classical

/-- The actual binary digit in each chain, formed from the original
subset coordinates through the supplied chain equivalence. -/
noncomputable def forestSubsetDigits
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U : Finset (Fin n)) :
    ∀ a, Fin (2^(L a)) := fun a ↦
  ⟨∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), 2^j.val,
    finset_fin_binary_weight_lt (L a) _⟩

/-- The explicit chain digits distinguish all original subsets. -/
theorem forest_subset_digits_injective
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) :
    Function.Injective (forestSubsetDigits L E) := by
  classical
  intro U V he
  have hpart (a : β) : Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U)=
      Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ V) := by
    apply finset_fin_binary_weight_injective (L a)
    exact congrArg (fun p ↦ (p a).val) he
  ext v
  obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective v
  have h := Finset.ext_iff.mp (hpart a) j
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using h

/-- The explicit chain-digit map is a bijection onto the whole forest box. -/
theorem forest_subset_digits_bijective
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) :
    Function.Bijective (forestSubsetDigits L E) := by
  classical
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨forest_subset_digits_injective L E,?_⟩
  simp only [Fintype.card_finset,Fintype.card_fin,Fintype.card_pi,Finset.prod_pow_eq_pow_sum,hsize]

/-- Explicit binary digits preserve every actual shifted subset sum. -/
theorem forest_subset_digits_sum_eq
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (U : Finset (Fin n)) :
    (∑ a, (forestSubsetDigits L E U a).val • x a)=∑ i ∈ U, (g i+b) := by
  classical
  change (∑ a, (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), 2^j.val) • x a)=_
  calc
    _=∑ a, ∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), (g (E ⟨a,j⟩)+b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_nsmul_assoc]
      exact Finset.sum_congr rfl (fun j _ ↦ (hchain a j).symm)
    _=∑ t : (Σ a : β, Fin (L a)), if E t ∈ U then g (E t)+b else 0 := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_filter]
    _=∑ v : Fin n, if v ∈ U then g v+b else 0 := E.sum_comp (fun v ↦ if v ∈ U then g v+b else 0)
    _=∑ i ∈ U, (g i+b) := by simp

/-- Box weight is the sum of the actual binary place weights of the
selected original coordinates. -/
theorem forest_subset_digit_weight_eq
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U : Finset (Fin n)) :
    (∑ a, (forestSubsetDigits L E U a).val)=∑ v ∈ U, 2^(E.symm v).2.val := by
  classical
  calc
    _=∑ t : (Σ a : β, Fin (L a)), if E t ∈ U then 2^t.2.val else 0 := by
      rw [Fintype.sum_sigma]
      simp only [forestSubsetDigits,Finset.sum_filter]
    _=∑ v : Fin n, if v ∈ U then 2^(E.symm v).2.val else 0 := by
      rw [← E.sum_comp (fun v ↦ if v ∈ U then 2^(E.symm v).2.val else 0)]
      apply Finset.sum_congr rfl
      intro t _
      exact congrArg (fun s : (Σ a : β, Fin (L a)) ↦ if E t ∈ U then 2^s.2.val else 0)
        (E.symm_apply_apply t).symm
    _=∑ v ∈ U, 2^(E.symm v).2.val := by simp

/-- On disjoint original subsets, the actual digits add coordinatewise
without a carry from a common selected bit. -/
theorem forest_subset_digits_add_of_disjoint
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U V : Finset (Fin n))
    (hd : Disjoint U V) (a : β) :
    (forestSubsetDigits L E (U ∪ V) a).val=
      (forestSubsetDigits L E U a).val+(forestSubsetDigits L E V a).val := by
  classical
  let A := Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U)
  let B := Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ V)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  have hpart : Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U ∪ V)=A ∪ B := by
    ext j
    simp only [A,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  change (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U ∪ V), 2^j.val)=
    (∑ j ∈ A, 2^j.val)+(∑ j ∈ B, 2^j.val)
  rw [hpart,Finset.sum_union hdis]

/-- Box weight exceeds subset cardinality by at most the full forest
diameter minus its number of original coordinates. -/
theorem forest_subset_digit_weight_bounds
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U : Finset (Fin n)) :
    U.card ≤ (∑ a, (forestSubsetDigits L E U a).val) ∧
      (∑ a, (forestSubsetDigits L E U a).val) ≤ U.card+((∑ a, (2^(L a)-1))-n) := by
  classical
  let d := fun v : Fin n ↦ 2^(E.symm v).2.val
  have hd (v : Fin n) : 1 ≤ d v := by
    have hp : 0 < (2 : ℕ)^(E.symm v).2.val := by positivity
    exact hp
  have hsum (V : Finset (Fin n)) :
      (∑ v ∈ V, d v)=V.card+(∑ v ∈ V, (d v-1)) := by
    rw [Finset.card_eq_sum_ones,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have hv := hd v
    omega
  have htotal : (∑ v : Fin n, d v)=∑ a, (2^(L a)-1) := by
    change (∑ v ∈ Finset.univ, 2^(E.symm v).2.val)=_
    rw [← forest_subset_digit_weight_eq L E Finset.univ]
    apply Finset.sum_congr rfl
    intro a _
    change (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ Finset.univ), 2^j.val)=2^(L a)-1
    simp only [Finset.mem_univ,Finset.filter_true,Fin.sum_univ_eq_sum_range]
    exact sum_two_pow (L a)
  have hU := hsum U
  have hall := hsum Finset.univ
  simp only [Finset.card_univ,Fintype.card_fin] at hall
  rw [htotal] at hall
  have hle := Finset.sum_le_sum_of_subset (Finset.subset_univ U) (f:=fun v ↦ d v-1)
  rw [forest_subset_digit_weight_eq]
  change U.card ≤ (∑ v ∈ U, d v) ∧ (∑ v ∈ U, d v) ≤ U.card+((∑ a, (2^(L a)-1))-n)
  constructor <;> omega

/-- On each actual equal-sum fibre of a valid positive forest, box
weight order agrees exactly with original subset cardinality order. -/
theorem forest_subset_digit_weight_lt_iff_card_lt_of_equal_sum
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) :
    (∑ a, (forestSubsetDigits L E U a).val) < (∑ a, (forestSubsetDigits L E V a).val) ↔ U.card < V.card := by
  by_cases hUV : U=V
  · subst V
    simp
  have hne : forestSubsetDigits L E U ≠ forestSubsetDigits L E V :=
    fun h ↦ hUV (forest_subset_digits_injective L E h)
  have heval : (∑ a, (forestSubsetDigits L E U a).val • x a)=
      ∑ a, (forestSubsetDigits L E V a).val • x a := by
    rw [forest_subset_digits_sum_eq L g E x b hchain U,forest_subset_digits_sum_eq L g E x b hchain V,he]
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ a, (2^(L a)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro a _
    have hh := Nat.lt_two_pow_self (n:=L a)
    omega
  have hU := forest_subset_digit_weight_bounds L E U
  have hV := forest_subset_digit_weight_bounds L E V
  have hspacing := box_weight_spacing_of_valid_chain_forest_collision L hL g hg E x b hchain
    (forestSubsetDigits L E U) (forestSubsetDigits L E V) hne heval
  rcases hspacing with hs | hs <;> constructor <;> intro h <;> omega

end MinModulus
