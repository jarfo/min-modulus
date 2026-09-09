import MinModulus.RankedOutsideCollisionGap

namespace MinModulus
open Finset
open scoped Classical

/-- Outside subsets with the same actual sum have cardinalities
separated by the available ranked growth plus one. -/
theorem outside_subset_card_spacing_of_ranked_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C : Finset (Fin n)) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val)
    (U V : Finset (Fin n)) (hU : U ⊆ Finset.univ \ C) (hV : V ⊆ Finset.univ \ C)
    (hne : U ≠ V) (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) :
    U.card+((∑ i : C, 2^(r i))+1-C.card) ≤ V.card ∨
      V.card+((∑ i : C, 2^(r i))+1-C.card) ≤ U.card := by
  have hcne : U.card ≠ V.card := by
    intro hc
    apply hne
    apply tuple_subset_fibre_cardinality_injective g hg 0 (∑ i ∈ U, g i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using he.symm⟩) hc
  rcases lt_or_gt_of_ne hcne with hc | hc
  · have hh := ranked_growth_lt_card_add_outside_collision_gap g hg C r hp V U hV he.symm hc
    left; omega
  · have hh := ranked_growth_lt_card_add_outside_collision_gap g hg C r hp U V hU he hc
    right; omega

/-- The actual subset fibre on a disjoint block has at most one
member per cardinality interval of the proved ranked-growth spacing. -/
theorem disjoint_subset_fibre_card_le_of_ranked_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hdCT : Disjoint C T) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val) (z : G) :
    (T.powerset.filter (fun U ↦ (∑ i ∈ U, g i)=z)).card ≤
      T.card/((∑ i : C, 2^(r i))+1-C.card)+1 := by
  classical
  let W := ∑ i : C, 2^(r i)
  let d := W+1-C.card
  have hCW : C.card ≤ W := by
    calc
      _ = ∑ _i : C, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ Nat.one_le_two_pow)
  have hd : 0 < d := by dsimp only [d]; omega
  have hTC : T ⊆ Finset.univ \ C := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc ↦ Finset.disjoint_left.mp hdCT hc hi⟩
  let F := T.powerset.filter (fun U ↦ (∑ i ∈ U, g i)=z)
  have hsub (U : F) : U.val ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp U.property).1
  let f : F → Fin (T.card/d+1) := fun U ↦ ⟨U.val.card/d,
    Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.card_le_card (hsub U)))⟩
  have hf : Function.Injective f := by
    intro U V he
    by_contra hne
    have hUV : U.val ≠ V.val := fun h ↦ hne (Subtype.ext h)
    have hsum : (∑ i ∈ U.val, g i)=(∑ i ∈ V.val, g i) :=
      (Finset.mem_filter.mp U.property).2.trans (Finset.mem_filter.mp V.property).2.symm
    have heq : U.val.card/d=V.val.card/d := congrArg Fin.val he
    have hu := Nat.mod_lt U.val.card hd
    have hv := Nat.mod_lt V.val.card hd
    have hdu := Nat.mod_add_div U.val.card d
    have hdv := Nat.mod_add_div V.val.card d
    rw [heq] at hdu
    rcases outside_subset_card_spacing_of_ranked_growth g hg C r hp U.val V.val
      ((hsub U).trans hTC) ((hsub V).trans hTC) hUV hsum with hh | hh
    · change _+d ≤ _ at hh
      omega
    · change _+d ≤ _ at hh
      omega
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin,F,d,W] using hh

/-- The number of gaps in an actual outside fibre, times the ranked
growth spacing, cannot exceed the outside block's cardinality. -/
theorem disjoint_subset_fibre_card_pred_mul_growth_le
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hdCT : Disjoint C T) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val) (z : G) :
    ((T.powerset.filter (fun U ↦ (∑ i ∈ U, g i)=z)).card-1)*
      ((∑ i : C, 2^(r i))+1-C.card) ≤ T.card := by
  have hCW : C.card ≤ ∑ i : C, 2^(r i) := by
    calc
      _ = ∑ _i : C, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ Nat.one_le_two_pow)
  have hd : 0 < (∑ i : C, 2^(r i))+1-C.card := by omega
  have hh := disjoint_subset_fibre_card_le_of_ranked_growth g hg C T hdCT r hp z
  apply (Nat.le_div_iff_mul_le hd).mp
  simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hh 1

/-- Ranked growth lowers the multiplicity of every disjoint subset
sum, giving a lower bound on the entire actual subset image. -/
theorem disjoint_subset_image_card_lower_bound_of_ranked_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hdCT : Disjoint C T) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val) :
    2^T.card ≤ (T.card/((∑ i : C, 2^(r i))+1-C.card)+1)*(subsetSumImageOn g T).card := by
  classical
  calc
    _ = T.powerset.card := Finset.card_powerset T |>.symm
    _ = ∑ z ∈ subsetSumImageOn g T, (T.powerset.filter (fun U ↦ (∑ i ∈ U, g i)=z)).card :=
      Finset.card_eq_sum_card_image (fun U : Finset (Fin n) ↦ ∑ i ∈ U, g i) T.powerset
    _ ≤ ∑ _z ∈ subsetSumImageOn g T, (T.card/((∑ i : C, 2^(r i))+1-C.card)+1) := by
      apply Finset.sum_le_sum
      intro z _
      exact disjoint_subset_fibre_card_le_of_ranked_growth g hg C T hdCT r hp z
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]

end MinModulus
