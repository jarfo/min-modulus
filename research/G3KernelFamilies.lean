import research.G3MiddleLayer
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false

namespace MinModulus.Research
open Finset

/-- Compatible zero-sum coefficient vectors have distinct weighted targets
in a valid tuple, even when the family contains the zero vector. -/
theorem compatible_zero_sum_family_target_injective
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (F : Finset (Fin n → ℤ))
    (hsum : ∀ c ∈ F, ∑ i, c i = 0)
    (hfloor : ∀ c ∈ F, ∀ d ∈ F, ∀ i, -1 ≤ c i-d i) :
    Set.InjOn (fun c : Fin n → ℤ ↦ ∑ i, c i • g i) F := by
  intro c hc d hd he
  by_contra hne
  apply (validTuple_iff_no_zero_witness g).mp hg (c-d)
  refine ⟨sub_ne_zero.mpr hne,?_,?_,?_⟩
  · intro i
    exact hfloor c hc d hd i
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hsum c hc,hsum d hd,sub_self]
  · simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,he,sub_self]

/-- A common fixed-rank quotient fibre supplies a simultaneous compatible
family, not just independently chosen witnesses. There are more than r
distinct targets, including zero, and every vector vanishes outside A. -/
theorem large_rank_yields_compatible_kernel_family
    {n k r : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n))
    (hlarge : Fintype.card H*r < A.card.choose k) :
    ∃ F : Finset (Fin n → ℤ), 0 ∈ F ∧ r < F.card ∧
      (∀ c ∈ F, (∑ i, c i)=0 ∧ f (∑ i, c i • g i)=0 ∧
        ∀ i, i ∉ A → c i=0) ∧
      (∀ c ∈ F, ∀ d ∈ F, ∀ i, -1 ≤ c i-d i ∧ c i-d i ≤ 1) ∧
      Set.InjOn (fun c : Fin n → ℤ ↦ ∑ i, c i • g i) F := by
  classical
  let v : Finset (Fin n) → H := fun S ↦ ∑ i ∈ S, f (g i)
  obtain ⟨y,_,hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := A.powersetCard k) (t := Finset.univ) (f := v)
    (fun _ _ ↦ Finset.mem_univ _) (by simpa only [Finset.card_univ,Finset.card_powersetCard] using hlarge)
  let E := (A.powersetCard k).filter (fun S ↦ v S=y)
  have hE : r < E.card := hy
  obtain ⟨T,hT⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hE)
  have hdata (S : Finset (Fin n)) (hS : S ∈ E) :
      S ⊆ A ∧ S.card=k ∧ v S=y := by
    have hh := Finset.mem_filter.mp hS
    exact ⟨(Finset.mem_powersetCard.mp hh.1).1,
      (Finset.mem_powersetCard.mp hh.1).2,hh.2⟩
  have hTd := hdata T hT
  let delta : Finset (Fin n) → Fin n → ℤ := fun S i ↦
    (if i ∈ S then 1 else 0)-(if i ∈ T then 1 else 0)
  have hinj : Function.Injective delta := by
    intro S U he
    ext i
    have hh := congrFun he i
    dsimp [delta] at hh
    by_cases hS : i ∈ S <;> by_cases hU : i ∈ U <;>
      by_cases hT : i ∈ T <;> simp_all
  let F := E.image delta
  have hzero : (0 : Fin n → ℤ) ∈ F := by
    apply Finset.mem_image.mpr
    exact ⟨T,hT,by funext i; simp [delta]⟩
  have hsize : r < F.card := by
    simpa only [F,Finset.card_image_of_injective _ hinj] using hE
  have hvalues : ∀ c ∈ F, (∑ i, c i)=0 ∧ f (∑ i, c i • g i)=0 ∧
      ∀ i, i ∉ A → c i=0 := by
    intro c hc
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hc
    have hSd := hdata S hS
    refine ⟨?_,?_,?_⟩
    · simp [delta,Finset.sum_sub_distrib,hSd.2.1,hTd.2.1]
    · have hw : (∑ i, delta S i • g i) = (∑ i ∈ S, g i)-∑ i ∈ T, g i := by
        simp only [delta,sub_smul,ite_smul,one_zsmul,zero_smul,
          Finset.sum_sub_distrib,Finset.sum_ite_mem,Finset.univ_inter]
      rw [hw,map_sub,map_sum,map_sum]
      change v S-v T=0
      rw [hSd.2.2,hTd.2.2,sub_self]
    · intro i hi
      have hiS : i ∉ S := fun hh ↦ hi (hSd.1 hh)
      have hiT : i ∉ T := fun hh ↦ hi (hTd.1 hh)
      simp [delta,hiS,hiT]
  have hpair : ∀ c ∈ F, ∀ d ∈ F, ∀ i, -1 ≤ c i-d i ∧ c i-d i ≤ 1 := by
    intro c hc d hd i
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hd
    dsimp [delta]
    split_ifs <;> omega
  exact ⟨F,hzero,hsize,hvalues,hpair,
    compatible_zero_sum_family_target_injective g hg F
      (fun c hc ↦ (hvalues c hc).1) (fun c hc d hd i ↦ (hpair c hc d hd i).1)⟩

/-- Every nonzero member of a compatible family containing zero is a
reversible witness; validity keeps its target nonzero. -/
theorem reversible_witness_of_compatible_family
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (F : Finset (Fin n → ℤ))
    (hzero : 0 ∈ F) (hsum : ∀ c ∈ F, ∑ i, c i=0)
    (hpair : ∀ c ∈ F, ∀ d ∈ F, ∀ i, -1 ≤ c i-d i ∧ c i-d i ≤ 1)
    {c : Fin n → ℤ} (hc : c ∈ F) (hcne : c ≠ 0) :
    (∑ i, c i • g i) ≠ 0 ∧ Witness g (∑ i, c i • g i) c ∧
      Witness g (-(∑ i, c i • g i)) (-c) := by
  have hunit : ∀ i, -1 ≤ c i ∧ c i ≤ 1 := by
    intro i
    simpa only [Pi.zero_apply,sub_zero] using hpair c hc 0 hzero i
  have hw : Witness g (∑ i, c i • g i) c :=
    ⟨hcne,fun i ↦ (hunit i).1,hsum c hc,rfl⟩
  refine ⟨?_,hw,witness_neg_of_unit_coefficients g hw (fun i ↦ (hunit i).2)⟩
  intro hz
  exact (validTuple_iff_no_zero_witness g).mp hg c (hz ▸ hw)

/-- All differences between distinct members of the common-base family
are reversible witnesses as well, at the corresponding nonzero target differences. -/
theorem difference_witness_of_compatible_family
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (F : Finset (Fin n → ℤ))
    (hsum : ∀ c ∈ F, ∑ i, c i=0)
    (hpair : ∀ c ∈ F, ∀ d ∈ F, ∀ i, -1 ≤ c i-d i ∧ c i-d i ≤ 1)
    {c d : Fin n → ℤ} (hc : c ∈ F) (hd : d ∈ F) (hne : c ≠ d) :
    (∑ i, c i • g i)-(∑ i, d i • g i) ≠ 0 ∧
      Witness g ((∑ i, c i • g i)-(∑ i, d i • g i)) (c-d) ∧
      Witness g (-((∑ i, c i • g i)-(∑ i, d i • g i))) (-(c-d)) := by
  have hw : Witness g ((∑ i, c i • g i)-(∑ i, d i • g i)) (c-d) := by
    refine ⟨sub_ne_zero.mpr hne,fun i ↦ (hpair c hc d hd i).1,?_,?_⟩
    · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hsum c hc,hsum d hd,sub_self]
    · simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
  refine ⟨?_,hw,witness_neg_of_unit_coefficients g hw (fun i ↦ (hpair c hc d hd i).2)⟩
  intro hz
  exact (validTuple_iff_no_zero_witness g).mp hg (c-d) (hz ▸ hw)

end MinModulus.Research
