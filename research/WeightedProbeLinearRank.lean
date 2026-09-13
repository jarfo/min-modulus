import research.WeightedProbeCardinality
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A weighted probe is additive in the coefficient vector. -/
theorem weighted_single_repeat_probe_add
    {n N d : ℕ} [NeZero N] {K : Type*} [Semiring K]
    (g : Fin n → ZMod N) (M : Fin n → Fin n → K) (y : ZMod N)
    (f h : Finset (Fin n) → K) :
    weightedSingleRepeatProbe g d M y (f+h)=
      weightedSingleRepeatProbe g d M y f+weightedSingleRepeatProbe g d M y h := by
  classical
  have hi (p : Prop) [Decidable p] (u v : K) :
      (if p then u+v else 0)=(if p then u else 0)+(if p then v else 0) := by
    by_cases h : p <;> simp [h]
  simp only [weightedSingleRepeatProbe,singleRepeatProbe,Pi.add_apply,
    hi,Finset.sum_add_distrib,mul_add]

/-- Over a commutative semiring, scalar multiplication commutes with a
weighted probe. -/
theorem weighted_single_repeat_probe_smul
    {n N d : ℕ} [NeZero N] {K : Type*} [CommSemiring K]
    (g : Fin n → ZMod N) (M : Fin n → Fin n → K) (y : ZMod N)
    (c : K) (f : Finset (Fin n) → K) :
    weightedSingleRepeatProbe g d M y (c • f)=
      c * weightedSingleRepeatProbe g d M y f := by
  classical
  have hi (p : Prop) [Decidable p] (u : K) :
      (if p then c*u else 0)=c*(if p then u else 0) := by
    by_cases h : p <;> simp [h]
  simp only [weightedSingleRepeatProbe,singleRepeatProbe,Pi.smul_apply,
    smul_eq_mul,hi,Finset.mul_sum,mul_left_comm]

/-- In every even degree, one coefficient-preserving probe combination
outside the doubled half-degree cover forces the corresponding cardinality
increment. No validity assumption or finiteness of the coefficient field is needed. -/
theorem even_degree_card_bound_of_weighted_probe_injective_field
    {n N k : ℕ} [NeZero N] {K : Type*} [Field K]
    (hN : Odd N) (g : Fin n → ZMod N)
    (M : Fin n → Fin n → K)
    (hdecode : ∀ f h : Finset (Fin n) → K,
      (∀ y : ZMod N, y ∉ (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x) →
        weightedSingleRepeatProbe g (2*k+1) M y f=weightedSingleRepeatProbe g (2*k+1) M y h) →
      ∀ T : Finset (Fin n), T.card=2*k+1 → f T=h T) :
    (actualFibreCoinCover g (k+1)).card+n.choose (2*k+1) ≤
      (repeatedCoinCover g (2*k+2)).card := by
  classical
  let S := (Finset.univ : Finset (Fin n)).powersetCard (2*k+1)
  let D := (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)
  let E := repeatedCoinCover g (2*k+2) \ D
  let extend (f : S → K) (T : Finset (Fin n)) : K :=
    if h : T ∈ S then f ⟨T,h⟩ else 0
  let encode : (S → K) →ₗ[K] (E → K) := {
    toFun := fun f y ↦ weightedSingleRepeatProbe g (2*k+1) M y.val (extend f)
    map_add' := by
      intro f h
      funext y
      have he : extend (f+h)=extend f+extend h := by
        funext T
        simp only [extend,Pi.add_apply]
        split_ifs <;> simp
      rw [he,weighted_single_repeat_probe_add]
      rfl
    map_smul' := by
      intro c f
      funext y
      have he : extend (c • f)=c • extend f := by
        funext T
        simp only [extend,Pi.smul_apply]
        split_ifs <;> simp
      rw [he,weighted_single_repeat_probe_smul]
      rfl }
  have hi : Function.Injective encode := by
    intro f h he
    have hh := hdecode (extend f) (extend h) (by
      intro y hy
      by_cases hyr : y ∈ repeatedCoinCover g (2*k+2)
      · have hE : y ∈ E := Finset.mem_sdiff.mpr ⟨hyr,hy⟩
        exact congrFun he ⟨y,hE⟩
      · have hz (q : Finset (Fin n) → K) : weightedSingleRepeatProbe g (2*k+1) M y q=0 := by
          unfold weightedSingleRepeatProbe
          simp only [single_repeat_probe_eq_zero_outside_repeated g _ _ y hyr,
            mul_zero,Finset.sum_const_zero]
        rw [hz,hz])
    funext T
    have hT := hh T.val (Finset.mem_powersetCard.mp T.property).2
    simpa only [extend,dif_pos T.property] using hT
  have hSE : S.card ≤ E.card := by
    have hcount := LinearMap.finrank_le_finrank_of_injective (f := encode) hi
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hcount
  have hS : S.card=n.choose (2*k+1) := by simp [S]
  have hsub : D ⊆ repeatedCoinCover g (2*k+2) :=
    by
      simpa only [mul_add,Nat.mul_one] using
        doubled_coin_cover_subset_repeated_coin_cover (k := k+1) (by omega) g
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro a b he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using he
  have hD : D.card=(actualFibreCoinCover g (k+1)).card :=
    Finset.card_image_of_injective _ hd
  have hE : E.card=(repeatedCoinCover g (2*k+2)).card-D.card := Finset.card_sdiff_of_subset hsub
  have hle := Finset.card_le_card hsub
  omega

/-- A single coefficient-preserving probe combination outside the doubled
two-coin cover gives the absolute quartic repeated-sum bound, uniformly in n.
The coefficient field may include symbolic matrix indeterminates. -/
theorem absolute_quartic_bound_of_weighted_probe_injective_field
    {n N : ℕ} [NeZero N] {K : Type*} [Field K]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (M : Fin n → Fin n → K)
    (hdecode : ∀ f h : Finset (Fin n) → K,
      (∀ y : ZMod N, y ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x) →
        weightedSingleRepeatProbe g 3 M y f=weightedSingleRepeatProbe g 3 M y h) →
      ∀ T : Finset (Fin n), T.card=3 → f T=h T) :
    (n+1).choose 2+n.choose 3 ≤ (repeatedCoinCover g 4).card := by
  have h := even_degree_card_bound_of_weighted_probe_injective_field (k := 1) hN g M hdecode
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at h
  rwa [two_coin_card_eq_of_odd hN g hg] at h

end MinModulus.Research
