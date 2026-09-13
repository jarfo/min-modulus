import research.WeightedProbeLinearRank

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Contract squarefree coefficient functions by one row of a matrix.
The residual support determines which removed coordinates are available. -/
noncomputable def probeContraction {n : ℕ} {K : Type*} [Semiring K]
    (M : Fin n → Fin n → K) (a : Fin n) (S : Finset (Fin n))
    (f : Finset (Fin n) → K) : K := by
  classical
  exact ∑ b, if b ∉ S then M a b * f (insert b S) else 0

/-- Reindex a probe by the residual support after removing its chosen coordinate. -/
theorem single_repeat_probe_reindex_residual_support
    {n N d : ℕ} [NeZero N] {K : Type*} [AddCommMonoid K]
    (g : Fin n → ZMod N) (a b : Fin n) (y : ZMod N)
    (f : Finset (Fin n) → K) :
    singleRepeatProbe g (d+1) a b y f =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        if b ∉ S ∧ 2 • g a+(∑ i ∈ S,g i)=y then f (insert b S) else 0 := by
  classical
  let U := ((Finset.univ : Finset (Fin n)).powersetCard (d+1)).filter (fun T ↦ b ∈ T)
  let V := ((Finset.univ : Finset (Fin n)).powersetCard d).filter (fun S ↦ b ∉ S)
  calc
    _ = ∑ T ∈ U, if 2 • g a+(∑ i ∈ T.erase b,g i)=y then f T else 0 := by
      simp only [singleRepeatProbe,U,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hb : b ∈ T <;> simp [hb]
    _ = ∑ S ∈ V, if 2 • g a+(∑ i ∈ S,g i)=y then f (insert b S) else 0 := by
      apply Finset.sum_bij (fun T _ ↦ T.erase b)
      · intro T hT
        obtain ⟨hT,hb⟩ := Finset.mem_filter.mp hT
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,by simp⟩
        rw [Finset.card_erase_of_mem hb,(Finset.mem_powersetCard.mp hT).2]
        omega
      · intro T hT T' hT' he
        have hb := (Finset.mem_filter.mp hT).2
        have hb' := (Finset.mem_filter.mp hT').2
        rw [← Finset.insert_erase hb,he,Finset.insert_erase hb']
      · intro S hS
        obtain ⟨hS,hb⟩ := Finset.mem_filter.mp hS
        refine ⟨insert b S,?_,Finset.erase_insert hb⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,by simp⟩
        rw [Finset.card_insert_of_notMem hb,(Finset.mem_powersetCard.mp hS).2]
      · intro T hT
        rw [Finset.insert_erase (Finset.mem_filter.mp hT).2]
    _ = _ := by
      simp only [V,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hb : b ∉ S <;> simp [hb]

/-- A full weighted probe first contracts the coefficient function and
then groups the contracted entries by their residue sum. -/
theorem weighted_probe_eq_grouped_contractions
    {n N d : ℕ} [NeZero N] {K : Type*} [Semiring K]
    (g : Fin n → ZMod N) (M : Fin n → Fin n → K) (y : ZMod N)
    (f : Finset (Fin n) → K) :
    weightedSingleRepeatProbe g (d+1) M y f =
      ∑ a, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        if 2 • g a+(∑ i ∈ S,g i)=y then probeContraction M a S f else 0 := by
  classical
  unfold weightedSingleRepeatProbe
  simp_rw [single_repeat_probe_reindex_residual_support,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : 2 • g a+(∑ i ∈ S,g i)=y
  · simp only [h,and_true,if_true,probeContraction,mul_ite,mul_zero]
  · simp only [h,and_false,if_false,mul_zero,Finset.sum_const_zero]

/-- Vanishing contractions imply vanishing weighted probes, at every residue. -/
theorem weighted_probe_eq_zero_of_contractions_eq_zero
    {n N d : ℕ} [NeZero N] {K : Type*} [Semiring K]
    (g : Fin n → ZMod N) (M : Fin n → Fin n → K)
    (f : Finset (Fin n) → K)
    (hz : ∀ a S, S.card=d → probeContraction M a S f=0) (y : ZMod N) :
    weightedSingleRepeatProbe g (d+1) M y f=0 := by
  rw [weighted_probe_eq_grouped_contractions]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro S hS
  rw [hz a S (Finset.mem_powersetCard.mp hS).2]
  simp

/-- An injective matrix preserves every positive-degree squarefree
coefficient through the contraction stage. This does not assert that
subsequent residue grouping preserves those coefficients. -/
theorem injective_matrix_contractions_determine_coefficients
    {n d : ℕ} {K : Type*} [Semiring K]
    (M : Fin n → Fin n → K)
    (hM : Function.Injective (fun v : Fin n → K ↦ fun a ↦ ∑ b, M a b * v b))
    (f h : Finset (Fin n) → K)
    (he : ∀ a S, S.card=d → probeContraction M a S f=probeContraction M a S h) :
    ∀ T : Finset (Fin n), T.card=d+1 → f T=h T := by
  classical
  intro T hT
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let S := T.erase b
  have hS : S.card=d := by rw [Finset.card_erase_of_mem hb,hT]; omega
  let u : Fin n → K := fun c ↦ if c ∉ S then f (insert c S) else 0
  let v : Fin n → K := fun c ↦ if c ∉ S then h (insert c S) else 0
  have huv : u=v := by
    apply hM
    funext a
    simpa only [u,v,mul_ite,mul_zero,probeContraction] using he a S hS
  have heq := congrFun huv b
  simpa [u,v,S,Finset.insert_erase hb] using heq

end MinModulus.Research
