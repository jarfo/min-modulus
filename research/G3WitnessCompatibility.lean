import MinModulus.G1Triangle

set_option autoImplicit false

/-! The exact admissibility gap in the G3 same-target pigeonhole proposal. -/
namespace MinModulus.Research
open Finset

/-- For tail-light witnesses, only an opposite-sign tail entry or the anchor
can violate the floor required for subtraction. -/
theorem light_witness_sub_floor_iff
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+1) → G) {h t : G} {c d : Fin (m+1) → ℤ}
    (hc : Witness g h c) (hd : Witness g t d)
    (hc_light : ∀ j : Fin m, c j.succ ≤ 1)
    (hd_light : ∀ j : Fin m, d j.succ ≤ 1) :
    (∀ i, -1 ≤ (c-d) i) ↔
      d 0 ≤ c 0+1 ∧ ∀ j : Fin m, ¬ (c j.succ = -1 ∧ d j.succ = 1) := by
  constructor
  · intro hf
    constructor
    · have h0 := hf 0
      simp only [Pi.sub_apply] at h0
      omega
    · intro j hj
      have h := hf j.succ
      simp only [Pi.sub_apply] at h
      omega
  · rintro ⟨h0,htail⟩ i
    refine Fin.cases ?_ ?_ i
    · simp only [Pi.sub_apply]
      omega
    · intro j
      have hcl := hc.2.1 j.succ
      have hdl := hd.2.1 j.succ
      have hcu := hc_light j
      have hdu := hd_light j
      have hj := htail j
      simp only [Pi.sub_apply]
      omega

/-- At one target, two distinct tail-light witnesses with admissible anchor
difference must have a forbidden opposite-sign tail coordinate. -/
theorem same_target_light_witnesses_force_reverse_tail
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+1) → G) (hg : ValidTuple g)
    {h : G} {c d : Fin (m+1) → ℤ}
    (hc : Witness g h c) (hd : Witness g h d) (hne : c ≠ d)
    (hc_light : ∀ j : Fin m, c j.succ ≤ 1)
    (hd_light : ∀ j : Fin m, d j.succ ≤ 1)
    (hanchor : d 0 ≤ c 0+1) :
    ∃ j : Fin m, c j.succ = -1 ∧ d j.succ = 1 := by
  by_contra hnot
  push Not at hnot
  have hf : ∀ i, -1 ≤ (c-d) i :=
    (light_witness_sub_floor_iff g hc hd hc_light hd_light).mpr
      ⟨hanchor,fun j hj ↦ hnot j hj.1 hj.2⟩
  apply (validTuple_iff_no_zero_witness g).mp hg (c-d)
  refine ⟨sub_ne_zero.mpr hne,hf,?_,?_⟩
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hc.2.2.1,hd.2.2.1,sub_self]
  · simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,hc.2.2.2,hd.2.2.2,sub_self]

/-- A fixed target and the omitted tail coordinates determine a tail-light
witness completely. Equal omitted tails make one subtraction direction admissible. -/
theorem same_target_light_witness_eq_of_negative_tail_eq
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+1) → G) (hg : ValidTuple g)
    {h : G} {c d : Fin (m+1) → ℤ}
    (hc : Witness g h c) (hd : Witness g h d)
    (hc_light : ∀ j : Fin m, c j.succ ≤ 1)
    (hd_light : ∀ j : Fin m, d j.succ ≤ 1)
    (htail : ∀ j : Fin m, c j.succ = -1 ↔ d j.succ = -1) : c=d := by
  by_contra hne
  rcases le_total (d 0) (c 0) with ha | ha
  · obtain ⟨j,hc',hd'⟩ := same_target_light_witnesses_force_reverse_tail
      g hg hc hd hne hc_light hd_light (by omega)
    have h := (htail j).mp hc'
    omega
  · obtain ⟨j,hd',hc'⟩ := same_target_light_witnesses_force_reverse_tail
      g hg hd hc (Ne.symm hne) hd_light hc_light (by omega)
    have h := (htail j).mpr hd'
    omega

/-- A family of distinct tail-light witnesses at one target has at most one
member for each omitted-tail subset. This is a bound, not existence of a
compatible pair; the latter is still required by the proposed G3 argument. -/
theorem same_target_light_witness_family_card_le
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+1) → G) (hg : ValidTuple g) (h : G)
    (F : Finset (Fin (m+1) → ℤ))
    (hF : ∀ c ∈ F, Witness g h c)
    (hlight : ∀ c ∈ F, ∀ j : Fin m, c j.succ ≤ 1) : F.card ≤ 2^m := by
  classical
  let negTail : (Fin (m+1) → ℤ) → Finset (Fin m) :=
    fun c ↦ Finset.univ.filter (fun j ↦ c j.succ = -1)
  have hinj : Set.InjOn negTail F := by
    intro c hc d hd he
    apply same_target_light_witness_eq_of_negative_tail_eq g hg
      (hF c hc) (hF d hd) (hlight c hc) (hlight d hd)
    intro j
    have hj := congrArg (fun S : Finset (Fin m) ↦ j ∈ S) he
    simpa only [negTail,Finset.mem_filter,Finset.mem_univ,true_and] using Iff.of_eq hj
  have hh := Finset.card_le_card_of_injOn negTail
    (fun _ _ ↦ Finset.mem_univ _) hinj
  simpa only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using hh

end MinModulus.Research
