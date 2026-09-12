import research.RepeatedCoinGrowth

set_option autoImplicit false

/-! Uniform collision bounds for sums with exactly one doubled coordinate. -/
namespace MinModulus.Research
open Finset

/-- In two single-repeat representations of the same value, either repeated
coordinate is absent from the support of the other representation. -/
theorem single_repeat_support_avoids_other_anchor
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (a b : Fin n) (hab : a ≠ b) (S T : Finset (Fin n))
    (ha : a ∈ S) (hcard : S.card = T.card)
    (he : (∑ i ∈ S, g i)+g a = (∑ i ∈ T, g i)+g b) : b ∉ S := by
  classical
  intro hb
  have he' : (∑ i ∈ S.erase b, g i)+g a = ∑ i ∈ T, g i := by
    have hs := Finset.sum_erase_add S g hb
    have hh : ((∑ i ∈ S.erase b, g i)+g a)+g b = (∑ i ∈ T, g i)+g b := by
      calc
        _ = (∑ i ∈ S, g i)+g a := by rw [← hs]; abel
        _ = _ := he
    exact add_right_cancel hh
  have hm : a ::ₘ (S.erase b).val = T.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg T _
    · simp only [Multiset.card_cons, ← Finset.card_def]
      have hc := Finset.card_erase_add_one hb
      omega
    · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
        add_comm] using he'
  have hn := T.nodup
  rw [← hm] at hn
  exact (Multiset.nodup_cons.mp hn).1 (Finset.mem_erase.mpr ⟨hab,ha⟩)

/-- Any family of single-repeat representations has distinct residual supports
at odd order; all residual supports avoid every repeated coordinate in the family. -/
theorem single_repeat_family_card_le_choose
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun y : G ↦ 2 • y))
    (x : G) (R : Finset (Fin n)) (S : Fin n → Finset (Fin n))
    (ha : ∀ a ∈ R, a ∈ S a)
    (hc : ∀ a ∈ R, (S a).card = k+1)
    (hv : ∀ a ∈ R, (∑ i ∈ S a, g i)+g a = x) :
    R.card ≤ (n-R.card).choose k := by
  classical
  let f : Fin n → Finset (Fin n) := fun a ↦ (S a).erase a
  have hf : Set.MapsTo f R (Rᶜ.powersetCard k) := by
    intro a har
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro b hb
      apply Finset.mem_compl.mpr
      intro hbr
      have hb' := Finset.mem_erase.mp hb
      exact single_repeat_support_avoids_other_anchor g hg a b
        (Ne.symm hb'.1) (S a) (S b) (ha a har)
        ((hc a har).trans (hc b hbr).symm)
        ((hv a har).trans (hv b hbr).symm) hb'.2
    · dsimp [f]
      have hh := Finset.card_erase_add_one (ha a har)
      have hh' := hc a har
      omega
  have hi : Set.InjOn f R := by
    intro a har b hbr hab
    have hsa := Finset.sum_erase_add (S a) g (ha a har)
    have hsb := Finset.sum_erase_add (S b) g (ha b hbr)
    have hs : (∑ i ∈ (S a).erase a, g i) = ∑ i ∈ (S b).erase b, g i := by
      change f a = f b at hab
      exact congrArg (fun U : Finset (Fin n) ↦ ∑ i ∈ U, g i) hab
    have he : 2 • g a = 2 • g b := by
      have h := (hv a har).trans (hv b hbr).symm
      simp only [two_nsmul]
      have hh : (∑ i ∈ (S a).erase a, g i)+(g a+g a) =
          (∑ i ∈ (S a).erase a, g i)+(g b+g b) := by
        calc
          _ = (∑ i ∈ S a, g i)+g a := by rw [← hsa]; abel
          _ = (∑ i ∈ S b, g i)+g b := h
          _ = _ := by rw [← hsb,← hs]; abel
      exact add_left_cancel hh
    exact validTuple_injective g hg (hd he)
  have hh := Finset.card_le_card_of_injOn f hf hi
  simpa only [Finset.card_powersetCard,Finset.card_compl,Fintype.card_fin] using hh

/-- Repeated coordinates occurring in representations with one double and k
other, distinct coordinates. The total coin degree is k+2. -/
noncomputable def singleRepeatFibre {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (k : ℕ) (x : G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun a ↦ ∃ S : Finset (Fin n),
    a ∈ S ∧ S.card=k+1 ∧ (∑ i ∈ S, g i)+g a=x)

/-- Membership interface independent of the chosen decidability instance. -/
theorem mem_singleRepeatFibre {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (x : G) (a : Fin n) :
    a ∈ singleRepeatFibre g k x ↔ ∃ S : Finset (Fin n),
      a ∈ S ∧ S.card=k+1 ∧ (∑ i ∈ S, g i)+g a=x := by
  classical
  simp only [singleRepeatFibre,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Every residue fibre satisfies an implicit binomial bound, uniformly in
both the tuple size and the coin degree. -/
theorem single_repeat_fibre_card_le_choose
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun y : G ↦ 2 • y)) (x : G) :
    (singleRepeatFibre g k x).card ≤
      (n-(singleRepeatFibre g k x).card).choose k := by
  classical
  let R := singleRepeatFibre g k x
  have hex : ∀ a ∈ R, ∃ S : Finset (Fin n),
      a ∈ S ∧ S.card=k+1 ∧ (∑ i ∈ S, g i)+g a=x := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  let S : Fin n → Finset (Fin n) := fun a ↦
    if ha : a ∈ R then Classical.choose (hex a ha) else ∅
  have hp : ∀ a ∈ R, a ∈ S a ∧ (S a).card=k+1 ∧
      (∑ i ∈ S a, g i)+g a=x := by
    intro a ha
    simpa only [S,dif_pos ha] using Classical.choose_spec (hex a ha)
  exact single_repeat_family_card_le_choose g hg hd x R S
    (fun a ha ↦ (hp a ha).1) (fun a ha ↦ (hp a ha).2.1) (fun a ha ↦ (hp a ha).2.2)

/-- The required doubling injectivity holds in every odd cyclic group. -/
theorem single_repeat_fibre_card_le_choose_of_odd
    {n N k : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (x : ZMod N) :
    (singleRepeatFibre g k x).card ≤
      (n-(singleRepeatFibre g k x).card).choose k := by
  apply single_repeat_fibre_card_le_choose g hg
  intro a b he
  apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
  simpa only [nsmul_eq_mul,Nat.cast_ofNat] using he

/-- Finite configurations with one repeated coordinate in a squarefree support. -/
noncomputable def singleRepeatConfigurations (n k : ℕ) :
    Finset (Σ _ : Finset (Fin n), Fin n) := by
  classical
  exact (Finset.univ.powersetCard (k+1)).sigma (fun S ↦ S)

/-- Count configurations before identifying equal residues. -/
theorem single_repeat_configurations_card (n k : ℕ) :
    (singleRepeatConfigurations n k).card = (k+1)*n.choose (k+1) := by
  classical
  rw [singleRepeatConfigurations,Finset.card_sigma]
  have hh : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1), S.card =
      ((Finset.univ : Finset (Fin n)).powersetCard (k+1)).card*(k+1) := by
    apply Finset.sum_const_nat
    intro S hS
    exact (Finset.mem_powersetCard.mp hS).2
  simpa only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,mul_comm] using hh

/-- At a fixed value the repeated coordinate determines the whole configuration. -/
theorem single_repeat_configuration_fibre_card
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (x : ZMod N) :
    ((singleRepeatConfigurations n k).filter
      (fun p ↦ (∑ i ∈ p.1, g i)+g p.2=x)).card = (singleRepeatFibre g k x).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ p.2)
  · intro p hp
    obtain ⟨hp,hx⟩ := Finset.mem_filter.mp hp
    obtain ⟨hS,ha⟩ := Finset.mem_sigma.mp hp
    exact (mem_singleRepeatFibre g x p.2).mpr ⟨p.1,ha,
      (Finset.mem_powersetCard.mp hS).2,hx⟩
  · intro p hp q hq hpq
    rcases p with ⟨S,a⟩
    rcases q with ⟨T,b⟩
    change a=b at hpq
    subst b
    obtain ⟨hp,hpx⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hqx⟩ := Finset.mem_filter.mp hq
    have hS := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp).1).2
    have hT := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hq).1).2
    have he : (∑ i ∈ S, g i) = ∑ i ∈ T, g i :=
      add_right_cancel (hpx.trans hqx.symm)
    have hST : S=T := by
      apply Finset.val_injective
      apply multiset_eq_finset_of_validTuple_card_sum g hg T S.val
      · exact hS.trans hT.symm
      · exact he
    subst T
    rfl
  · intro a ha
    obtain ⟨S,ha,hS,hx⟩ := (mem_singleRepeatFibre g x a).mp ha
    refine ⟨⟨S,a⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hx⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hS⟩,ha⟩

/-- Exact incidence count over residues, for every dimension and coin degree. -/
theorem sum_single_repeat_fibre_card
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) :
    ∑ x : ZMod N, (singleRepeatFibre g k x).card = (k+1)*n.choose (k+1) := by
  classical
  simp_rw [← single_repeat_configuration_fibre_card g hg]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)]
  exact single_repeat_configurations_card n k

/-- An occupied single-repeat fibre is a repeated coin value of degree k+2. -/
theorem mem_repeatedCoinCover_of_single_repeat
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (x : ZMod N)
    (a : Fin n) (ha : a ∈ singleRepeatFibre g k x) :
    x ∈ repeatedCoinCover g (k+2) := by
  classical
  obtain ⟨S,ha,hS,hx⟩ := (mem_singleRepeatFibre g x a).mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,a ::ₘ S.val,?_,?_,?_⟩
  · simp only [Multiset.card_cons,← Finset.card_def,hS]
  · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
      add_comm] using hx
  · intro hn
    exact (Multiset.nodup_cons.mp hn).1 ha

/-- Largest fibre size allowed by the uniform binomial constraint. -/
noncomputable def singleRepeatCapacity (n k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n+1)).filter (fun r ↦ r ≤ (n-r).choose k)).sup id

/-- The implicit bound gives an explicit dimension-dependent capacity. -/
theorem single_repeat_fibre_card_le_capacity
    {n N k : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (x : ZMod N) :
    (singleRepeatFibre g k x).card ≤ singleRepeatCapacity n k := by
  classical
  have hn := Finset.card_le_univ (singleRepeatFibre g k x)
  apply Finset.le_sup (f := id)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_,single_repeat_fibre_card_le_choose_of_odd hN g hg x⟩
  simp only [Fintype.card_fin] at hn
  exact Nat.lt_succ_of_le hn

/-- Global single-repeat counting bound. This is unconditional at odd order;
it does not assert the stronger growth inequality required for G2. -/
theorem single_repeat_incidence_le_capacity_mul_repeated
    {n N k : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    (k+1)*n.choose (k+1) ≤ singleRepeatCapacity n k*(repeatedCoinCover g (k+2)).card := by
  classical
  rw [← sum_single_repeat_fibre_card g hg]
  have he : ∑ x : ZMod N, (singleRepeatFibre g k x).card =
      ∑ x ∈ repeatedCoinCover g (k+2), (singleRepeatFibre g k x).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hx (mem_repeatedCoinCover_of_single_repeat g x a ha)
  rw [he]
  calc
    _ ≤ ∑ _ ∈ repeatedCoinCover g (k+2), singleRepeatCapacity n k :=
      Finset.sum_le_sum (fun x _ ↦ single_repeat_fibre_card_le_capacity hN g hg x)
    _ = _ := by simp [mul_comm]

end MinModulus.Research
