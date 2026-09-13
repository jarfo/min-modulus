import research.SingleRepeatProbes

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Doubling every positive-degree coin sum produces a repeated coin sum. -/
theorem doubled_coin_cover_subset_repeated_coin_cover
    {n N k : ℕ} [NeZero N] (hk : 1 ≤ k) (g : Fin n → ZMod N) :
    (actualFibreCoinCover g k).image (fun x ↦ 2 • x) ⊆ repeatedCoinCover g (2*k) := by
  classical
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,s+s,?_,?_,?_⟩
  · simp [hc,two_mul]
  · simp only [Multiset.map_add,Multiset.sum_add,hs,two_nsmul]
  · intro hn
    have hz : s=0 := disjoint_self.mp (Multiset.nodup_add.mp hn).2.2
    simp only [hz,Multiset.card_zero] at hc
    omega

/-- Probes in degree d are supported on repeated coin values of degree d+1. -/
theorem single_repeat_probe_eq_zero_outside_repeated
    {n N d : ℕ} [NeZero N] {K : Type*} [AddCommMonoid K]
    (g : Fin n → ZMod N) (a b : Fin n) (y : ZMod N)
    (hy : y ∉ repeatedCoinCover g (d+1)) (f : Finset (Fin n) → K) :
    singleRepeatProbe g d a b y f=0 := by
  classical
  unfold singleRepeatProbe
  apply Finset.sum_eq_zero
  intro T hT
  split_ifs with h
  · exfalso
    apply hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,a ::ₘ a ::ₘ (T.erase b).val,?_,?_,?_⟩
    · simp only [Multiset.card_cons,← Finset.card_def]
      have hc := (Finset.mem_powersetCard.mp hT).2
      have he := Finset.card_erase_add_one h.1
      omega
    · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
        two_nsmul,add_assoc] using h.2
    · simp
  · rfl

/-- A fixed matrix combines all anchor/removal probes at each value. -/
noncomputable def weightedSingleRepeatProbe
    {n N : ℕ} [NeZero N] {K : Type*} [Semiring K]
    (g : Fin n → ZMod N) (d : ℕ) (M : Fin n → Fin n → K)
    (y : ZMod N) (f : Finset (Fin n) → K) : K :=
  ∑ a, ∑ b, M a b * singleRepeatProbe g d a b y f

/-- In every even degree, one coefficient-preserving probe combination
outside the doubled half-degree cover forces the corresponding cardinality
increment. No validity assumption is needed for this counting implication. -/
theorem even_degree_card_bound_of_weighted_probe_injective
    {n N k : ℕ} [NeZero N] {K : Type*} [Semiring K] [Fintype K] [Nontrivial K]
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
  let encode (f : S → K) (y : E) : K :=
    weightedSingleRepeatProbe g (2*k+1) M y.val (extend f)
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
  have hcount := Fintype.card_le_of_injective encode hi
  simp only [Fintype.card_fun,Fintype.card_coe] at hcount
  have hSE : S.card ≤ E.card :=
    (Nat.pow_le_pow_iff_right (Fintype.one_lt_card : 1 < Fintype.card K)).mp hcount
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
Over a finite field the hypothesis is the concrete full-column-rank target. -/
theorem absolute_quartic_bound_of_weighted_probe_injective
    {n N : ℕ} [NeZero N] {K : Type*} [Semiring K] [Fintype K] [Nontrivial K]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (M : Fin n → Fin n → K)
    (hdecode : ∀ f h : Finset (Fin n) → K,
      (∀ y : ZMod N, y ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x) →
        weightedSingleRepeatProbe g 3 M y f=weightedSingleRepeatProbe g 3 M y h) →
      ∀ T : Finset (Fin n), T.card=3 → f T=h T) :
    (n+1).choose 2+n.choose 3 ≤ (repeatedCoinCover g 4).card := by
  have h := even_degree_card_bound_of_weighted_probe_injective (k := 1) hN g M hdecode
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at h
  rwa [two_coin_card_eq_of_odd hN g hg] at h

end MinModulus.Research
