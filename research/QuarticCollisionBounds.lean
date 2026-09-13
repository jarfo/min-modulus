import research.SingleRepeatIncidenceBounds
import research.CoordinateDifferencePacking
import research.TranslatedSquarefreePacking
import research.WeightedProbeCardinality

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A pair of quartic anchors has at most six common pure values when
its doubled difference is not a coordinate difference. -/
theorem quartic_pair_values_card_le_six_of_no_coordinate_difference
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (a b : Fin n) (hab : a ≠ b)
    (Y : Finset G) (hno : ∀ i j, g i+2 • (g a-g b) ≠ g j) :
    (Y.filter (fun x ↦ a ∈ singleRepeatFibre g 2 x ∧
      b ∈ singleRepeatFibre g 2 x)).card ≤ 6 := by
  classical
  let A := (Finset.univ : Finset (Fin n)) \ {a,b}
  let C := A.powersetCard 2
  let D := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hsub : C ⊆ D := by
    intro S hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,(Finset.mem_powersetCard.mp hS).2⟩
  have hfirst := single_repeat_pair_values_card_le_residual_intersection g hg a b hab Y (k := 2)
  have hinter :
      (C.image (fun S ↦ (∑ i ∈ S, g i)+2 • (g a-g b))) ∩
        (C.image (fun S ↦ ∑ i ∈ S, g i)) ⊆
      (D.image (fun S ↦ (∑ i ∈ S, g i)+2 • (g a-g b))) ∩
        (D.image (fun S ↦ ∑ i ∈ S, g i)) :=
    Finset.inter_subset_inter (Finset.image_subset_image hsub) (Finset.image_subset_image hsub)
  exact hfirst.trans ((Finset.card_le_card hinter).trans
    (translated_pair_sum_intersection_card_le_six g hg (2 • (g a-g b)) hno))

/-- If a doubled anchor difference is represented by coordinates p,q,
common quartic pure values have cardinality at most n-3 when p,q avoid
the anchors, and zero otherwise. -/
theorem quartic_pair_values_card_le_of_coordinate_difference
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (a b : Fin n) (hab : a ≠ b)
    (p q : Fin n) (hpq : p ≠ q) (Y : Finset G)
    (he : 2 • (g a-g b)=g p-g q) :
    (Y.filter (fun x ↦ a ∈ singleRepeatFibre g 2 x ∧
      b ∈ singleRepeatFibre g 2 x)).card ≤
      if p ∉ ({a,b} : Finset (Fin n)) ∧ q ∉ ({a,b} : Finset (Fin n))
        then n-3 else 0 := by
  classical
  let A := (Finset.univ : Finset (Fin n)) \ {a,b}
  have hfirst := single_repeat_pair_values_card_le_residual_intersection g hg a b hab Y (k := 2)
  simp only [he] at hfirst
  have hsecond := coordinate_difference_pair_intersection_card_le hinj g hg p q hpq A
  have hcard : A.card=n-2 := by
    simp only [A,Finset.card_sdiff_of_subset (Finset.subset_univ {a,b}),
      Finset.card_univ,Fintype.card_fin,Finset.card_pair hab]
  have hbound := hfirst.trans hsecond
  simp only [hcard,A,Finset.mem_sdiff,Finset.mem_univ,true_and,Nat.sub_sub,
    Nat.reduceAdd] at hbound
  exact hbound

/-- Unordered anchor pairs whose doubled difference is represented by
two distinct coordinates outside the pair. -/
noncomputable def disjointDoubledDifferencePairs
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
    (fun P ↦ ∃ a b p q : Fin n, a ∈ P ∧ b ∈ P ∧ a ≠ b ∧
      p ∉ P ∧ q ∉ P ∧ p ≠ q ∧ 2 • (g a-g b)=g p-g q)

/-- Only disjointly represented doubled differences require the n-3
quartic collision cap; all other anchor pairs have the six-point cap. -/
theorem quartic_anchor_pair_values_card_le_exceptional
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (P : Finset (Fin n)) (hP : P.card=2)
    (Y : Finset G) :
    (Y.filter (fun x ↦ P ⊆ singleRepeatFibre g 2 x)).card ≤
      if P ∈ disjointDoubledDifferencePairs g then n-3 else 6 := by
  classical
  by_cases hE : P ∈ disjointDoubledDifferencePairs g
  · rw [if_pos hE]
    obtain ⟨a,b,p,q,ha,hb,hab,hp,hq,hpq,he⟩ := (Finset.mem_filter.mp hE).2
    have hpair : P={a,b} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
      · simpa only [Finset.card_pair hab,hP] using (Nat.le_refl 2)
    have hbound := quartic_pair_values_card_le_of_coordinate_difference
      hinj g hg a b hab p q hpq Y he
    rw [if_pos ⟨by simpa only [← hpair] using hp,by simpa only [← hpair] using hq⟩] at hbound
    simpa only [hpair,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hbound
  · rw [if_neg hE]
    obtain ⟨a,b,hab,hpair⟩ := Finset.card_eq_two.mp hP
    have hnonzero : 2 • (g a-g b) ≠ 0 := by
      intro hz
      have hh : (g a-g b)+(g a-g b)=(0 : G)+0 := by
        simpa only [two_nsmul,zero_add] using hz
      exact hab (validTuple_injective g hg (sub_eq_zero.mp (hinj _ _ hh)))
    by_cases hrep : ∃ p q : Fin n, 2 • (g a-g b)=g p-g q
    · obtain ⟨p,q,he⟩ := hrep
      have hpq : p ≠ q := by intro h; exact hnonzero (by simpa only [h,sub_self] using he)
      have hmiss : ¬ (p ∉ ({a,b} : Finset (Fin n)) ∧ q ∉ ({a,b} : Finset (Fin n))) := by
        intro h
        apply hE
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hP⟩,
          a,b,p,q,?_,?_,hab,?_,?_,hpq,he⟩
        · rw [hpair]; simp
        · rw [hpair]; simp
        · simpa only [hpair] using h.1
        · simpa only [hpair] using h.2
      have hbound := quartic_pair_values_card_le_of_coordinate_difference
        hinj g hg a b hab p q hpq Y he
      rw [if_neg hmiss] at hbound
      have hbound' := hbound.trans (by decide : 0 ≤ 6)
      simpa only [hpair,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hbound'
    · have hno : ∀ i j, g i+2 • (g a-g b) ≠ g j := by
        intro i j he
        apply hrep
        refine ⟨j,i,?_⟩
        apply eq_sub_iff_add_eq.mpr
        simpa only [add_comm] using he
      have hbound := quartic_pair_values_card_le_six_of_no_coordinate_difference g hg a b hab Y hno
      simpa only [hpair,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hbound

/-- The global quartic pair-collision count is controlled by the number
of disjointly represented doubled differences, uniformly for n>=9. -/
theorem quartic_pair_collision_sum_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (hn : 9 ≤ n) (Y : Finset G) :
    (∑ x ∈ Y, ((singleRepeatFibre g 2 x).card).choose 2) ≤
      6*n.choose 2+(n-9)*(disjointDoubledDifferencePairs g).card := by
  classical
  let F := (Finset.univ : Finset (Fin n)).powersetCard 2
  let C := disjointDoubledDifferencePairs g
  have hCF : C ⊆ F := fun P hP ↦ (Finset.mem_filter.mp hP).1
  have hpos : F.filter (fun P ↦ P ∈ C)=C := by
    ext P
    constructor
    · intro h; exact (Finset.mem_filter.mp h).2
    · intro h; exact Finset.mem_filter.mpr ⟨hCF h,h⟩
  have hneg : F.filter (fun P ↦ P ∉ C)=F \ C := by
    ext P
    simp only [Finset.mem_filter,Finset.mem_sdiff]
  have hsum : (∑ P ∈ F, (if P ∈ C then n-3 else 6)) =
      (n-3)*C.card+6*(F \ C).card := by
    rw [Finset.sum_ite,hpos,hneg]
    simp only [Finset.sum_const,smul_eq_mul]
    ring
  have htotal : C.card+(F \ C).card=F.card := by
    rw [Finset.card_sdiff_of_subset hCF]
    have h := Finset.card_le_card hCF
    omega
  have hFc : F.card=n.choose 2 := by
    simp only [F,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  have hdiff : n-3=(n-9)+6 := by omega
  calc
    _ = ∑ P ∈ F, (Y.filter (fun x ↦ P ⊆ singleRepeatFibre g 2 x)).card :=
      single_repeat_pair_collisions_eq_sum_anchor_pairs g Y
    _ ≤ ∑ P ∈ F, (if P ∈ C then n-3 else 6) := by
      apply Finset.sum_le_sum
      intro P hP
      exact quartic_anchor_pair_values_card_le_exceptional hinj g hg P
        (Finset.mem_powersetCard.mp hP).2 Y
    _ = (n-3)*C.card+6*(F \ C).card := hsum
    _ = (n-9)*C.card+6*(C.card+(F \ C).card) := by rw [hdiff]; ring
    _ = _ := by rw [htotal,hFc]; ring

/-- Sparse disjoint doubled differences suffice for the cubic number of
quartic values outside the doubled two-coin cover. The sparsity hypothesis
is explicit and is not asserted for arbitrary valid tuples. -/
theorem quartic_outside_doubled_cover_card_of_sparse_differences
    {n N : ℕ} [NeZero N] (hn : 14 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsparse : 3*(n-9)*(disjointDoubledDifferencePairs g).card ≤
      2*(n-14)*n.choose 2) :
    n.choose 3 ≤ ((repeatedCoinCover g 4) \
      (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)).card := by
  classical
  let E := (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)
  have hinj : ∀ u v : ZMod N, u+u=v+v → u=v := by
    intro u v he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [Nat.cast_ofNat,two_mul] using he
  have hlo := single_repeat_outside_doubled_cover_pair_collision_bound (k := 1)
    (by decide) hN g hg
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at hlo
  have hhi := quartic_pair_collision_sum_le hinj g hg (by omega) Eᶜ
  have hcombined := hlo.trans (Nat.add_le_add_left hhi
    (((repeatedCoinCover g 4) \ E).card))
  have hfour : n-4+4=n := by omega
  have hnine : n-9+9=n := by omega
  have hfourteen : n-14+14=n := by omega
  have htwo : n-2+2=n := by omega
  have hchoose := Nat.choose_succ_right_eq n 2
  change n.choose 3*3=n.choose 2*(n-2) at hchoose
  change n.choose 3 ≤ ((repeatedCoinCover g 4) \ E).card
  nlinarith

/-- The absolute quartic repeated-sum lower bound holds whenever the
explicit disjoint doubled-difference sparsity inequality holds. -/
theorem absolute_quartic_bound_of_sparse_differences
    {n N : ℕ} [NeZero N] (hn : 14 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsparse : 3*(n-9)*(disjointDoubledDifferencePairs g).card ≤
      2*(n-14)*n.choose 2) :
    (n+1).choose 2+n.choose 3 ≤ (repeatedCoinCover g 4).card := by
  classical
  let E := (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)
  have hsub : E ⊆ repeatedCoinCover g 4 :=
    doubled_coin_cover_subset_repeated_coin_cover (k := 2) (by decide) g
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro a b he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using he
  have hE : E.card=(n+1).choose 2 := by
    rw [Finset.card_image_of_injective _ hd,two_coin_card_eq_of_odd hN g hg]
  have hout := quartic_outside_doubled_cover_card_of_sparse_differences hn hN g hg hsparse
  change n.choose 3 ≤ ((repeatedCoinCover g 4) \ E).card at hout
  rw [Finset.card_sdiff_of_subset hsub] at hout
  have hcard := Finset.card_le_card hsub
  omega

end MinModulus.Research
