import MinModulus.SeparatedPairLayerCounts

namespace MinModulus
open Finset
open scoped Classical

/-- Validity determines every same-size multiset replacement of a subset
exactly, including repetitions of coordinates already in that subset. -/
theorem multiset_eq_finset_of_validTuple_card_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (S : Finset (Fin n)) (t : Multiset (Fin n)) (htcard : t.card=S.card)
    (htsum : (t.map g).sum=∑ i ∈ S, g i) : t=S.val := by
  classical
  let R := Sᶜ
  let v := R.val+t
  have hcard : v.card=n := by
    simp only [v,Multiset.card_add,htcard]
    have hh := Finset.card_compl_add_card S
    simpa only [R,Finset.card_def,Fintype.card_fin] using hh
  have hsum : (v.map g).sum=∑ i, g i := by
    rw [Multiset.map_add,Multiset.sum_add,htsum]
    simpa only [R,Finset.sum_eq_multiset_sum] using Finset.sum_compl_add_sum S g
  ext i
  have hc := multiset_count_eq_one_of_validTuple g hg v hcard hsum i
  simp only [v,Multiset.count_add] at hc
  by_cases hi : i ∈ S
  · have hs := Multiset.count_eq_one_of_mem S.nodup hi
    have hr : R.val.count i=0 := Multiset.count_eq_zero.mpr (by simpa [R] using hi)
    omega
  · have hs : S.val.count i=0 := Multiset.count_eq_zero.mpr hi
    have hr := Multiset.count_eq_one_of_mem R.nodup (by simpa [R] using hi : i ∈ R.val)
    omega

/-- Contracting a repeated coordinate along an actual affine doubling
edge in a one-extra representation recovers the original subset exactly. -/
theorem one_extra_double_contraction_eq_subset
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (R : Multiset (Fin n)) (i j : Fin n)
    (hcard : R.card+1=S.card)
    (he : ((i ::ₘ i ::ₘ R).map (fun a ↦ g a+b)).sum=∑ a ∈ S, (g a+b))
    (hd : g j=2 • g i+b) : j ::ₘ R=S.val := by
  have hv : ValidTuple (fun a ↦ g a+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  apply multiset_eq_finset_of_validTuple_card_sum (fun a ↦ g a+b) hv S (j ::ₘ R)
    (by simpa only [Multiset.card_cons] using hcard)
  have hq : g j+b=(g i+b)+(g i+b) := by rw [hd,two_nsmul]; abel
  rw [Multiset.map_cons,Multiset.sum_cons,hq]
  simpa only [Multiset.map_cons,Multiset.sum_cons,add_assoc] using he

/-- If a one-extra representation has another repeated coordinate, each
selected repeated coordinate must escape the tuple under affine doubling. -/
theorem no_affine_double_target_of_one_extra_other_repetition
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (R : Multiset (Fin n)) (i k : Fin n)
    (hcard : R.card+1=S.card)
    (he : ((i ::ₘ i ::ₘ R).map (fun a ↦ g a+b)).sum=∑ a ∈ S, (g a+b))
    (hk : 2 ≤ R.count k) : ∀ j, g j ≠ 2 • g i+b := by
  intro j hj
  have h := one_extra_double_contraction_eq_subset g hg b S R i j hcard he hj
  have hkR : k ∈ R := Multiset.count_pos.mp (by omega)
  have hkS : k ∈ S := by
    have hm : k ∈ j ::ₘ R := Multiset.mem_cons.mpr (Or.inr hkR)
    rwa [h] at hm
  have hc := congrArg (Multiset.count k) h
  have hs := Multiset.count_eq_one_of_mem S.nodup hkS
  simp only [Multiset.count_cons] at hc
  split_ifs at hc <;> omega

/-- A one-short equal-sum representation cannot contain a coordinate
with any affine doubling predecessor in the original tuple. -/
theorem no_affine_predecessor_of_one_short_representation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (R : Multiset (Fin n)) (j : Fin n)
    (hcard : R.card+2=S.card)
    (he : ((j ::ₘ R).map (fun a ↦ g a+b)).sum=∑ a ∈ S, (g a+b)) :
    ∀ i, g j ≠ 2 • g i+b := by
  intro i hd
  have hv : ValidTuple (fun a ↦ g a+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  have hq : g j+b=(g i+b)+(g i+b) := by rw [hd,two_nsmul]; abel
  have h : i ::ₘ i ::ₘ R=S.val := by
    apply multiset_eq_finset_of_validTuple_card_sum (fun a ↦ g a+b) hv S (i ::ₘ i ::ₘ R)
      (by simpa only [Multiset.card_cons,add_assoc] using hcard)
    simpa only [Multiset.map_cons,Multiset.sum_cons,hq,add_assoc] using he
  have hn := S.nodup
  rw [← h] at hn
  simp at hn

/-- Every coordinate on the smaller side of a unit-gap collision is a
root of the full affine doubling graph, even before cancelling common coordinates. -/
theorem unit_gap_negative_side_has_no_affine_predecessor
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V : Finset (Fin n)) (hcard : U.card=V.card+1)
    (he : (∑ a ∈ U, (g a+b))=(∑ a ∈ V, (g a+b))) :
    ∀ j ∈ V, ∀ i, g j ≠ 2 • g i+b := by
  intro j hj
  apply no_affine_predecessor_of_one_short_representation g hg b U (V.val.erase j) j
  · have h := Multiset.card_erase_add_one hj
    change (V.val.erase j).card+2=U.card
    change (V.val.erase j).card+1=V.card at h
    omega
  · rw [Multiset.cons_erase hj]
    exact he.symm

end MinModulus
