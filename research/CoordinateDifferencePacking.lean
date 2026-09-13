import MinModulus.TriplingClosure
import research.RepeatedCoinGrowth

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- In a disjoint translated match of degree at least two, validity forces
both endpoints of a coordinate-difference shift into their own sides. -/
theorem coordinate_difference_disjoint_match_anchors_mem
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n)
    (S T : Finset (Fin n)) (hc : S.card = T.card) (hS : 2 ≤ S.card)
    (hd : Disjoint S T)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    p ∈ S ∧ q ∈ T := by
  classical
  have anchor (a b : Fin n) (U V : Finset (Fin n))
      (hcard : U.card = V.card) (hlarge : 2 ≤ U.card) (hdis : Disjoint U V)
      (hv : (∑ i ∈ U, g i) + g a = (∑ i ∈ V, g i) + g b) : a ∈ U := by
    by_contra ha
    have hm : b ::ₘ V.val = (insert a U).val := by
      apply multiset_eq_finset_of_validTuple_card_sum g hg (insert a U) _
      · simp only [Multiset.card_cons,← Finset.card_def,Finset.card_insert_of_notMem ha]
        omega
      · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
          Finset.sum_insert ha,add_comm] using hv.symm
    have hsub : V ⊆ ({a} : Finset (Fin n)) := by
      intro c hcV
      have hm' : c ∈ b ::ₘ V.val := Multiset.mem_cons_of_mem hcV
      rw [hm] at hm'
      rcases Finset.mem_insert.mp hm' with hca | hcU
      · exact Finset.mem_singleton.mpr hca
      · exact False.elim (Finset.disjoint_left.mp hdis hcU hcV)
    have h := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at h
    omega
  exact ⟨anchor p q S T hc hS hd he,
    anchor q p T S hc.symm (by omega) hd.symm he.symm⟩

/-- Overlapping pair supports shifted by a nonzero coordinate difference
are exactly the common-coordinate matches {q,c} and {p,c}. -/
theorem coordinate_difference_overlapping_pair_match
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hS : S.card = 2) (hT : T.card = 2)
    (hd : ¬ Disjoint S T)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    ∃ c, c ≠ p ∧ c ≠ q ∧ S = {q,c} ∧ T = {p,c} := by
  classical
  obtain ⟨c,hcS,hcT⟩ := Finset.not_disjoint_iff.mp hd
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (show (S.erase c).card = 1 by
    have := Finset.card_erase_add_one hcS; omega)
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (show (T.erase c).card = 1 by
    have := Finset.card_erase_add_one hcT; omega)
  have hs : (∑ i ∈ S, g i) = g a + g c := by
    rw [← Finset.sum_erase_add S g hcS,ha,Finset.sum_singleton]
  have ht : (∑ i ∈ T, g i) = g b + g c := by
    rw [← Finset.sum_erase_add T g hcT,hb,Finset.sum_singleton]
  have he' : g a + g p = g b + g q := by
    apply add_right_cancel (b := g c)
    calc
      g a + g p + g c = (∑ i ∈ S, g i) + g p := by rw [hs]; abel
      _ = (∑ i ∈ T, g i) + g q := he
      _ = g b + g q + g c := by rw [ht]; abel
  have hdif : g p - g q = g b - g a := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using he'
  obtain ⟨hpb,hqa⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg p q b a hpq hdif
  subst a; subst b
  have hcp : c ≠ p := by
    intro h; subst p
    have := Finset.notMem_erase c T
    rw [hb] at this
    exact this (Finset.mem_singleton_self c)
  have hcq : c ≠ q := by
    intro h; subst q
    have := Finset.notMem_erase c S
    rw [ha] at this
    exact this (Finset.mem_singleton_self c)
  refine ⟨c,hcp,hcq,?_,?_⟩
  · calc S = insert c (S.erase c) := (Finset.insert_erase hcS).symm
         _ = {q,c} := by rw [ha,Finset.pair_comm]
  · calc T = insert c (T.erase c) := (Finset.insert_erase hcT).symm
         _ = {p,c} := by rw [hb,Finset.pair_comm]

/-- A nonzero coordinate-difference shift admits at most one disjoint
match between squarefree pair supports. -/
theorem coordinate_difference_disjoint_pair_matches_eq
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T U V : Finset (Fin n))
    (hS : S.card = 2) (hT : T.card = 2) (hU : U.card = 2) (hV : V.card = 2)
    (hdST : Disjoint S T) (hdUV : Disjoint U V)
    (heST : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q)
    (heUV : (∑ i ∈ U, g i) + g p = (∑ i ∈ V, g i) + g q) :
    S = U ∧ T = V := by
  classical
  obtain ⟨hpS,hqT⟩ := coordinate_difference_disjoint_match_anchors_mem g hg p q S T
    (hS.trans hT.symm) (by omega) hdST heST
  obtain ⟨hpU,hqV⟩ := coordinate_difference_disjoint_match_anchors_mem g hg p q U V
    (hU.trans hV.symm) (by omega) hdUV heUV
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (show (S.erase p).card = 1 by
    have := Finset.card_erase_add_one hpS; omega)
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (show (T.erase q).card = 1 by
    have := Finset.card_erase_add_one hqT; omega)
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (show (U.erase p).card = 1 by
    have := Finset.card_erase_add_one hpU; omega)
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp (show (V.erase q).card = 1 by
    have := Finset.card_erase_add_one hqV; omega)
  have residual (A B : Finset (Fin n)) (hpA : p ∈ A) (hqB : q ∈ B)
      (a b : Fin n) (ha : A.erase p = {a}) (hb : B.erase q = {b})
      (he : (∑ i ∈ A, g i) + g p = (∑ i ∈ B, g i) + g q) :
      g a - g b = (g q+g q) - (g p+g p) := by
    have hs : (∑ i ∈ A, g i) = g a + g p := by
      rw [← Finset.sum_erase_add A g hpA,ha,Finset.sum_singleton]
    have ht : (∑ i ∈ B, g i) = g b + g q := by
      rw [← Finset.sum_erase_add B g hqB,hb,Finset.sum_singleton]
    apply sub_eq_sub_iff_add_eq_add.mpr
    calc
      g a + (g p+g p) = (∑ i ∈ A, g i) + g p := by rw [hs]; abel
      _ = (∑ i ∈ B, g i) + g q := he
      _ = (g q+g q) + g b := by rw [ht]; abel
  have hab := residual S T hpS hqT a b ha hb heST
  have hcd := residual U V hpU hqV c d hc hd heUV
  have hne : a ≠ b := by
    intro h
    have hz : g q+g q = g p+g p := sub_eq_zero.mp (by simpa only [h,sub_self] using hab.symm)
    exact hpq (validTuple_injective g hg (hinj _ _ hz).symm)
  obtain ⟨hac,hbd⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg a b c d hne (hab.trans hcd.symm)
  subst c; subst d
  constructor
  · calc S = insert p (S.erase p) := (Finset.insert_erase hpS).symm
         _ = insert p (U.erase p) := by rw [ha,hc]
         _ = U := Finset.insert_erase hpU
  · calc T = insert q (T.erase q) := (Finset.insert_erase hqT).symm
         _ = insert q (V.erase q) := by rw [hb,hd]
         _ = V := Finset.insert_erase hqV

/-- A coordinate-difference match always uses both difference endpoints. -/
theorem coordinate_difference_pair_match_endpoints_mem
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hS : S.card = 2) (hT : T.card = 2)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    p ∈ S ∪ T ∧ q ∈ S ∪ T := by
  by_cases hd : Disjoint S T
  · have h := coordinate_difference_disjoint_match_anchors_mem g hg p q S T
      (hS.trans hT.symm) (by omega) hd he
    exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_right _ h.2⟩
  · obtain ⟨c,_,_,rfl,rfl⟩ := coordinate_difference_overlapping_pair_match hinj g hg p q hpq S T hS hT hd he
    simp

/-- On an allowed coordinate set A, a nonzero coordinate-difference shift
has at most |A|-1 pair-support matches; it has none if an endpoint is absent. -/
theorem coordinate_difference_pair_family_card_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hc : ∀ uv ∈ F, uv.1.card = 2 ∧ uv.2.card = 2)
    (hsub : ∀ uv ∈ F, uv.1 ⊆ A ∧ uv.2 ⊆ A)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.1, g i) + g p = (∑ i ∈ uv.2, g i) + g q) :
    F.card ≤ if p ∈ A ∧ q ∈ A then A.card - 1 else 0 := by
  classical
  by_cases hmem : p ∈ A ∧ q ∈ A
  · rw [if_pos hmem]
    let H := F.filter (fun uv ↦ Disjoint uv.1 uv.2)
    let K := F.filter (fun uv ↦ ¬ Disjoint uv.1 uv.2)
    have hH : H.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro uv huv pq hpq'
      obtain ⟨huv,hd⟩ := Finset.mem_filter.mp huv
      obtain ⟨hpq',hd'⟩ := Finset.mem_filter.mp hpq'
      have h := coordinate_difference_disjoint_pair_matches_eq hinj g hg p q hpq
        uv.1 uv.2 pq.1 pq.2 (hc uv huv).1 (hc uv huv).2
        (hc pq hpq').1 (hc pq hpq').2 hd hd' (hv uv huv) (hv pq hpq')
      exact Prod.ext h.1 h.2
    have hKsub : K ⊆ (A \ {p,q}).image (fun c ↦ (({q,c} : Finset (Fin n)),({p,c} : Finset (Fin n)))) := by
      intro uv huv
      obtain ⟨huv,hd⟩ := Finset.mem_filter.mp huv
      obtain ⟨c,hcp,hcq,hS,hT⟩ := coordinate_difference_overlapping_pair_match hinj g hg p q hpq
        uv.1 uv.2 (hc uv huv).1 (hc uv huv).2 hd (hv uv huv)
      have hcA : c ∈ A := (hsub uv huv).1 (by rw [hS]; simp)
      refine Finset.mem_image.mpr ⟨c,Finset.mem_sdiff.mpr ⟨hcA,?_⟩,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨hcp,hcq⟩
      · exact Prod.ext hS.symm hT.symm
    have hpqA : ({p,q} : Finset (Fin n)) ⊆ A := by
      intro i hi
      rcases Finset.mem_insert.mp hi with h | h
      · exact h.symm ▸ hmem.1
      · exact (Finset.mem_singleton.mp h).symm ▸ hmem.2
    have hK : K.card ≤ A.card - 2 := by
      have h := (Finset.card_le_card hKsub).trans Finset.card_image_le
      simpa only [Finset.card_sdiff_of_subset hpqA,Finset.card_pair hpq] using h
    have hA : 2 ≤ A.card := by
      have h := Finset.card_le_card hpqA
      simpa only [Finset.card_pair hpq] using h
    have htotal : H.card + K.card = F.card := Finset.card_filter_add_card_filter_not (s := F) (fun uv ↦ Disjoint uv.1 uv.2)
    omega
  · rw [if_neg hmem]
    have hempty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro uv huv
      obtain ⟨hp,hq⟩ := coordinate_difference_pair_match_endpoints_mem hinj g hg p q hpq
        uv.1 uv.2 (hc uv huv).1 (hc uv huv).2 (hv uv huv)
      have hUA : uv.1 ∪ uv.2 ⊆ A := Finset.union_subset (hsub uv huv).1 (hsub uv huv).2
      exact hmem ⟨hUA hp,hUA hq⟩
    simp [hempty]

/-- Restricted squarefree pair-sum sets have a linear intersection
bound for coordinate-difference shifts, and zero intersection if an
endpoint of the difference is missing from the allowed coordinates. -/
theorem coordinate_difference_pair_intersection_card_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) :
    let C := A.powersetCard 2
    ((C.image (fun S ↦ (∑ i ∈ S, g i) + (g p - g q))) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i))).card ≤
      if p ∈ A ∧ q ∈ A then A.card - 1 else 0 := by
  classical
  intro C
  let F := (C.product C).filter (fun uv ↦ (∑ i ∈ uv.1, g i) + g p = (∑ i ∈ uv.2, g i) + g q)
  have hc : ∀ uv ∈ F, uv.1.card = 2 ∧ uv.2.card = 2 := by
    intro uv huv
    have h := Finset.mem_product.mp (Finset.mem_filter.mp huv).1
    exact ⟨(Finset.mem_powersetCard.mp h.1).2,(Finset.mem_powersetCard.mp h.2).2⟩
  have hs : ∀ uv ∈ F, uv.1 ⊆ A ∧ uv.2 ⊆ A := by
    intro uv huv
    have h := Finset.mem_product.mp (Finset.mem_filter.mp huv).1
    exact ⟨(Finset.mem_powersetCard.mp h.1).1,(Finset.mem_powersetCard.mp h.2).1⟩
  have hv : ∀ uv ∈ F, (∑ i ∈ uv.1, g i) + g p = (∑ i ∈ uv.2, g i) + g q := by
    intro uv huv
    exact (Finset.mem_filter.mp huv).2
  have hsub : (C.image (fun S ↦ (∑ i ∈ S, g i) + (g p-g q))) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i)) ⊆ F.image (fun uv ↦ ∑ i ∈ uv.2, g i) := by
    intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
    obtain ⟨T,hT,hTx⟩ := Finset.mem_image.mp hy
    have he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q := by
      calc
        (∑ i ∈ S, g i) + g p = ((∑ i ∈ S, g i) + (g p-g q)) + g q := by abel
        _ = (∑ i ∈ T, g i) + g q := congrArg (fun y ↦ y + g q) (hSx.trans hTx.symm)
    exact Finset.mem_image.mpr ⟨(S,T),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hS,hT⟩,he⟩,hTx⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (coordinate_difference_pair_family_card_le hinj g hg p q hpq A F hc hs hv))

end MinModulus.Research
