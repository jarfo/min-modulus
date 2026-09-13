import research.SingleRepeatFibres

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- If the first difference endpoint is absent from its own side, a
coordinate-difference match replaces the opposite endpoint and keeps
all other coordinates. This holds in every degree and needs no doubling
injectivity. -/
theorem coordinate_difference_match_normal_form
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hc : S.card = T.card) (hpS : p ∉ S)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    q ∈ S ∧ q ∉ T ∧ p ∈ T ∧
      T = insert p (S.erase q) := by
  classical
  have hm : q ::ₘ T.val = (insert p S).val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg (insert p S) _
    · simp only [Multiset.card_cons,← Finset.card_def,Finset.card_insert_of_notMem hpS]
      omega
    · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
        Finset.sum_insert hpS,add_comm] using he.symm
  have hn : (q ::ₘ T.val).Nodup := hm.symm ▸ (insert p S).nodup
  have hqT : q ∉ T := (Multiset.nodup_cons.mp hn).1
  have hmem (i : Fin n) : i = q ∨ i ∈ T ↔ i = p ∨ i ∈ S := by
    have h := congrArg (fun U : Multiset (Fin n) ↦ i ∈ U) hm
    simpa only [Multiset.mem_cons,Finset.mem_val,Finset.mem_insert] using (Iff.of_eq h)
  have hqS : q ∈ S := ((hmem q).mp (Or.inl rfl)).resolve_left hpq.symm
  have hpT : p ∈ T := ((hmem p).mpr (Or.inl rfl)).resolve_left hpq
  refine ⟨hqS,hqT,hpT,?_⟩
  ext i
  constructor
  · intro hi
    rcases (hmem i).mp (Or.inr hi) with hip | hiS
    · exact Finset.mem_insert.mpr (Or.inl hip)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by intro h; subst i; exact hqT hi,hiS⟩)
  · intro hi
    rcases Finset.mem_insert.mp hi with hip | hi
    · exact hip.symm ▸ hpT
    · have h := Finset.mem_erase.mp hi
      exact ((hmem i).mpr (Or.inr h.2)).resolve_left h.1

/-- If the first difference endpoint is present in its own side, both
endpoints are present only on their own sides. Erasing them doubles
the shift and lowers the common degree by one. -/
theorem coordinate_difference_match_repeated_form
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hc : S.card = T.card) (hpS : p ∈ S)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    q ∈ T ∧ q ∉ S ∧ p ∉ T ∧
      (∑ i ∈ S.erase p, g i) + 2 • g p =
        (∑ i ∈ T.erase q, g i) + 2 • g q := by
  classical
  have hqT : q ∈ T := by
    by_contra hq
    have hm : p ::ₘ S.val = (insert q T).val := by
      apply multiset_eq_finset_of_validTuple_card_sum g hg (insert q T) _
      · simp only [Multiset.card_cons,← Finset.card_def,Finset.card_insert_of_notMem hq]
        omega
      · simpa only [Multiset.map_cons,Multiset.sum_cons,← Finset.sum_eq_multiset_sum,
          Finset.sum_insert hq,add_comm] using he
    have hn : (p ::ₘ S.val).Nodup := hm.symm ▸ (insert q T).nodup
    exact (Multiset.nodup_cons.mp hn).1 hpS
  have hqS := single_repeat_support_avoids_other_anchor g hg p q hpq S T hpS hc he
  have hpT := single_repeat_support_avoids_other_anchor g hg q p hpq.symm T S hqT hc.symm he.symm
  refine ⟨hqT,hqS,hpT,?_⟩
  calc
    (∑ i ∈ S.erase p, g i) + 2 • g p = (∑ i ∈ S, g i) + g p := by
      rw [← Finset.sum_erase_add S g hpS,two_nsmul]; abel
    _ = (∑ i ∈ T, g i) + g q := he
    _ = (∑ i ∈ T.erase q, g i) + 2 • g q := by
      rw [← Finset.sum_erase_add T g hqT,two_nsmul]; abel

/-- Every equal-degree squarefree match for a nonzero coordinate difference
uses both difference endpoints, without any assumption on doubling. -/
theorem coordinate_difference_match_endpoints_mem_any_degree
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hc : S.card = T.card)
    (he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q) :
    p ∈ S ∪ T ∧ q ∈ S ∪ T := by
  by_cases hpS : p ∈ S
  · have h := coordinate_difference_match_repeated_form g hg p q hpq S T hc hpS he
    exact ⟨Finset.mem_union_left _ hpS,Finset.mem_union_right _ h.1⟩
  · have h := coordinate_difference_match_normal_form g hg p q hpq S T hc hpS he
    exact ⟨Finset.mem_union_right _ h.2.2.1,Finset.mem_union_left _ h.1⟩

/-- Excluding a difference endpoint makes every equal-degree squarefree
translation intersection empty, without any hypothesis on doubling. -/
theorem coordinate_difference_intersection_eq_empty_of_endpoint_missing
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (hmissing : p ∉ A ∨ q ∉ A) :
    let C := A.powersetCard k
    (C.image (fun S ↦ (∑ i ∈ S, g i) + (g p-g q))) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i)) = ∅ := by
  classical
  intro C
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hx
  obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
  obtain ⟨T,hT,hTx⟩ := Finset.mem_image.mp hy
  obtain ⟨hSA,hSc⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨hTA,hTc⟩ := Finset.mem_powersetCard.mp hT
  have he : (∑ i ∈ S, g i) + g p = (∑ i ∈ T, g i) + g q := by
    calc
      (∑ i ∈ S, g i) + g p = ((∑ i ∈ S, g i) + (g p-g q)) + g q := by abel
      _ = (∑ i ∈ T, g i) + g q := congrArg (fun y ↦ y+g q) (hSx.trans hTx.symm)
  obtain ⟨hp,hq⟩ := coordinate_difference_match_endpoints_mem_any_degree g hg p q hpq
    S T (hSc.trans hTc.symm) he
  have hU : S ∪ T ⊆ A := Finset.union_subset hSA hTA
  exact hmissing.elim (fun h ↦ h (hU hp)) (fun h ↦ h (hU hq))

/-- Pairs of equal-degree squarefree supports whose sums differ by `t`. -/
noncomputable def squarefreeTranslationMatches
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (k : ℕ) (t : G) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((A.powersetCard k).product (A.powersetCard k)).filter
    (fun uv ↦ (∑ i ∈ uv.1, g i) + t = ∑ i ∈ uv.2, g i)

theorem mem_squarefreeTranslationMatches
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A S T : Finset (Fin n)) (t : G) :
    (S,T) ∈ squarefreeTranslationMatches g A k t ↔
      S ⊆ A ∧ S.card = k ∧ T ⊆ A ∧ T.card = k ∧
        (∑ i ∈ S, g i) + t = ∑ i ∈ T, g i := by
  classical
  constructor
  · intro h
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp h
    obtain ⟨hS,hT⟩ := Finset.mem_product.mp hm
    obtain ⟨hSA,hSc⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨hTA,hTc⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨hSA,hSc,hTA,hTc,he⟩
  · rintro ⟨hSA,hSc,hTA,hTc,he⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hSA,hSc⟩,
        Finset.mem_powersetCard.mpr ⟨hTA,hTc⟩⟩,he⟩

/-- Validity makes the projection from support matches to common values
bijective. Hence counting matches counts the translated intersection exactly. -/
theorem squarefreeTranslationMatches_card_eq_intersection
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) :
    (squarefreeTranslationMatches g A k t).card =
      (((A.powersetCard k).image (fun S ↦ (∑ i ∈ S, g i) + t)) ∩
        ((A.powersetCard k).image (fun S ↦ ∑ i ∈ S, g i))).card := by
  classical
  have huniq (S T : Finset (Fin n)) (hc : S.card = T.card)
      (hs : (∑ i ∈ S, g i) = ∑ i ∈ T, g i) : S = T := by
    apply Finset.val_injective
    apply multiset_eq_finset_of_validTuple_card_sum g hg T S.val
    · exact hc
    · exact hs
  apply Finset.card_bij (fun uv _ ↦ ∑ i ∈ uv.2, g i)
  · rintro ⟨S,T⟩ huv
    obtain ⟨hSA,hSc,hTA,hTc,he⟩ := (mem_squarefreeTranslationMatches g A S T t).mp huv
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨S,Finset.mem_powersetCard.mpr ⟨hSA,hSc⟩,he⟩,
        Finset.mem_image.mpr ⟨T,Finset.mem_powersetCard.mpr ⟨hTA,hTc⟩,rfl⟩⟩
  · rintro ⟨S,T⟩ huv ⟨U,V⟩ hw huv'
    obtain ⟨_,hSc,_,hTc,he⟩ := (mem_squarefreeTranslationMatches g A S T t).mp huv
    obtain ⟨_,hUc,_,hVc,hf⟩ := (mem_squarefreeTranslationMatches g A U V t).mp hw
    have hTV : T = V := huniq T V (hTc.trans hVc.symm) huv'
    have hSU : S = U := huniq S U (hSc.trans hUc.symm)
      (add_right_cancel (he.trans (huv'.trans hf.symm)))
    exact Prod.ext hSU hTV
  · intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
    obtain ⟨T,hT,hTx⟩ := Finset.mem_image.mp hy
    obtain ⟨hSA,hSc⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨hTA,hTc⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨(S,T),(mem_squarefreeTranslationMatches g A S T t).mpr
      ⟨hSA,hSc,hTA,hTc,hSx.trans hTx.symm⟩,hTx⟩

/-- Normal coordinate-difference matches are indexed by the unchanged
`k`-element support outside the two endpoints. -/
theorem coordinate_difference_normal_matches_card
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (hpA : p ∈ A) (hqA : q ∈ A) :
    ((squarefreeTranslationMatches g A (k+1) (g p-g q)).filter
      (fun uv ↦ p ∉ uv.1)).card = (A.card-2).choose k := by
  classical
  let B := A \ {p,q}
  let F := (squarefreeTranslationMatches g A (k+1) (g p-g q)).filter
    (fun uv ↦ p ∉ uv.1)
  have hdata (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ F) :
      uv.1 ⊆ A ∧ uv.1.card = k+1 ∧ p ∉ uv.1 ∧ q ∈ uv.1 ∧
        uv.2 = insert p (uv.1.erase q) := by
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp huv
    obtain ⟨hSA,hSc,hTA,hTc,he⟩ :=
      (mem_squarefreeTranslationMatches g A uv.1 uv.2 (g p-g q)).mp hm
    have he' : (∑ i ∈ uv.1, g i) + g p = (∑ i ∈ uv.2, g i) + g q := by
      calc
        _ = ((∑ i ∈ uv.1, g i) + (g p-g q)) + g q := by abel
        _ = _ := congrArg (fun x ↦ x+g q) he
    have hn := coordinate_difference_match_normal_form g hg p q hpq
      uv.1 uv.2 (hSc.trans hTc.symm) hp he'
    exact ⟨hSA,hSc,hp,hn.1,hn.2.2.2⟩
  have hcard : F.card = (B.powersetCard k).card := by
    refine Finset.card_bij' (fun uv _ ↦ uv.1.erase q)
      (fun H _ ↦ (insert q H,insert p H)) ?_ ?_ ?_ ?_
    · intro uv huv
      obtain ⟨hSA,hSc,hp,hq,_⟩ := hdata uv huv
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro i hi
        obtain ⟨hiq,hiS⟩ := Finset.mem_erase.mp hi
        apply Finset.mem_sdiff.mpr
        refine ⟨hSA hiS,?_⟩
        simp only [Finset.mem_insert,Finset.mem_singleton]
        exact not_or.mpr ⟨by intro hip; subst i; exact hp hiS,hiq⟩
      · rw [Finset.card_erase_of_mem hq,hSc]
        omega
    · intro H hH
      obtain ⟨hHB,hHc⟩ := Finset.mem_powersetCard.mp hH
      have hpH : p ∉ H := by
        intro h; have hh := (Finset.mem_sdiff.mp (hHB h)).2; exact hh (by simp)
      have hqH : q ∉ H := by
        intro h; have hh := (Finset.mem_sdiff.mp (hHB h)).2; exact hh (by simp)
      have hHA : H ⊆ A := fun i hi ↦ (Finset.mem_sdiff.mp (hHB hi)).1
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_squarefreeTranslationMatches g A _ _ (g p-g q)).mpr
        refine ⟨Finset.insert_subset hqA hHA,?_,Finset.insert_subset hpA hHA,?_,?_⟩
        · simp only [Finset.card_insert_of_notMem hqH,hHc]
        · simp only [Finset.card_insert_of_notMem hpH,hHc]
        · simp only [Finset.sum_insert hpH,Finset.sum_insert hqH]
          abel
      · simpa only [Finset.mem_insert,not_or] using ⟨hpq,hpH⟩
    · intro uv huv
      obtain ⟨_,_,_,hq,hT⟩ := hdata uv huv
      exact Prod.ext (Finset.insert_erase hq) hT.symm
    · intro H hH
      have hqH : q ∉ H := by
        intro h
        have hh := (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hH).1 h)).2
        exact hh (by simp)
      exact Finset.erase_insert hqH
  have hpqA : {p,q} ⊆ A := by
    intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · exact h.symm ▸ hpA
    · exact (Finset.mem_singleton.mp h).symm ▸ hqA
  change F.card = _
  rw [hcard,Finset.card_powersetCard]
  simp only [B,Finset.card_sdiff_of_subset hpqA,Finset.card_pair hpq]

/-- Repeated-endpoint matches are in bijection with degree `k` matches
outside both endpoints, with the translation doubled. -/
theorem coordinate_difference_repeated_matches_card
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (hpA : p ∈ A) (hqA : q ∈ A) :
    ((squarefreeTranslationMatches g A (k+1) (g p-g q)).filter
      (fun uv ↦ p ∈ uv.1)).card =
      (squarefreeTranslationMatches g (A \ {p,q}) k (2 • (g p-g q))).card := by
  classical
  let B := A \ {p,q}
  let F := (squarefreeTranslationMatches g A (k+1) (g p-g q)).filter
    (fun uv ↦ p ∈ uv.1)
  have hdata (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ F) :
      p ∈ uv.1 ∧ q ∈ uv.2 ∧ q ∉ uv.1 ∧ p ∉ uv.2 ∧
        (∑ i ∈ uv.1.erase p, g i) + 2 • g p =
          (∑ i ∈ uv.2.erase q, g i) + 2 • g q := by
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp huv
    obtain ⟨_,hSc,_,hTc,he⟩ :=
      (mem_squarefreeTranslationMatches g A uv.1 uv.2 (g p-g q)).mp hm
    have he' : (∑ i ∈ uv.1, g i) + g p = (∑ i ∈ uv.2, g i) + g q := by
      calc
        _ = ((∑ i ∈ uv.1, g i) + (g p-g q)) + g q := by abel
        _ = _ := congrArg (fun x ↦ x+g q) he
    exact ⟨hp,coordinate_difference_match_repeated_form g hg p q hpq
      uv.1 uv.2 (hSc.trans hTc.symm) hp he'⟩
  have hsub (S : Finset (Fin n)) (hSA : S ⊆ A) (hp : p ∉ S) (hq : q ∉ S) :
      S ⊆ B := by
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨hSA hi,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact not_or.mpr ⟨by intro h; subst i; exact hp hi,
      by intro h; subst i; exact hq hi⟩
  have hnot (S : Finset (Fin n)) (hSB : S ⊆ B) : p ∉ S ∧ q ∉ S := by
    constructor <;> intro h
    · exact (Finset.mem_sdiff.mp (hSB h)).2 (by simp)
    · exact (Finset.mem_sdiff.mp (hSB h)).2 (by simp)
  change F.card = (squarefreeTranslationMatches g B k (2 • (g p-g q))).card
  refine Finset.card_bij' (fun uv _ ↦ (uv.1.erase p,uv.2.erase q))
    (fun uv _ ↦ (insert p uv.1,insert q uv.2)) ?_ ?_ ?_ ?_
  · intro uv huv
    obtain ⟨hSA,hSc,hTA,hTc,_⟩ :=
      (mem_squarefreeTranslationMatches g A uv.1 uv.2 (g p-g q)).mp
        (Finset.mem_filter.mp huv).1
    obtain ⟨hpS,hqT,hqS,hpT,he⟩ := hdata uv huv
    apply (mem_squarefreeTranslationMatches g B _ _ (2 • (g p-g q))).mpr
    refine ⟨hsub _ (Finset.Subset.trans (Finset.erase_subset _ _) hSA)
      (Finset.notMem_erase _ _) (fun h ↦ hqS (Finset.mem_of_mem_erase h)),?_,
      hsub _ (Finset.Subset.trans (Finset.erase_subset _ _) hTA)
        (fun h ↦ hpT (Finset.mem_of_mem_erase h)) (Finset.notMem_erase _ _),?_,?_⟩
    · rw [Finset.card_erase_of_mem hpS,hSc]; omega
    · rw [Finset.card_erase_of_mem hqT,hTc]; omega
    · apply add_right_cancel (b := 2 • g q)
      calc
        _ = (∑ i ∈ uv.1.erase p, g i) + 2 • g p := by
          simp only [two_nsmul]; abel
        _ = _ := he
  · intro uv huv
    obtain ⟨hSB,hSc,hTB,hTc,he⟩ :=
      (mem_squarefreeTranslationMatches g B uv.1 uv.2 (2 • (g p-g q))).mp huv
    obtain ⟨hpS,hqS⟩ := hnot uv.1 hSB
    obtain ⟨hpT,hqT⟩ := hnot uv.2 hTB
    have hSA : uv.1 ⊆ A := fun i hi ↦ (Finset.mem_sdiff.mp (hSB hi)).1
    have hTA : uv.2 ⊆ A := fun i hi ↦ (Finset.mem_sdiff.mp (hTB hi)).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,Finset.mem_insert_self _ _⟩
    apply (mem_squarefreeTranslationMatches g A _ _ (g p-g q)).mpr
    refine ⟨Finset.insert_subset hpA hSA,?_,Finset.insert_subset hqA hTA,?_,?_⟩
    · simp only [Finset.card_insert_of_notMem hpS,hSc]
    · simp only [Finset.card_insert_of_notMem hqT,hTc]
    · calc
        _ = ((∑ i ∈ uv.1, g i) + 2 • (g p-g q)) + g q := by
          rw [Finset.sum_insert hpS,two_nsmul]; abel
        _ = (∑ i ∈ uv.2, g i) + g q := congrArg (fun x ↦ x+g q) he
        _ = _ := by rw [Finset.sum_insert hqT]; abel
  · intro uv huv
    obtain ⟨hp,hq,_⟩ := hdata uv huv
    exact Prod.ext (Finset.insert_erase hp) (Finset.insert_erase hq)
  · intro uv huv
    obtain ⟨hSB,_,hTB,_,_⟩ :=
      (mem_squarefreeTranslationMatches g B uv.1 uv.2 (2 • (g p-g q))).mp huv
    exact Prod.ext (Finset.erase_insert (hnot uv.1 hSB).1)
      (Finset.erase_insert (hnot uv.2 hTB).2)

/-- Exact all-degree recurrence for squarefree support matches under a
coordinate-difference shift. -/
theorem coordinate_difference_matches_card_recursion
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (hpA : p ∈ A) (hqA : q ∈ A) :
    (squarefreeTranslationMatches g A (k+1) (g p-g q)).card =
      (A.card-2).choose k +
        (squarefreeTranslationMatches g (A \ {p,q}) k (2 • (g p-g q))).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := squarefreeTranslationMatches g A (k+1) (g p-g q)) (fun uv ↦ p ∈ uv.1)
  rw [coordinate_difference_repeated_matches_card g hg p q hpq A hpA hqA,
    coordinate_difference_normal_matches_card g hg p q hpq A hpA hqA] at h
  omega

/-- Exact translated-intersection recurrence: delete both difference
endpoints, lower the degree by one, and double the shift. This holds in
every abelian group; no odd-order hypothesis is needed. -/
theorem coordinate_difference_intersection_card_recursion
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (p q : Fin n) (hpq : p ≠ q)
    (A : Finset (Fin n)) (hpA : p ∈ A) (hqA : q ∈ A) :
    let C := A.powersetCard (k+1)
    let D := (A \ {p,q}).powersetCard k
    ((C.image (fun S ↦ (∑ i ∈ S, g i) + (g p-g q))) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i))).card = (A.card-2).choose k +
      ((D.image (fun S ↦ (∑ i ∈ S, g i) + 2 • (g p-g q))) ∩
        (D.image (fun S ↦ ∑ i ∈ S, g i))).card := by
  classical
  dsimp only
  rw [← squarefreeTranslationMatches_card_eq_intersection g hg A (g p-g q),
    ← squarefreeTranslationMatches_card_eq_intersection g hg (A \ {p,q}) (2 • (g p-g q))]
  exact coordinate_difference_matches_card_recursion g hg p q hpq A hpA hqA

end MinModulus.Research
