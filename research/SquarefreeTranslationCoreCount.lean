import research.CoordinateDifferenceRecursion
import research.NonuniformTranslatedPacking

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Disjoint balanced difference supports of a degree-k translation match. -/
noncomputable def squarefreeTranslationCores
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (k : ℕ) (t : G) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (A.powerset.product A.powerset).filter (fun uv ↦
    Disjoint uv.1 uv.2 ∧ uv.1.card=uv.2.card ∧ uv.1.card≤k ∧
      (∑ i ∈ uv.1, g i)+t=∑ i ∈ uv.2, g i)

theorem mem_squarefreeTranslationCores
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A U V : Finset (Fin n)) (t : G) :
    (U,V) ∈ squarefreeTranslationCores g A k t ↔
      U⊆A ∧ V⊆A ∧ Disjoint U V ∧ U.card=V.card ∧ U.card≤k ∧
        (∑ i ∈ U, g i)+t=∑ i ∈ V, g i := by
  classical
  constructor
  · intro h
    obtain ⟨hp,hd,hc,hk,he⟩ := Finset.mem_filter.mp h
    obtain ⟨hU,hV⟩ := Finset.mem_product.mp hp
    exact ⟨Finset.mem_powerset.mp hU,Finset.mem_powerset.mp hV,hd,hc,hk,he⟩
  · rintro ⟨hUA,hVA,hd,hc,hk,he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hUA,Finset.mem_powerset.mpr hVA⟩,hd,hc,hk,he⟩

/-- Cancellation extracts a disjoint core and a common support of the
exact residual size, without any tuple-validity assumption. -/
theorem squarefree_translation_match_core_data
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A S T : Finset (Fin n)) (t : G)
    (hmatch : (S,T) ∈ squarefreeTranslationMatches g A k t) :
    (S\T,T\S) ∈ squarefreeTranslationCores g A k t ∧
      S∩T ∈ (A \ ((S\T)∪(T\S))).powersetCard (k-(S\T).card) := by
  classical
  obtain ⟨hSA,hSc,hTA,hTc,he⟩ := (mem_squarefreeTranslationMatches g A S T t).mp hmatch
  have hcs := Finset.card_sdiff_add_card_inter S T
  have hct := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hct
  have hc : (S\T).card=(T\S).card := by omega
  have he' : (∑ i ∈ S\T, g i)+t=∑ i ∈ T\S, g i := by
    apply add_right_cancel (b := ∑ i ∈ S∩T, g i)
    calc
      _ = (∑ i ∈ S, g i)+t := by
        conv_rhs => rw [← Finset.sdiff_union_inter S T,Finset.sum_union (Finset.disjoint_sdiff_inter S T)]
        abel
      _ = ∑ i ∈ T, g i := he
      _ = _ := by
        conv_lhs => rw [← Finset.sdiff_union_inter T S,Finset.sum_union (Finset.disjoint_sdiff_inter T S)]
        rw [Finset.inter_comm T S]
  constructor
  · apply (mem_squarefreeTranslationCores g A _ _ t).mpr
    refine ⟨(Finset.sdiff_subset).trans hSA,(Finset.sdiff_subset).trans hTA,?_,hc,by omega,he'⟩
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro i hi
      obtain ⟨hiS,hiT⟩ := Finset.mem_inter.mp hi
      apply Finset.mem_sdiff.mpr
      refine ⟨hSA hiS,?_⟩
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_sdiff.mp h).2 hiT
      · exact (Finset.mem_sdiff.mp h).2 hiS
    · omega

/-- Every translation match is uniquely a disjoint core with an arbitrary
common support outside that core. This gives an exact all-degree count. -/
theorem squarefreeTranslationMatches_card_eq_sum_cores
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (t : G) :
    (squarefreeTranslationMatches g A k t).card =
      ∑ uv ∈ squarefreeTranslationCores g A k t,
        (A.card-2*uv.1.card).choose (k-uv.1.card) := by
  classical
  let F := squarefreeTranslationCores g A k t
  let B := F.sigma (fun uv ↦ (A \ (uv.1∪uv.2)).powersetCard (k-uv.1.card))
  have hparts (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ F)
      (H : Finset (Fin n)) (hH : H ∈ (A \ (uv.1∪uv.2)).powersetCard (k-uv.1.card)) :
      Disjoint uv.1 H ∧ Disjoint uv.2 H := by
    have hsub := (Finset.mem_powersetCard.mp hH).1
    constructor
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp (hsub hj)).2 (Finset.mem_union_left _ hi)
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp (hsub hj)).2 (Finset.mem_union_right _ hi)
  have hcount : (squarefreeTranslationMatches g A k t).card=B.card := by
    refine Finset.card_bij'
      (fun uv _ ↦ (⟨(uv.1\uv.2,uv.2\uv.1),uv.1∩uv.2⟩ :
        Σ _uv : Finset (Fin n) × Finset (Fin n), Finset (Fin n)))
      (fun p _ ↦ (p.1.1∪p.2,p.1.2∪p.2)) ?_ ?_ ?_ ?_
    · intro uv huv
      apply Finset.mem_sigma.mpr
      exact squarefree_translation_match_core_data g A uv.1 uv.2 t huv
    · intro p hp
      obtain ⟨huv,hH⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hUA,hVA,hd,hc,hk,he⟩ := (mem_squarefreeTranslationCores g A p.1.1 p.1.2 t).mp huv
      obtain ⟨hUH,hVH⟩ := hparts p.1 huv p.2 hH
      obtain ⟨hHB,hHc⟩ := Finset.mem_powersetCard.mp hH
      have hHA : p.2 ⊆ A := fun i hi ↦ (Finset.mem_sdiff.mp (hHB hi)).1
      apply (mem_squarefreeTranslationMatches g A _ _ t).mpr
      refine ⟨Finset.union_subset hUA hHA,?_,Finset.union_subset hVA hHA,?_,?_⟩
      · rw [Finset.card_union_of_disjoint hUH,hHc]
        omega
      · rw [Finset.card_union_of_disjoint hVH,hHc]
        omega
      · rw [Finset.sum_union hUH,Finset.sum_union hVH]
        calc
          _ = ((∑ i ∈ p.1.1, g i)+t)+(∑ i ∈ p.2, g i) := by abel
          _ = _ := by rw [he]
    · intro uv huv
      apply Prod.ext
      · exact Finset.sdiff_union_inter uv.1 uv.2
      · rw [Finset.inter_comm uv.1 uv.2]
        exact Finset.sdiff_union_inter uv.2 uv.1
    · intro p hp
      obtain ⟨huv,hH⟩ := Finset.mem_sigma.mp hp
      obtain ⟨_,_,hd,_,_,_⟩ := (mem_squarefreeTranslationCores g A p.1.1 p.1.2 t).mp huv
      obtain ⟨hUH,hVH⟩ := hparts p.1 huv p.2 hH
      have hU : (p.1.1∪p.2)\(p.1.2∪p.2)=p.1.1 := by
        ext i
        have h1 : i ∈ p.1.1 → i ∈ p.1.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hd ha hb
        have h2 : i ∈ p.1.1 → i ∈ p.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hUH ha hb
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
      have hV : (p.1.2∪p.2)\(p.1.1∪p.2)=p.1.2 := by
        ext i
        have h1 : i ∈ p.1.1 → i ∈ p.1.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hd ha hb
        have h2 : i ∈ p.1.2 → i ∈ p.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hVH ha hb
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
      have hCommon : (p.1.1∪p.2)∩(p.1.2∪p.2)=p.2 := by
        ext i
        have h1 : i ∈ p.1.1 → i ∈ p.1.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hd ha hb
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      simp only [hU,hV,hCommon]
  rw [hcount,Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro uv huv
  obtain ⟨hUA,hVA,hd,hc,_,_⟩ := (mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv
  rw [Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.union_subset hUA hVA),
    Finset.card_union_of_disjoint hd,← hc]
  congr 2
  omega

/-- A support-binomial bound on each weighted disjoint core bounds every
translation-match family in arbitrary degree. The numerical premise is
explicit and is not claimed uniformly sharp. -/
theorem squarefree_translation_matches_card_le_weight_bound
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) (M : ℕ)
    (hM : ∀ uv ∈ squarefreeTranslationCores g A k t,
      (A.card-2*uv.1.card).choose (k-uv.1.card)*(2*uv.1.card).choose uv.1.card ≤ M) :
    (squarefreeTranslationMatches g A k t).card ≤ M := by
  rw [squarefreeTranslationMatches_card_eq_sum_cores]
  apply equal_evaluation_disjoint_family_weight_sum_le (δ:=0) g hg t
    (squarefreeTranslationCores g A k t)
  · intro uv huv
    exact ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.1
  · intro uv huv
    have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.1
    omega
  · intro uv huv
    have he := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.2.2
    rw [← he]
    abel
  · intro uv huv
    have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.1
    have hh := hM uv huv
    simpa only [← hc,two_mul] using hh

end MinModulus.Research
