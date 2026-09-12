import research.AnchoredCompatibleRelation

/-! Exact counting of anchored-cube intersections by signed supports. -/
namespace MinModulus.Research
open Finset
variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Removing the anchor does not change an anchored subset sum. -/
theorem anchored_sum_erase (g : Fin n → G) (k : Fin n) (S : Finset (Fin n)) :
    (∑ j ∈ S.erase k, (g j - g k)) = ∑ j ∈ S, (g j - g k) := by
  apply Finset.sum_subset (Finset.erase_subset k S)
  intro j hj hnot
  by_cases hjk : j = k
  · simp [hjk]
  · exact (hnot (Finset.mem_erase.mpr ⟨hjk,hj⟩)).elim

/-- Validity makes normalized anchored subset representations unique. -/
theorem normalized_anchored_sum_injective (g : Fin n → G) (hg : ValidTuple g)
    (k : Fin n) (S T : Finset (Fin n)) (hSk : k ∉ S) (hTk : k ∉ T)
    (hs : (∑ j ∈ S, (g j - g k)) = ∑ j ∈ T, (g j - g k)) : S = T := by
  let e : Fin n → ℤ := fun j ↦ (if j ∈ S then 1 else 0) - if j ∈ T then 1 else 0
  have he := ternary_anchor_relation_eq_zero g hg k e (by simp [e,hSk,hTk]) (by
    intro j
    dsimp only [e]
    split_ifs <;> omega) (by
    simp only [e,sub_smul,ite_smul,one_smul,zero_smul,Finset.sum_sub_distrib,
      Finset.sum_ite_mem,Finset.univ_inter,hs,sub_self])
  ext j
  have hz := congrFun he j
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [e,hS,hT] at hz ⊢

abbrev OverlapSupport (n : ℕ) := Finset (Fin n) × Finset (Fin n)
abbrev OverlapProfile (n : ℕ) := OverlapSupport n × Finset (Fin n)

def overlapSupports (k l : Fin n) : Finset (OverlapSupport n) :=
  Finset.univ.filter fun p ↦ Disjoint p.1 p.2 ∧ k ∉ p.1 ∧ l ∉ p.1 ∧ k ∉ p.2 ∧ l ∉ p.2

def overlapFreeIndices (p : OverlapSupport n) : Finset (Fin n) :=
  Finset.univ \ (p.1 ∪ p.2)

def splitOverlapPair (k l : Fin n) (a : Finset (Fin n) × Finset (Fin n)) : OverlapProfile n :=
  (((a.1 \ a.2).erase l, (a.2 \ a.1).erase k),
    (a.1 ∩ a.2) ∪ (a.2 ∩ {k}) ∪ (a.1 ∩ {l}))

def joinOverlapProfile (k l : Fin n) (t : OverlapProfile n) : Finset (Fin n) × Finset (Fin n) :=
  ((t.1.1 ∪ t.2).erase k, (t.1.2 ∪ t.2).erase l)

def GoodOverlapProfile (k l : Fin n) (t : OverlapProfile n) : Prop :=
  t.1 ∈ overlapSupports k l ∧ t.2 ⊆ overlapFreeIndices t.1

instance instDecidableGoodOverlapProfile (k l : Fin n) (t : OverlapProfile n) : Decidable (GoodOverlapProfile k l t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem splitOverlapPair_good (k l : Fin n) (hkl : k ≠ l)
    (S T : Finset (Fin n)) (hSk : k ∉ S) (hTl : l ∉ T) :
    GoodOverlapProfile k l (splitOverlapPair k l (S,T)) := by
  simp only [GoodOverlapProfile,overlapSupports,splitOverlapPair,overlapFreeIndices,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · refine ⟨?_,?_,?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      simp only [Finset.mem_erase,Finset.mem_sdiff]
      aesop
    · simp [hSk]
    · simp
    · simp
    · simp [hTl]
  · intro j hj
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,
      Finset.mem_erase,Finset.mem_inter,Finset.mem_singleton] at hj ⊢
    aesop

theorem join_split_overlap (k l : Fin n) (hkl : k ≠ l)
    (S T : Finset (Fin n)) (hSk : k ∉ S) (hTl : l ∉ T) :
    joinOverlapProfile k l (splitOverlapPair k l (S,T)) = (S,T) := by
  apply Prod.ext <;> ext j <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all [joinOverlapProfile,splitOverlapPair] <;> tauto

private theorem overlap_boolean_roundtrip (P Q U K L : Prop)
    (h : ((K ∨ L) → ¬P ∧ ¬Q) ∧ ¬(P ∧ Q) ∧ ¬(P ∧ U) ∧ ¬(Q ∧ U) ∧ ¬(K ∧ L)) :
    ((¬L ∧ ((¬K ∧ (P ∨ U)) ∧ ¬(¬L ∧ (Q ∨ U)))) ↔ P) ∧
    ((¬K ∧ ((¬L ∧ (Q ∨ U)) ∧ ¬(¬K ∧ (P ∨ U)))) ↔ Q) ∧
    (((((¬K ∧ (P ∨ U)) ∧ (¬L ∧ (Q ∨ U))) ∨ ((¬L ∧ (Q ∨ U)) ∧ K)) ∨
      ((¬K ∧ (P ∨ U)) ∧ L)) ↔ U) := by
  tauto

theorem split_join_overlap (k l : Fin n) (hkl : k ≠ l) (t : OverlapProfile n)
    (ht : GoodOverlapProfile k l t) :
    splitOverlapPair k l (joinOverlapProfile k l t) = t := by
  rcases t with ⟨⟨P,Q⟩,U⟩
  simp only [GoodOverlapProfile,overlapSupports,Finset.mem_filter,Finset.mem_univ,true_and,
    overlapFreeIndices] at ht
  obtain ⟨⟨hPQ,hPk,hPl,hQk,hQl⟩,hU⟩ := ht
  have hPU : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro j hjP hjU
    exact (Finset.mem_sdiff.mp (hU hjU)).2 (Finset.mem_union_left Q hjP)
  have hQU : Disjoint Q U := by
    apply Finset.disjoint_left.mpr
    intro j hjQ hjU
    exact (Finset.mem_sdiff.mp (hU hjU)).2 (Finset.mem_union_right P hjQ)
  have hpoint (j : Fin n) :
      ((j = k ∨ j = l) → j ∉ P ∧ j ∉ Q) ∧
      ¬ (j ∈ P ∧ j ∈ Q) ∧ ¬ (j ∈ P ∧ j ∈ U) ∧ ¬ (j ∈ Q ∧ j ∈ U) ∧
      ¬ (j = k ∧ j = l) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rintro (rfl | rfl)
      · exact ⟨hPk,hQk⟩
      · exact ⟨hPl,hQl⟩
    · rintro ⟨hP,hQ⟩; exact Finset.disjoint_left.mp hPQ hP hQ
    · rintro ⟨hP,hU⟩; exact Finset.disjoint_left.mp hPU hP hU
    · rintro ⟨hQ,hU⟩; exact Finset.disjoint_left.mp hQU hQ hU
    · rintro ⟨rfl,h⟩; exact hkl h
  apply Prod.ext
  · apply Prod.ext
    · ext j
      simpa only [splitOverlapPair,joinOverlapProfile,Finset.mem_erase,Finset.mem_union,
        Finset.mem_sdiff] using (overlap_boolean_roundtrip _ _ _ _ _ (hpoint j)).1
    · ext j
      simpa only [splitOverlapPair,joinOverlapProfile,Finset.mem_erase,Finset.mem_union,
        Finset.mem_sdiff] using (overlap_boolean_roundtrip _ _ _ _ _ (hpoint j)).2.1
  · ext j
    simpa only [splitOverlapPair,joinOverlapProfile,Finset.mem_erase,Finset.mem_union,
      Finset.mem_inter,Finset.mem_singleton] using
      (overlap_boolean_roundtrip _ _ _ _ _ (hpoint j)).2.2

def normalizedOverlapPairs {N : ℕ} [NeZero N] (g : Fin n → ZMod N) (k l : Fin n) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter fun a ↦ k ∉ a.1 ∧ l ∉ a.2 ∧
    (∑ j ∈ a.1, (g j - g k)) = ∑ j ∈ a.2, (g j - g l)

theorem anchored_intersection_card_eq_normalized_pairs {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) :
    (anchoredCube g k ∩ anchoredCube g l).card = (normalizedOverlapPairs g k l).card := by
  symm
  apply Finset.card_bij (fun a _ ↦ ∑ j ∈ a.1, (g j - g k))
  · intro a ha
    simp only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a.1,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,ha.2.2.symm⟩⟩
  · intro a ha b hb he
    simp only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
    exact Prod.ext (normalized_anchored_sum_injective g hg k a.1 b.1 ha.1 hb.1 he)
      (normalized_anchored_sum_injective g hg l a.2 b.2 ha.2.1 hb.2.1
        (ha.2.2.symm.trans (he.trans hb.2.2)))
  · intro x hx
    obtain ⟨S,hSk,hS⟩ := mem_anchoredCube_normalized g k x (Finset.mem_inter.mp hx).1
    obtain ⟨T,hTl,hT⟩ := mem_anchoredCube_normalized g l x (Finset.mem_inter.mp hx).2
    exact ⟨(S,T),by
      simpa only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and] using
        And.intro hSk (And.intro hTl (hS.trans hT.symm)),hS⟩

def overlapRelationValue (g : Fin n → G) (k l : Fin n) (p : OverlapSupport n) (r : ℕ) : G :=
  (∑ j ∈ p.1, (g j - g k)) - (∑ j ∈ p.2, (g j - g k)) +
    (p.2.card + r) • (g l - g k)

theorem joinOverlapProfile_difference (g : Fin n → G) (k l : Fin n) (t : OverlapProfile n)
    (ht : GoodOverlapProfile k l t) :
    (∑ j ∈ (joinOverlapProfile k l t).1, (g j - g k)) -
      (∑ j ∈ (joinOverlapProfile k l t).2, (g j - g l)) =
        overlapRelationValue g k l t.1 t.2.card := by
  rcases t with ⟨⟨P,Q⟩,U⟩
  have hPU : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro j hjP hjU
    exact (Finset.mem_sdiff.mp (ht.2 hjU)).2 (Finset.mem_union_left Q hjP)
  have hQU : Disjoint Q U := by
    apply Finset.disjoint_left.mpr
    intro j hjQ hjU
    exact (Finset.mem_sdiff.mp (ht.2 hjU)).2 (Finset.mem_union_right P hjQ)
  have hshift (W : Finset (Fin n)) :
      (∑ j ∈ W, (g j - g l)) = (∑ j ∈ W, (g j - g k)) - W.card • (g l - g k) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,smul_sub]
    abel
  simp only [joinOverlapProfile,anchored_sum_erase]
  rw [Finset.sum_union hPU,Finset.sum_union hQU,hshift Q,hshift U]
  simp only [overlapRelationValue,add_nsmul]
  abel

def overlapProfileChoices {N : ℕ} [NeZero N] (g : Fin n → ZMod N) (k l : Fin n)
    (p : OverlapSupport n) : Finset (Finset (Fin n)) :=
  (overlapFreeIndices p).powerset.filter fun U ↦ overlapRelationValue g k l p U.card = 0

def overlapRelationProfiles {N : ℕ} [NeZero N] (g : Fin n → ZMod N) (k l : Fin n) :
    Finset (OverlapProfile n) :=
  (overlapSupports k l).biUnion fun p ↦ (overlapProfileChoices g k l p).image fun U ↦ (p,U)

@[simp] theorem mem_overlapRelationProfiles {N : ℕ} [NeZero N] (g : Fin n → ZMod N)
    (k l : Fin n) (t : OverlapProfile n) :
    t ∈ overlapRelationProfiles g k l ↔
      GoodOverlapProfile k l t ∧ overlapRelationValue g k l t.1 t.2.card = 0 := by
  rcases t with ⟨⟨P,Q⟩,U⟩
  simp [overlapRelationProfiles,overlapProfileChoices,GoodOverlapProfile,and_assoc]

theorem normalized_pairs_card_eq_profiles {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k l : Fin n) (hkl : k ≠ l) :
    (normalizedOverlapPairs g k l).card = (overlapRelationProfiles g k l).card := by
  apply Finset.card_bij (fun a _ ↦ splitOverlapPair k l a)
  · intro a ha
    simp only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    have ht := splitOverlapPair_good k l hkl a.1 a.2 ha.1 ha.2.1
    apply (mem_overlapRelationProfiles g k l _).mpr
    refine ⟨ht,?_⟩
    rw [← joinOverlapProfile_difference g k l _ ht,join_split_overlap k l hkl a.1 a.2 ha.1 ha.2.1]
    exact sub_eq_zero.mpr ha.2.2
  · intro a ha b hb he
    simp only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
    have hh := congrArg (joinOverlapProfile k l) he
    rwa [join_split_overlap k l hkl a.1 a.2 ha.1 ha.2.1,
      join_split_overlap k l hkl b.1 b.2 hb.1 hb.2.1] at hh
  · intro t ht
    obtain ⟨hgood,hval⟩ := (mem_overlapRelationProfiles g k l t).mp ht
    refine ⟨joinOverlapProfile k l t,?_,split_join_overlap k l hkl t hgood⟩
    simp only [normalizedOverlapPairs,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨by simp [joinOverlapProfile],by simp [joinOverlapProfile],?_⟩
    apply sub_eq_zero.mp
    rw [joinOverlapProfile_difference g k l t hgood,hval]

/-- Grouping subsets by cardinality gives the binomial fibre weights. -/
theorem card_filter_powerset_by_card (F : Finset (Fin n)) (p : ℕ → Prop) [DecidablePred p] :
    (F.powerset.filter fun U ↦ p U.card).card =
      ∑ r ∈ Finset.range (n+1), if p r then F.card.choose r else 0 := by
  have hmap : ((F.powerset.filter fun U ↦ p U.card) : Set (Finset (Fin n))).MapsTo
      Finset.card (Finset.range (n+1)) := by
    intro U hU
    have hUF := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have hcard := Finset.card_le_card hUF
    have hF := Finset.card_le_univ F
    rw [Fintype.card_fin] at hF
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro r _
  have hf : (F.powerset.filter fun U ↦ p U.card).filter (fun U ↦ U.card = r) =
      if p r then F.powersetCard r else ∅ := by
    ext U
    by_cases hp : p r <;> simp [hp,Finset.mem_powersetCard] <;> aesop
  rw [hf]
  by_cases hp : p r <;> simp [hp,Finset.card_powersetCard]

theorem overlap_profiles_card_eq_sum_choices {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k l : Fin n) :
    (overlapRelationProfiles g k l).card =
      ∑ p ∈ overlapSupports k l, (overlapProfileChoices g k l p).card := by
  unfold overlapRelationProfiles
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.card_image_of_injective
    intro U V h
    exact congrArg Prod.snd h
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro t ht hp
    obtain ⟨U,_,hU⟩ := Finset.mem_image.mp ht
    obtain ⟨V,_,hV⟩ := Finset.mem_image.mp hp
    exact hpq (congrArg Prod.fst (hU.trans hV.symm))

/-- Exact intersection cardinality. For signed support sizes p,q, a shared
selector of size r has binomial(n-p-q,r) choices and multiplier M=q+r. -/
theorem anchored_intersection_card_eq_binomial_sum {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l) :
    (anchoredCube g k ∩ anchoredCube g l).card =
      ∑ p ∈ overlapSupports k l, ∑ r ∈ Finset.range (n+1),
        if overlapRelationValue g k l p r = 0 then (n-p.1.card-p.2.card).choose r else 0 := by
  rw [anchored_intersection_card_eq_normalized_pairs g hg k l,
    normalized_pairs_card_eq_profiles g k l hkl,overlap_profiles_card_eq_sum_choices]
  apply Finset.sum_congr rfl
  intro p hp
  unfold overlapProfileChoices
  rw [card_filter_powerset_by_card (overlapFreeIndices p) (fun r ↦ overlapRelationValue g k l p r = 0)]
  have hdisj : Disjoint p.1 p.2 := (Finset.mem_filter.mp hp).2.1
  have hc : (overlapFreeIndices p).card = n-p.1.card-p.2.card := by
    rw [overlapFreeIndices,Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ,Fintype.card_fin,Finset.card_union_of_disjoint hdisj,Nat.sub_add_eq]
  rw [hc]

end MinModulus.Research
