import MinModulus.LossOneBlockSupport

namespace MinModulus
open Finset
open scoped Classical

/-- Ordered disjoint equal-sum subset pairs in an actual coordinate block,
including the empty pair. -/
noncomputable def subsetDisjointCollisionPairs
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) :
    Finset (Finset α × Finset α) :=
  (S.powerset ×ˢ S.powerset).filter (fun uv ↦
    Disjoint uv.1 uv.2 ∧ (∑ i ∈ uv.1, x i)=(∑ i ∈ uv.2, x i))

theorem mem_subset_disjoint_collision_pairs
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (uv : Finset α × Finset α) :
    uv ∈ subsetDisjointCollisionPairs x S ↔
      uv.1 ⊆ S ∧ uv.2 ⊆ S ∧ Disjoint uv.1 uv.2 ∧
        (∑ i ∈ uv.1, x i)=(∑ i ∈ uv.2, x i) := by
  simp only [subsetDisjointCollisionPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_powerset]
  tauto

/-- A loss-one block has exactly three disjoint ordered collisions:
the empty pair and the two orientations of its complementary pair. -/
theorem disjoint_collision_pair_card_eq_three_of_loss_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hloss : subsetCollisionLossOn x S=1) :
    (subsetDisjointCollisionPairs x S).card=3 := by
  classical
  obtain ⟨z,U,V,hU,hV,hne,hd,hcover,heU,heV,_,hf,hother⟩ :=
    exists_complementary_double_fibre_of_loss_one x S hloss
  have hempty : ((∅,∅) : Finset α × Finset α) ∈ subsetDisjointCollisionPairs x S := by
    rw [mem_subset_disjoint_collision_pairs]
    simp
  have hUV : (U,V) ∈ subsetDisjointCollisionPairs x S :=
    (mem_subset_disjoint_collision_pairs x S _).mpr ⟨hU,hV,hd,heU.trans heV.symm⟩
  have hVU : (V,U) ∈ subsetDisjointCollisionPairs x S :=
    (mem_subset_disjoint_collision_pairs x S _).mpr ⟨hV,hU,hd.symm,heV.trans heU.symm⟩
  have hset : subsetDisjointCollisionPairs x S={(∅,∅),(U,V),(V,U)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hA,hB,hdis,he⟩ := (mem_subset_disjoint_collision_pairs x S p).mp hp
      by_cases hAB : p.1=p.2
      · have hzero : p.1=∅ := (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hAB] using hdis)
        have hpeq : p=(∅,∅) := Prod.ext hzero (hAB.symm.trans hzero)
        simp [hpeq]
      · have hz : (∑ i ∈ p.1, x i)=z := by
          by_contra hnot
          have hcard := hother _ hnot
          have htwo : 1 < (S.powerset.filter (fun W ↦ (∑ i ∈ W, x i)=(∑ i ∈ p.1, x i))).card :=
            Finset.one_lt_card.mpr ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA,rfl⟩,
              p.2,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB,he.symm⟩,hAB⟩
          omega
        have ha := (hf p.1).mp ⟨hA,hz⟩
        have hb := (hf p.2).mp ⟨hB,he.symm.trans hz⟩
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact False.elim (hAB (ha.trans hb.symm))
        · have hpUV : p=(U,V) := Prod.ext ha hb
          simp [hpUV]
        · have hpVU : p=(V,U) := Prod.ext ha hb
          simp [hpVU]
        · exact False.elim (hAB (ha.trans hb.symm))
    · intro hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hempty
      · exact hUV
      · exact hVU
  have hUVne : (U,V) ≠ (V,U) := fun h ↦ hne (congrArg Prod.fst h)
  have h0UV : ((∅,∅) : Finset α × Finset α) ≠ (U,V) := by
    intro h
    exact hne ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))
  have h0VU : ((∅,∅) : Finset α × Finset α) ≠ (V,U) := by
    intro h
    exact hne ((congrArg Prod.snd h).symm.trans (congrArg Prod.fst h))
  rw [hset]
  simp [h0UV,h0VU,hUVne]

/-- Independent addition of block sum images makes disjoint collision
pairs factor exactly across the two coordinate blocks. -/
theorem disjoint_collision_pair_card_eq_product
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α)
    (hd : Disjoint S T)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G))) :
    (subsetDisjointCollisionPairs x (S ∪ T)).card=
      (subsetDisjointCollisionPairs x S).card*(subsetDisjointCollisionPairs x T).card := by
  classical
  have hpart (U : Finset α) (hU : U ⊆ S ∪ T) : (U ∩ S) ∪ (U ∩ T)=U := by
    ext i
    have hh : i ∈ U → i ∈ S ∨ i ∈ T := fun h ↦ Finset.mem_union.mp (hU h)
    simp only [Finset.mem_union,Finset.mem_inter]
    tauto
  have hinter (U V : Finset α) (hU : U ⊆ S) (hV : V ⊆ T) :
      (U ∪ V) ∩ S=U ∧ (U ∪ V) ∩ T=V := by
    constructor <;> ext i
    all_goals
      have hu : i ∈ U → i ∈ S := fun h ↦ hU h
      have hv : i ∈ V → i ∈ T := fun h ↦ hV h
      have hn : i ∈ S → i ∈ T → False := fun h1 h2 ↦ Finset.disjoint_left.mp hd h1 h2
      simp only [Finset.mem_inter,Finset.mem_union]
      tauto
  rw [← Finset.card_product]
  apply Finset.card_bij (fun p _ ↦ ((p.1 ∩ S,p.2 ∩ S),(p.1 ∩ T,p.2 ∩ T)))
  · intro p hp
    obtain ⟨hA,hB,hdis,he⟩ := (mem_subset_disjoint_collision_pairs x (S ∪ T) p).mp hp
    obtain ⟨heS,heT⟩ := (subset_sum_eq_iff_blockwise_of_add_injective x S T p.1 p.2 hd hA hB hi).mp he
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_subset_disjoint_collision_pairs x S _).mpr
        ⟨Finset.inter_subset_right,Finset.inter_subset_right,
          hdis.mono Finset.inter_subset_left Finset.inter_subset_left,heS⟩
    · exact (mem_subset_disjoint_collision_pairs x T _).mpr
        ⟨Finset.inter_subset_right,Finset.inter_subset_right,
          hdis.mono Finset.inter_subset_left Finset.inter_subset_left,heT⟩
  · intro p hp q hq he
    obtain ⟨hp1,hp2,_,_⟩ := (mem_subset_disjoint_collision_pairs x (S ∪ T) p).mp hp
    obtain ⟨hq1,hq2,_,_⟩ := (mem_subset_disjoint_collision_pairs x (S ∪ T) q).mp hq
    have hh := congrArg (fun r : (Finset α × Finset α) × (Finset α × Finset α) ↦
      (r.1.1 ∪ r.2.1,r.1.2 ∪ r.2.2)) he
    simpa only [hpart p.1 hp1,hpart p.2 hp2,hpart q.1 hq1,hpart q.2 hq2,Prod.eta] using hh
  · rintro ⟨⟨A,B⟩,⟨C,D⟩⟩ hp
    obtain ⟨hpS,hpT⟩ := Finset.mem_product.mp hp
    obtain ⟨hA,hB,hAB,heAB⟩ := (mem_subset_disjoint_collision_pairs x S _).mp hpS
    obtain ⟨hC,hD,hCD,heCD⟩ := (mem_subset_disjoint_collision_pairs x T _).mp hpT
    refine ⟨(A ∪ C,B ∪ D),?_,?_⟩
    · apply (mem_subset_disjoint_collision_pairs x (S ∪ T) _).mpr
      refine ⟨Finset.union_subset_union hA hC,Finset.union_subset_union hB hD,?_,?_⟩
      · apply Finset.disjoint_left.mpr
        intro i hi hj
        rcases Finset.mem_union.mp hi with ha | hc <;> rcases Finset.mem_union.mp hj with hb | hd'
        · exact Finset.disjoint_left.mp hAB ha hb
        · exact Finset.disjoint_left.mp hd (hA ha) (hD hd')
        · exact Finset.disjoint_left.mp hd (hB hb) (hC hc)
        · exact Finset.disjoint_left.mp hCD hc hd'
      · rw [Finset.sum_union (hd.mono hA hC),Finset.sum_union (hd.mono hB hD),heAB,heCD]
    · apply Prod.ext
      · exact Prod.ext (hinter A C hA hC).1 (hinter B D hB hD).1
      · exact Prod.ext (hinter A C hA hC).2 (hinter B D hB hD).2

/-- Validity orients exactly half the nonempty disjoint collision pairs;
the empty pair is the only equal-cardinality case. -/
theorem twice_binary_core_card_add_one_eq_disjoint_pair_card
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G) :
    2*(tupleBinaryCollisionCores g b).card+1=
      (subsetDisjointCollisionPairs (fun i ↦ g i+b) Finset.univ).card := by
  classical
  let R := subsetDisjointCollisionPairs (fun i ↦ g i+b) Finset.univ
  let P := R.filter (fun p ↦ p.2.card < p.1.card)
  let Q := R.filter (fun p ↦ p.1.card < p.2.card)
  let E := R.filter (fun p ↦ p.1.card=p.2.card)
  have hP : P=tupleBinaryCollisionCores g b := by
    ext p
    simp only [P,R,Finset.mem_filter,mem_subset_disjoint_collision_pairs,
      tupleBinaryCollisionCores,Finset.mem_univ,Finset.subset_univ,true_and,and_assoc]
  have hswap : P.card=Q.card := by
    apply Finset.card_bij (fun p _ ↦ p.swap)
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hA,hB,hd,he⟩ := (mem_subset_disjoint_collision_pairs _ _ p).mp hp
      exact Finset.mem_filter.mpr ⟨(mem_subset_disjoint_collision_pairs _ _ p.swap).mpr
        ⟨hB,hA,hd.symm,he.symm⟩,hlt⟩
    · intro p _ q _ he
      exact Prod.swap_injective he
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hA,hB,hd,he⟩ := (mem_subset_disjoint_collision_pairs _ _ p).mp hp
      exact ⟨p.swap,Finset.mem_filter.mpr ⟨(mem_subset_disjoint_collision_pairs _ _ p.swap).mpr
        ⟨hB,hA,hd.symm,he.symm⟩,hlt⟩,Prod.swap_swap p⟩
  have hE : E={((∅,∅) : Finset (Fin n) × Finset (Fin n))} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hcard⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,_,hd,he⟩ := (mem_subset_disjoint_collision_pairs _ _ p).mp hp
      have hAB : p.1=p.2 := tuple_subset_fibre_cardinality_injective g hg b (∑ i ∈ p.1, (g i+b))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm⟩) hcard
      have hzero : p.1=∅ := (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hAB] using hd)
      exact Finset.mem_singleton.mpr (Prod.ext hzero (hAB.symm.trans hzero))
    · intro hp
      have he := Finset.mem_singleton.mp hp
      subst p
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_subset_disjoint_collision_pairs]
        simp
      · rfl
  have hrest : R.filter (fun p ↦ ¬ p.2.card < p.1.card)=Q ∪ E := by
    ext p
    simp only [Q,E,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro ⟨hp,hlt⟩
      by_cases he : p.1.card=p.2.card
      · exact Or.inr ⟨hp,he⟩
      · exact Or.inl ⟨hp,by omega⟩
    · rintro (⟨hp,hlt⟩ | ⟨hp,he⟩) <;> exact ⟨hp,by omega⟩
  have hdis : Disjoint Q E := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hlt := (Finset.mem_filter.mp hp).2
    have he := (Finset.mem_filter.mp hq).2
    omega
  have hc := Finset.card_filter_add_card_filter_not (s:=R) (fun p ↦ p.2.card < p.1.card)
  rw [hrest,Finset.card_union_of_disjoint hdis,hE,Finset.card_singleton] at hc
  change P.card+Q.card+1=R.card at hc
  rw [← hswap,hP] at hc
  change 2*(tupleBinaryCollisionCores g b).card+1=R.card
  omega

/-- A valid tuple partitioned into independent loss-one blocks has
exactly four oriented disjoint binary collision cores. -/
theorem binary_core_card_eq_four_of_unit_loss_partition
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S T : Finset (Fin n)) (hd : Disjoint S T) (hcover : S ∪ T=Finset.univ)
    (hs : subsetCollisionLossOn (fun i ↦ g i+b) S=1)
    (ht : subsetCollisionLossOn (fun i ↦ g i+b) T=1)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn (fun i ↦ g i+b) S) ×ˢ (subsetSumImageOn (fun i ↦ g i+b) T)) : Finset (G × G))) :
    (tupleBinaryCollisionCores g b).card=4 := by
  classical
  have hp := disjoint_collision_pair_card_eq_product (fun i ↦ g i+b) S T hd hi
  rw [disjoint_collision_pair_card_eq_three_of_loss_one _ S hs,
    disjoint_collision_pair_card_eq_three_of_loss_one _ T ht] at hp
  have hp' : (subsetDisjointCollisionPairs (fun i ↦ g i+b) (S ∪ T)).card=9 := by
    convert hp using 1
    congr
    exact Subsingleton.elim _ _
  rw [hcover] at hp'
  have hc := twice_binary_core_card_add_one_eq_disjoint_pair_card g hg b
  omega

/-- At the sharp large-midpoint boundary there are exactly four actual
oriented binary collision cores, without choosing a forest. -/
theorem binary_core_card_eq_four_at_midpoint_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (tupleBinaryCollisionCores g b).card=4 := by
  obtain ⟨S,T,hd,hcover,_,_,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  exact binary_core_card_eq_four_of_unit_loss_partition g hg b S T hd hcover hs ht hi

end MinModulus
