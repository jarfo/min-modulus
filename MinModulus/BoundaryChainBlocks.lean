import MinModulus.BoundaryCoreChainSeparation

namespace MinModulus
open Finset
open scoped Classical

/-- Full-support complementary equal-sum subsets at the boundary
separate whole chains, regardless of which side is heavier. -/
theorem boundary_full_support_relation_whole_chains
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (U V : Finset (Fin n)) (hd : Disjoint U V) (hfull : U ∪ V=Finset.univ)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) :
    ∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ U) ∨ (∀ j : Fin (L a), E ⟨a,j⟩ ∈ V) := by
  classical
  have hne : U ≠ V := by
    intro h
    subst V
    have hzero : U=∅ := (Finset.disjoint_self_iff_empty U).mp hd
    have hc := congrArg Finset.card hfull
    simp only [Finset.union_self,Finset.card_univ,Fintype.card_fin,hzero,Finset.card_empty] at hc
    omega
  have hcne : U.card ≠ V.card := by
    intro hc
    exact hne (tuple_subset_fibre_cardinality_injective g hg b (∑ i ∈ U, (g i+b))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm⟩) hc)
  rcases lt_or_gt_of_ne hcne with hc | hc
  · let uv : tupleBinaryCollisionCores g b := ⟨(V,U),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.symm,he.symm,hc⟩⟩
    have hh := boundary_full_support_core_whole_chains hn L hL g hg E x b z hchain hmid hlarge hboundary uv (by
      change V ∪ U=Finset.univ
      rw [Finset.union_comm,hfull])
    intro a
    rcases hh a with h | h
    · exact Or.inr (fun j ↦ (h j).1)
    · exact Or.inl (fun j ↦ (h j).1)
  · let uv : tupleBinaryCollisionCores g b := ⟨(U,V),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,he,hc⟩⟩
    have hh := boundary_full_support_core_whole_chains hn L hL g hg E x b z hchain hmid hlarge hboundary uv (by
      exact hfull)
    intro a
    rcases hh a with h | h
    · exact Or.inl (fun j ↦ (h j).1)
    · exact Or.inr (fun j ↦ (h j).1)

/-- Two transverse unions of disjoint cell pairs distinguish all four
cells: a family lying on one side of each union lies in one cell. -/
theorem whole_family_in_cell_of_two_union_partitions
    {α I : Type*} (A B C D : Finset α) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (f : I → α)
    (hfirst : (∀ i, f i ∈ A ∪ C) ∨ (∀ i, f i ∈ B ∪ D))
    (hsecond : (∀ i, f i ∈ A ∪ D) ∨ (∀ i, f i ∈ B ∪ C)) :
    (∀ i, f i ∈ A) ∨ (∀ i, f i ∈ B) ∨ (∀ i, f i ∈ C) ∨ (∀ i, f i ∈ D) := by
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · left
    intro i
    have h1 := Finset.mem_union.mp (hfirst i)
    have h2 := Finset.mem_union.mp (hsecond i)
    by_contra h
    exact Finset.disjoint_left.mp hCD (h1.resolve_left h) (h2.resolve_left h)
  · right; right; left
    intro i
    have h1 := Finset.mem_union.mp (hfirst i)
    have h2 := Finset.mem_union.mp (hsecond i)
    by_contra h
    exact Finset.disjoint_left.mp hAB (h1.resolve_right h) (h2.resolve_right h)
  · right; right; right
    intro i
    have h1 := Finset.mem_union.mp (hfirst i)
    have h2 := Finset.mem_union.mp (hsecond i)
    by_contra h
    exact Finset.disjoint_left.mp hAB (h2.resolve_right h) (h1.resolve_right h)
  · right; left
    intro i
    have h1 := Finset.mem_union.mp (hfirst i)
    have h2 := Finset.mem_union.mp (hsecond i)
    by_contra h
    exact Finset.disjoint_left.mp hCD (h2.resolve_left h) (h1.resolve_left h)

/-- Complementary equal-sum pairs on disjoint blocks combine to a
complementary equal-sum pair on their union. -/
theorem complementary_collision_pair_across_disjoint_blocks
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T A B C D : Finset α)
    (hd : Disjoint S T) (hAB : A ∪ B=S) (hCD : C ∪ D=T)
    (hdAB : Disjoint A B) (hdCD : Disjoint C D)
    (heAB : (∑ i ∈ A, x i)=(∑ i ∈ B, x i))
    (heCD : (∑ i ∈ C, x i)=(∑ i ∈ D, x i)) :
    Disjoint (A ∪ C) (B ∪ D) ∧ (A ∪ C) ∪ (B ∪ D)=S ∪ T ∧
      (∑ i ∈ A ∪ C, x i)=(∑ i ∈ B ∪ D, x i) := by
  classical
  have hAS : A ⊆ S := hAB ▸ Finset.subset_union_left
  have hBS : B ⊆ S := hAB ▸ Finset.subset_union_right
  have hCT : C ⊆ T := hCD ▸ Finset.subset_union_left
  have hDT : D ⊆ T := hCD ▸ Finset.subset_union_right
  have hAC := hd.mono hAS hCT
  have hAD := hd.mono hAS hDT
  have hBC := hd.mono hBS hCT
  have hBD := hd.mono hBS hDT
  refine ⟨?_,?_,?_⟩
  · simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
    exact ⟨⟨hdAB,hBC.symm⟩,⟨hAD,hdCD⟩⟩
  · rw [← hAB,← hCD]
    ext i
    simp only [Finset.mem_union]
    tauto
  · rw [Finset.sum_union hAC,Finset.sum_union hBD,heAB,heCD]

/-- At the valid sharp midpoint boundary, the balanced loss-one
partition can be chosen so that every original chain stays in one block. -/
theorem exists_boundary_balanced_blocks_containing_whole_chains
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) S=1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) T=1 ∧
      (∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ S) ∨ (∀ j : Fin (L a), E ⟨a,j⟩ ∈ T)) := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hS,hT,_⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  obtain ⟨s,A,B,hAS,hBS,_,hdAB,hAB,hA,hB,_,_,_⟩ :=
    exists_complementary_double_fibre_of_loss_one (fun i ↦ g i+b) S hS
  obtain ⟨t,C,D,hCT,hDT,_,hdCD,hCD,hC,hD,_,_,_⟩ :=
    exists_complementary_double_fibre_of_loss_one (fun i ↦ g i+b) T hT
  have combine (C D : Finset (Fin n)) (hCD : C ∪ D=T) (hdCD : Disjoint C D)
      (heCD : (∑ i ∈ C, (g i+b))=(∑ i ∈ D, (g i+b))) :
      ∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ A ∪ C) ∨ (∀ j : Fin (L a), E ⟨a,j⟩ ∈ B ∪ D) := by
    obtain ⟨hpdis,hpcov,hpeq⟩ := complementary_collision_pair_across_disjoint_blocks
      (fun i ↦ g i+b) S T A B C D hd hAB
      (by convert hCD using 1; congr; exact Subsingleton.elim _ _) hdAB hdCD (hA.trans hB.symm) heCD
    apply boundary_full_support_relation_whole_chains hn L hL g hg E x b z hchain hmid hlarge hboundary
      (A ∪ C) (B ∪ D)
    · convert hpdis using 1 <;> congr <;> exact Subsingleton.elim _ _
    · have hh : (A ∪ C) ∪ (B ∪ D)=S ∪ T := by
        convert hpcov using 1 <;> congr <;> exact Subsingleton.elim _ _
      exact hh.trans hcover
    · convert hpeq using 1 <;> congr <;> exact Subsingleton.elim _ _
  have hfirst := combine C D (by convert hCD using 1; congr; exact Subsingleton.elim _ _)
    hdCD (hC.trans hD.symm)
  have hsecond := combine D C (by
    rw [Finset.union_comm]
    convert hCD using 1; congr; exact Subsingleton.elim _ _) hdCD.symm (hD.trans hC.symm)
  refine ⟨S,T,hd,hcover,hsizeS,hsizeT,hS,hT,?_⟩
  intro a
  have hcells := whole_family_in_cell_of_two_union_partitions A B C D hdAB hdCD
    (fun j : Fin (L a) ↦ E ⟨a,j⟩)
    (by simpa only [Finset.mem_union] using hfirst a)
    (by simpa only [Finset.mem_union] using hsecond a)
  rcases hcells with h | h | h | h
  · exact Or.inl (fun j ↦ hAS (h j))
  · exact Or.inl (fun j ↦ hBS (h j))
  · exact Or.inr (fun j ↦ hCT (h j))
  · exact Or.inr (fun j ↦ hDT (h j))

end MinModulus
