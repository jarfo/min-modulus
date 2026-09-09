import MinModulus.BoundaryDoublingBlocks

namespace MinModulus
open Finset
open scoped Classical

/-- A doubling edge cannot cross the two sides of a complementary
collision inside a loss-one block. No validity hypothesis is needed. -/
theorem no_doubling_across_loss_one_collision_parts
    {α G : Type*} [AddCommGroup G] (x : α → G) (S A B : Finset α)
    (hS : subsetCollisionLossOn x S=1) (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hd : Disjoint A B) (he : (∑ i ∈ A, x i)=(∑ i ∈ B, x i))
    (u v : α) (hu : u ∈ A) (hv : v ∈ B) : 2 • x u ≠ x v := by
  classical
  intro hdouble
  have huB : u ∉ B := fun h ↦ Finset.disjoint_left.mp hd hu h
  have hvA : v ∉ A := fun h ↦ Finset.disjoint_left.mp hd h hv
  have hne : v ≠ u := by intro h; subst v; exact huB hv
  let P := insert u (B.erase v)
  let Q := A.erase u
  have hP : P ⊆ S := Finset.insert_subset (hAS hu) ((Finset.erase_subset _ _).trans hBS)
  have hQ : Q ⊆ S := (Finset.erase_subset _ _).trans hAS
  have hPQ : P ≠ Q := by
    intro h
    have humem : u ∈ P := Finset.mem_insert_self _ _
    rw [h] at humem
    exact (Finset.notMem_erase _ _) humem
  have hsum : (∑ i ∈ P, x i)=(∑ i ∈ Q, x i) := by
    have hA := Finset.sum_erase_add A x hu
    have hB := Finset.sum_erase_add B x hv
    have hunot : u ∉ B.erase v := fun h ↦ huB (Finset.mem_erase.mp h).2
    dsimp only [P,Q]
    rw [Finset.sum_insert hunot]
    rw [two_nsmul] at hdouble
    calc
      x u+(∑ i ∈ B.erase v, x i)=(∑ i ∈ B, x i)-x v+x u := by rw [← hB]; abel
      _=(∑ i ∈ A, x i)-(x u+x u)+x u := by rw [← he,← hdouble]
      _=(∑ i ∈ A, x i)-x u := by abel
      _=∑ i ∈ A.erase u, x i := by rw [← hA]; abel
  have hfull := (complementary_subsets_of_loss_one_collision x S P Q hS hP hQ hPQ hsum).2
  have hvfull : v ∈ P ∪ Q := by rw [hfull]; exact hBS hv
  rcases Finset.mem_union.mp hvfull with hp | hq
  · simp only [P,Finset.mem_insert,Finset.mem_erase] at hp
    exact hp.elim hne (fun h ↦ h.1 rfl)
  · exact hvA (Finset.mem_erase.mp hq).2

/-- Within a loss-one block, doubling preserves each side of its
complementary collision. -/
theorem doubling_preserves_loss_one_collision_part
    {α G : Type*} [AddCommGroup G] (x : α → G) (S A B : Finset α)
    (hS : subsetCollisionLossOn x S=1) (hAB : A ∪ B=S) (hd : Disjoint A B)
    (he : (∑ i ∈ A, x i)=(∑ i ∈ B, x i))
    (u v : α) (hu : u ∈ A) (hv : v ∈ S) (hdouble : 2 • x u=x v) : v ∈ A := by
  have hvmem : v ∈ A ∪ B := by rw [hAB]; exact hv
  rcases Finset.mem_union.mp hvmem with h | h
  · exact h
  · exact False.elim (no_doubling_across_loss_one_collision_parts x S A B hS
      (hAB ▸ Finset.subset_union_left) (hAB ▸ Finset.subset_union_right) hd he u v hu h hdouble)

/-- A loss-one block closed under doubling splits into its unique
complementary collision parts, each still closed under doubling. -/
theorem exists_loss_one_collision_parts_closed_under_doubling
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hS : subsetCollisionLossOn x S=1)
    (hclosed : ∀ u ∈ S, ∀ v, 2 • x u=x v → v ∈ S) :
    ∃ A B : Finset α, Disjoint A B ∧ A ∪ B=S ∧ A ≠ B ∧
      (∑ i ∈ A, x i)=(∑ i ∈ B, x i) ∧
      (∀ u ∈ A, ∀ v, 2 • x u=x v → v ∈ A) ∧
      (∀ u ∈ B, ∀ v, 2 • x u=x v → v ∈ B) := by
  obtain ⟨z,A,B,hAS,hBS,hne,hd,hAB,hA,hB,_,_,_⟩ :=
    exists_complementary_double_fibre_of_loss_one x S hS
  refine ⟨A,B,hd,hAB,hne,hA.trans hB.symm,?_,?_⟩
  · intro u hu v he
    exact doubling_preserves_loss_one_collision_part x S A B hS hAB hd
      (hA.trans hB.symm) u v hu (hclosed u (hAS hu) v he) he
  · intro u hu v he
    exact doubling_preserves_loss_one_collision_part x S B A hS (by rw [Finset.union_comm,hAB]) hd.symm
      (hB.trans hA.symm) u v hu (hclosed u (hBS hu) v he) he

/-- Without validity or a chosen forest, the balanced boundary partition
refines into four complementary collision parts preserved by every
shifted doubling edge. Empty parts are allowed. -/
theorem exists_boundary_four_collision_parts_closed_under_doubling
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T A B C D : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) S=1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) T=1 ∧
      Disjoint A B ∧ Disjoint C D ∧ A ∪ B=S ∧ C ∪ D=T ∧
      (∑ i ∈ A, (g i+b))=(∑ i ∈ B, (g i+b)) ∧
      (∑ i ∈ C, (g i+b))=(∑ i ∈ D, (g i+b)) ∧
      (∀ u v, 2 • (g u+b)=g v+b →
        (u ∈ A → v ∈ A) ∧ (u ∈ B → v ∈ B) ∧ (u ∈ C → v ∈ C) ∧ (u ∈ D → v ∈ D)) := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hS,hT,hcross⟩ :=
    exists_boundary_balanced_blocks_without_cross_doubling hn g b z hmid hlarge hboundary
  have hclosedS : ∀ u ∈ S, ∀ v, 2 • (g u+b)=g v+b → v ∈ S := by
    intro u hu v he
    have hv : v ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hv
    · exact False.elim ((hcross u hu v hv).1 he)
  have hclosedT : ∀ u ∈ T, ∀ v, 2 • (g u+b)=g v+b → v ∈ T := by
    intro u hu v he
    have hv : v ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hv with hv | hv
    · exact False.elim ((hcross v hv u hu).2 he)
    · exact hv
  obtain ⟨A,B,hdAB,hAB,_,hA,hAc,hBc⟩ :=
    exists_loss_one_collision_parts_closed_under_doubling (fun i ↦ g i+b) S hS hclosedS
  obtain ⟨C,D,hdCD,hCD,_,hC,hCc,hDc⟩ :=
    exists_loss_one_collision_parts_closed_under_doubling (fun i ↦ g i+b) T hT hclosedT
  refine ⟨S,T,A,B,C,D,hd,hcover,hsizeS,hsizeT,hS,hT,hdAB,hdCD,?_,?_,hA,hC,?_⟩
  · convert hAB using 1; congr; exact Subsingleton.elim _ _
  · convert hCD using 1; congr; exact Subsingleton.elim _ _
  · intro u v he
    exact ⟨fun hu ↦ hAc u hu v he,fun hu ↦ hBc u hu v he,
      fun hu ↦ hCc u hu v he,fun hu ↦ hDc u hu v he⟩

end MinModulus
