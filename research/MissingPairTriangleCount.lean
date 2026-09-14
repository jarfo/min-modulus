import research.LinearBlockTriangleCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A fixed coordinate pair lies in at most n-2 three-element supports. -/
theorem pair_containing_triples_card_le
    {n : ℕ} (P : Finset (Fin n)) (hP : P.card=2) :
    (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun T ↦ P ⊆ T)).card ≤ n-2 := by
  classical
  let Ts := ((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun T ↦ P ⊆ T)
  have hmap : ∀ T ∈ Ts, T \ P ∈ ((Finset.univ : Finset (Fin n)) \ P).powersetCard 1 := by
    intro T hT
    obtain ⟨hT,hPT⟩ := Finset.mem_filter.mp hT
    have hTc := (Finset.mem_powersetCard.mp hT).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hi).2⟩
    · rw [Finset.card_sdiff_of_subset hPT,hTc,hP]
  have hfi : Set.InjOn (fun T ↦ T \ P) Ts := by
    intro A hA B hB he
    change A \ P=B \ P at he
    have hPA := (Finset.mem_filter.mp hA).2
    have hPB := (Finset.mem_filter.mp hB).2
    calc
      A = (A \ P) ∪ P := (Finset.sdiff_union_of_subset hPA).symm
      _ = (B \ P) ∪ P := by rw [he]
      _ = B := Finset.sdiff_union_of_subset hPB
  have hc := Finset.card_le_card_of_injOn (fun T ↦ T \ P) hmap hfi
  simpa only [Finset.card_powersetCard,Nat.choose_one_right,
    Finset.card_sdiff_of_subset (Finset.subset_univ P),Finset.card_univ,Fintype.card_fin,hP] using hc

/-- If a family contains every triple avoiding a given set of missing
pairs, each missing pair costs at most n-2 triangles. -/
theorem triangle_family_card_add_missing_pair_bound
    {n : ℕ} (Ts D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hTs : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
      (∀ P ∈ D, ¬ P ⊆ T) → T ∈ Ts) :
    n.choose 3 ≤ Ts.card+(n-2)*D.card := by
  classical
  let U := (Finset.univ : Finset (Fin n)).powersetCard 3
  let B := D.biUnion (fun P ↦ U.filter (fun T ↦ P ⊆ T))
  have hcover : U ⊆ Ts∪B := by
    intro T hT
    by_cases hB : T ∈ B
    · exact Finset.mem_union_right _ hB
    · apply Finset.mem_union_left
      apply hTs T hT
      intro P hP hPT
      exact hB (Finset.mem_biUnion.mpr ⟨P,hP,Finset.mem_filter.mpr ⟨hT,hPT⟩⟩)
  have hBc : B.card ≤ (n-2)*D.card := by
    calc
      _ ≤ ∑ P ∈ D, (U.filter (fun T ↦ P ⊆ T)).card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ D, (n-2) := by
        apply Finset.sum_le_sum
        intro P hP
        exact pair_containing_triples_card_le P (hD P hP)
      _ = _ := by simp [Nat.mul_comm]
  have h₀ := Finset.card_le_card hcover
  have h₁ := Finset.card_union_le Ts B
  have hU : U.card=n.choose 3 := by simp [U]
  omega

end MinModulus.Research
