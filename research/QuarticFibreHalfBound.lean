import research.ResidualGraphCounting

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace MinModulus.Research
open Finset

/-- A quartic single-repeat family occupies at most half the coordinates,
in every valid tuple in a group with injective doubling. -/
theorem quartic_single_repeat_family_twice_card_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x) :
    2*R.card ≤ n := by
  classical
  let U := Rᶜ
  let H := residualFamilyGraph R B
  let K := H.induce (U : Set (Fin n))
  let φ : K →g H := ⟨Subtype.val,fun h ↦ h⟩
  have hφ : Function.Injective φ := Subtype.val_injective
  have hshare : ∀ {u v} (p : K.Walk u u) (q : K.Walk v v),
      p.IsCycle → q.IsCycle → ∃ e, e ∈ p.edges ∧ e ∈ q.edges := by
    intro u v p q hp hq
    obtain ⟨e,hep,heq⟩ := residual_graph_cycles_share_edge g hg hd x R B hc ha hv
      (p.map φ) (hp.map hφ) (q.map φ) (hq.map hφ)
    rw [SimpleGraph.Walk.edges_map] at hep heq
    obtain ⟨ep,hep,hpe⟩ := List.mem_map.mp hep
    obtain ⟨eq,heq,hqe⟩ := List.mem_map.mp heq
    have he : ep=eq := Sym2.map.injective hφ (hpe.trans hqe.symm)
    exact ⟨ep,hep,he.symm ▸ heq⟩
  have hodd : ∀ {u} (p : K.Walk u u), p.IsCycle → Odd p.length := by
    intro u p hp
    have h := residual_graph_cycle_odd g hg hd x R B hc hv (p.map φ) (hp.map hφ)
    simpa only [SimpleGraph.Walk.length_map] using h
  have hs : H.support ⊆ (U : Set (Fin n)) := by
    intro v hvs
    obtain ⟨w,hw⟩ := H.mem_support.mp hvs
    exact Finset.mem_compl.mpr (residual_graph_adj_outside_anchor_family g hg x R B hc ha hv v w hw).1
  have hKcount : Nat.card K.edgeSet=Nat.card H.edgeSet := by
    have hh := SimpleGraph.card_edgeFinset_induce_of_support_subset
      (G := H) (s := (U : Set (Fin n))) hs
    change Nat.card (H.induce (U : Set (Fin n))).edgeSet=Nat.card H.edgeSet
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hh
  have hcount : Nat.card K.edgeSet=R.card := hKcount.trans
    (residual_graph_edge_card g hg hd x R B hc hv)
  have h := card_edges_le_vertices_of_odd_cycles_share_edge K hshare hodd
  rw [hcount] at h
  have hu : Fintype.card (U : Set (Fin n))=n-R.card := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card U=n-R.card
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    simp only [U,Finset.card_compl,Fintype.card_fin]
  rw [hu] at h
  have hR : R.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ R
  omega

/-- Every actual quartic single-repeat fibre has at most half as many
anchors as the tuple has coordinates. -/
theorem quartic_single_repeat_fibre_twice_card_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z)) (x : G) :
    2*(singleRepeatFibre g 2 x).card ≤ n := by
  classical
  obtain ⟨B,hc,ha,hv⟩ := exists_residual_family_of_single_repeat_fibre (k := 2) g x
  exact quartic_single_repeat_family_twice_card_le g hg hd x (singleRepeatFibre g 2 x) B hc ha hv

end MinModulus.Research
