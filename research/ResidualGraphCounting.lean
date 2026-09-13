import research.ResidualGraphParity

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace MinModulus.Research
open Finset
open scoped symmDiff

/-- Odd cycles that pairwise share an edge force the edge count of a
finite simple graph to be at most its vertex count. -/
theorem card_edges_le_vertices_of_odd_cycles_share_edge
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hshare : ∀ {u v} (p : G.Walk u u) (q : G.Walk v v),
      p.IsCycle → q.IsCycle → ∃ e, e ∈ p.edges ∧ e ∈ q.edges)
    (hodd : ∀ {u} (p : G.Walk u u), p.IsCycle → Odd p.length) :
    Nat.card G.edgeSet ≤ Fintype.card V := by
  classical
  by_cases hV : Nonempty V
  swap
  · have hempty : IsEmpty V := not_nonempty_iff.mp hV
    have hbot : G=⊥ := by ext u v; exact isEmptyElim u
    rw [hbot]
    simp
  let _ : Nonempty V := hV
  let v0 : V := Classical.arbitrary V
  have even_diff (S T : Finset (Sym2 V))
      (h : Odd S.card ↔ Odd T.card) : Even (S ∆ T).card := by
    have hd : Disjoint (S \ T) (T \ S) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
    have hc : (S ∆ T).card=(S \ T).card+(T \ S).card := by
      rw [symmDiff_def]
      change (S \ T ∪ T \ S).card=(S \ T).card+(T \ S).card
      exact Finset.card_union_of_disjoint hd
    have hs := Finset.card_sdiff_add_card_inter S T
    have ht := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at ht
    simp only [Nat.odd_iff] at h
    rw [Nat.even_iff]
    omega
  let code : Finset (Sym2 V) → Finset V := fun S ↦
    Finset.univ.filter (fun v ↦ if v=v0 then Odd S.card else Odd (S.filter (fun e ↦ v ∈ e)).card)
  have hinj : Set.InjOn code G.edgeFinset.powerset := by
    intro S hS T hT hcode
    have hS := Finset.mem_powerset.mp hS
    have hT := Finset.mem_powerset.mp hT
    let D := S ∆ T
    have hDG : D ⊆ G.edgeFinset := by
      intro e he
      rcases Finset.mem_symmDiff.mp he with he | he
      · exact hS he.1
      · exact hT he.1
    have hcard : Even D.card := by
      apply even_diff S T
      have h := Finset.ext_iff.mp hcode v0
      simpa [code] using h
    let H := SimpleGraph.fromEdgeSet (D : Set (Sym2 V))
    have hedge : H.edgeFinset=D := by
      ext e
      change e ∈ (SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).edgeFinset ↔ e ∈ D
      rw [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · exact fun h ↦ h.1
      · intro he
        exact ⟨he,G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hDG he))⟩
    have hle : H ≤ G := by
      intro u v huv
      exact (SimpleGraph.mem_edgeFinset.mp (hDG huv.1) : s(u,v) ∈ G.edgeSet)
    have hdeg (v : V) : H.degree v=(D.filter (fun e ↦ v ∈ e)).card := by
      rw [← H.card_incidenceFinset_eq_degree v,H.incidenceFinset_eq_filter v,hedge]
    have heven (v : V) (hv : v ≠ v0) : Even (H.degree v) := by
      have hc : Odd (S.filter (fun e ↦ v ∈ e)).card ↔ Odd (T.filter (fun e ↦ v ∈ e)).card := by
        have h := Finset.ext_iff.mp hcode v
        simpa only [code,Finset.mem_filter,Finset.mem_univ,true_and,if_neg hv] using h
      have hf : D.filter (fun e ↦ v ∈ e)=
          (S.filter (fun e ↦ v ∈ e)) ∆ (T.filter (fun e ↦ v ∈ e)) := by
        ext e
        simp only [D,Finset.mem_filter,Finset.mem_symmDiff]
        tauto
      rw [hdeg,hf]
      exact even_diff _ _ hc
    have hall (v : V) : Even (H.degree v) := by
      by_cases hv : v=v0
      · subst v
        by_contra hno
        obtain ⟨w,hw,ho⟩ := H.exists_ne_odd_degree_of_exists_odd_degree v0
          (Nat.not_even_iff_odd.mp hno)
        exact (Nat.not_even_iff_odd.mpr ho) (heven w hw)
      · exact heven v hv
    have hcard' : Even (Nat.card H.edgeSet) := by
      rw [Nat.card_eq_fintype_card,← H.edgeFinset_card,hedge]
      exact hcard
    have hbot := even_degree_even_edge_subgraph_eq_bot G H hle hshare hodd hall hcard'
    have hD : D=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hmem : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp (by rwa [hedge])
      have hh : H.edgeSet=∅ := by rw [hbot]; simp
      exact (hh ▸ hmem : e ∈ (∅ : Set (Sym2 V)))
    exact Finset.symmDiff_eq_empty.mp hD
  have hcount : 2^G.edgeFinset.card ≤ 2^Fintype.card V := by
    calc
      _ = (G.edgeFinset.powerset.image code).card := by
        rw [Finset.card_image_iff.mpr hinj,Finset.card_powerset]
      _ ≤ Fintype.card (Finset V) := Finset.card_le_univ _
      _ = _ := Fintype.card_finset
  rw [Nat.card_eq_fintype_card,← G.edgeFinset_card]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcount

end MinModulus.Research
