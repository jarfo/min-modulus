import research.ResidualGraphOddBalances
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false
namespace MinModulus.Research

/-- A nonempty finite graph all of whose vertex degrees are even contains
a cycle. Isolated vertices do not affect this assertion. -/
theorem exists_cycle_of_even_degrees {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hne : H ≠ ⊥) (heven : ∀ v, Even (H.degree v)) :
    ∃ v, ∃ w : H.Walk v v, w.IsCycle := by
  classical
  by_contra hno
  have hforest : H.IsAcyclic := by
    intro v w hw
    exact hno ⟨v,w,hw⟩
  have hex : ∃ u v, H.Adj u v := by
    by_contra hh
    apply hne
    ext u v
    simp only [SimpleGraph.bot_adj,iff_false]
    exact fun huv ↦ hh ⟨u,v,huv⟩
  obtain ⟨u,v,huv⟩ := hex
  let C := H.connectedComponentMk u
  have hu : u ∈ C.supp := rfl
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu huv
  let _ : Nontrivial C := ⟨⟨⟨u,hu⟩,⟨v,hv⟩,fun h ↦ huv.ne (congrArg Subtype.val h)⟩⟩
  let _ : Fintype C := Fintype.ofFinite C
  have ht := hforest.isTree_connectedComponent C
  obtain ⟨a,ha⟩ := ht.exists_vert_degree_one_of_nontrivial
  have hsub : H.neighborSet a.val ⊆ C.supp := by
    intro b hb
    exact C.mem_supp_of_adj_mem_supp a.property hb
  have hd : C.toSimpleGraph.degree a=H.degree a.val := by
    rw [← C.toSimpleGraph.card_neighborSet_eq_degree a,← H.card_neighborSet_eq_degree a.val]
    simp only [← Nat.card_eq_fintype_card]
    change Nat.card ((H.induce C.supp).neighborSet a)=Nat.card (H.neighborSet a.val)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := C.supp) (v := a) hsub)
  have he := heven a.val
  rw [← hd,ha] at he
  norm_num at he

/-- If every two cycles of a finite graph share an edge, every nonempty
subgraph with even degrees consists of the edges of one cycle. -/
theorem even_subgraph_eq_cycle_of_cycles_share_edge
    {V : Type*} [Fintype V] (G H : SimpleGraph V) [DecidableRel H.Adj]
    (hle : H ≤ G)
    (hshare : ∀ {u v} (p : G.Walk u u) (q : G.Walk v v),
      p.IsCycle → q.IsCycle → ∃ e, e ∈ p.edges ∧ e ∈ q.edges)
    (hne : H ≠ ⊥) (heven : ∀ v, Even (H.degree v)) :
    ∃ u, ∃ p : H.Walk u u, p.IsCycle ∧ H=p.toSubgraph.spanningCoe := by
  classical
  obtain ⟨u,p,hp⟩ := exists_cycle_of_even_degrees H hne heven
  let F := p.toSubgraph.spanningCoe
  have hFH : F ≤ H := p.toSubgraph.spanningCoe_le
  have hFeven (v : V) : Even (F.degree v) := by
    by_cases hne : (F.neighborSet v).Nonempty
    · have hh := hp.isCycles_spanningCoe_toSubgraph hne
      have hd : F.degree v=2 := by
        change (F.neighborSet v).toFinset.card=2
        simpa only [F,Set.ncard_eq_toFinset_card'] using hh
      rw [hd]
      decide
    · have hh : F.neighborSet v=∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hd : F.degree v=0 := by
        rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hh]
        simp
      rw [hd]
      decide
  let J := H \ F
  have hJeven (v : V) : Even (J.degree v) := by
    have hsub : F.neighborFinset v ⊆ H.neighborFinset v := by
      intro b hb
      exact (H.mem_neighborFinset v b).mpr (hFH ((F.mem_neighborFinset v b).mp hb))
    change Even ((H \ F).neighborFinset v).card
    have hfin : (H \ F).neighborFinset v=H.neighborFinset v \ F.neighborFinset v := by
      ext b
      simp
    rw [hfin,Finset.card_sdiff_of_subset hsub]
    rcases heven v with ⟨r,hr⟩
    rcases hFeven v with ⟨s,hs⟩
    refine ⟨r-s,?_⟩
    change H.degree v-F.degree v=(r-s)+(r-s)
    omega
  have hJ : J=⊥ := by
    by_contra hJ
    obtain ⟨v,q,hq⟩ := exists_cycle_of_even_degrees J hJ hJeven
    have hJG : J ≤ G := le_trans sdiff_le hle
    obtain ⟨e,hep,heq⟩ := hshare (p.mapLe hle) (q.mapLe hJG)
      (hp.mapLe hle) (hq.mapLe hJG)
    simp only [SimpleGraph.Walk.edges_mapLe_eq_edges] at hep heq
    have heJ := q.edges_subset_edgeSet heq
    have heF : e ∈ F.edgeSet := by
      rw [SimpleGraph.Subgraph.edgeSet_spanningCoe]
      exact p.mem_edges_toSubgraph.mpr hep
    have hh : e ∉ F.edgeSet := (SimpleGraph.edgeSet_sdiff H F ▸ heJ).2
    exact hh heF
  refine ⟨u,p,hp,le_antisymm ?_ hFH⟩
  exact sdiff_eq_bot_iff.mp hJ

/-- In a finite graph whose cycles are odd and pairwise share an edge,
a subgraph with even degrees and an even edge count must be empty. -/
theorem even_degree_even_edge_subgraph_eq_bot
    {V : Type*} [Fintype V] (G H : SimpleGraph V) [DecidableRel H.Adj]
    (hle : H ≤ G)
    (hshare : ∀ {u v} (p : G.Walk u u) (q : G.Walk v v),
      p.IsCycle → q.IsCycle → ∃ e, e ∈ p.edges ∧ e ∈ q.edges)
    (hodd : ∀ {u} (p : G.Walk u u), p.IsCycle → Odd p.length)
    (heven : ∀ v, Even (H.degree v))
    (hcard : Even (Nat.card H.edgeSet)) : H=⊥ := by
  classical
  by_contra hne
  obtain ⟨u,p,hp,hH⟩ := even_subgraph_eq_cycle_of_cycles_share_edge G H hle hshare hne heven
  have heq := congrArg (fun K : SimpleGraph V ↦ K.edgeSet) hH
  have hedge : H.edgeFinset=p.edges.toFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,heq,SimpleGraph.Subgraph.edgeSet_spanningCoe,
      p.mem_edges_toSubgraph,List.mem_toFinset]
  have hcount : Nat.card H.edgeSet=p.length := by
    calc
      _ = H.edgeFinset.card := by rw [Nat.card_eq_fintype_card,H.edgeFinset_card]
      _ = p.edges.toFinset.card := congrArg Finset.card hedge
      _ = p.edges.length := List.toFinset_card_of_nodup hp.isTrail.edges_nodup
      _ = p.length := p.length_edges
  have ho : Odd p.length := by
    have hlen : (p.mapLe hle).length=p.length := by
      calc
        _ = (p.mapLe hle).edges.length := (p.mapLe hle).length_edges.symm
        _ = p.edges.length := congrArg List.length (p.edges_mapLe_eq_edges hle)
        _ = p.length := p.length_edges
    simpa only [hlen] using hodd (p.mapLe hle) (hp.mapLe hle)
  rw [hcount] at hcard
  exact (Nat.not_even_iff_odd.mpr ho) hcard

end MinModulus.Research
