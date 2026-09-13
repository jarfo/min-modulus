import research.ResidualGraphCycles

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- An odd closed trail gives a rooted balance, using disjoint anchor
sets whose supports are edges of the trail. -/
theorem residual_odd_trail_rooted_balance {n : ℕ}
    (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    {p : Fin n} (w : (residualFamilyGraph R B).Walk p p)
    (hw : w.IsTrail) (ho : Odd w.length) :
    ∃ P Q : Finset (Fin n), P ⊆ R ∧ Q ⊆ R ∧ Disjoint P Q ∧
      (∑ a ∈ P, (B a).val)=(∑ a ∈ Q, (B a).val)+(p ::ₘ p ::ₘ 0) ∧
      ∀ a ∈ P ∪ Q, ∃ e ∈ w.edges, e.toFinset=B a := by
  classical
  obtain ⟨m,hm⟩ := ho
  obtain ⟨l,hl,hlR,hlB⟩ := residual_trail_anchor_labels R B w hw
  let ev : Fin (m+1) → Fin w.length := fun i ↦ ⟨2*i.val,by omega⟩
  let od : Fin m → Fin w.length := fun i ↦ ⟨2*i.val+1,by omega⟩
  let a := fun i ↦ l (ev i)
  let b := fun i ↦ l (od i)
  have ha : Function.Injective a := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [ev] at h
    exact Fin.ext (by omega)
  have hb : Function.Injective b := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [od] at h
    exact Fin.ext (by omega)
  have hdis : ∀ i j, a i ≠ b j := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [ev,od] at h
    omega
  let P := Finset.univ.image a
  let Q := Finset.univ.image b
  refine ⟨P,Q,?_,?_,?_,?_,?_⟩
  · intro c hh
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    exact hlR (ev i)
  · intro c hh
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    exact hlR (od i)
  · apply Finset.disjoint_left.mpr
    intro c hc hd
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨j,_,hh⟩ := Finset.mem_image.mp hd
    exact hdis i j hh.symm
  · have he (i : Fin m) : (B (a i.castSucc)).val=
        w.getVert (2*i.castSucc.val) ::ₘ w.getVert (2*i.val+1) ::ₘ 0 := hlB (ev i.castSucc)
    have hf (i : Fin m) : (B (b i)).val=
        w.getVert (2*i.val+1) ::ₘ w.getVert (2*i.succ.val) ::ₘ 0 := by
      convert hlB (od i) using 1 <;> simp only [od,Fin.val_succ] <;> congr 2 <;> omega
    have hlast : (B (a (Fin.last m))).val=
        w.getVert (2*(Fin.last m).val) ::ₘ w.getVert (2*(0 : Fin (m+1)).val) ::ₘ 0 := by
      simpa only [a,ev,Fin.val_last,Fin.val_zero,mul_zero,← hm,
        w.getVert_length,w.getVert_zero] using hlB (ev (Fin.last m))
    have h := odd_residual_cycle_balance B a (fun i : Fin (m+1) ↦ w.getVert (2*i.val))
      b (fun i : Fin m ↦ w.getVert (2*i.val+1)) ha hb he hf hlast
    simpa only [Fin.val_zero,mul_zero,w.getVert_zero] using h
  · intro c hc
    have hex : ∃ j : Fin w.length, l j=c := by
      rcases Finset.mem_union.mp hc with hh | hh
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh
        exact ⟨ev i,hi⟩
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh
        exact ⟨od i,hi⟩
    obtain ⟨j,rfl⟩ := hex
    refine ⟨s(w.getVert j,w.getVert (j+1)),?_,?_⟩
    · have he : w.edges[j.val]'(by simpa only [SimpleGraph.Walk.length_edges] using j.isLt)=
          s(w.getVert j,w.getVert (j+1)) := by
        simp [SimpleGraph.Walk.edges,SimpleGraph.Walk.darts_getElem_eq_getVert]
      rw [← he]
      exact List.getElem_mem _
    · rw [Sym2.toFinset_mk_eq]
      have he := congrArg Multiset.toFinset (hlB j)
      simpa using he.symm

/-- Two cycles of a valid single-repeat quartic residual graph share an
edge, even when their base vertices or connected components differ. -/
theorem residual_graph_cycles_share_edge
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    {p q : Fin n}
    (w : (residualFamilyGraph R B).Walk p p) (hw : w.IsCycle)
    (z : (residualFamilyGraph R B).Walk q q) (hz : z.IsCycle) :
    ∃ e, e ∈ w.edges ∧ e ∈ z.edges := by
  classical
  obtain ⟨P,Q,hP,hQ,_,he,hwe⟩ := residual_odd_trail_rooted_balance R B w hw.isTrail
    (residual_graph_cycle_odd g hg hd x R B hc hv w hw)
  obtain ⟨U,V,hU,hV,_,hf,hze⟩ := residual_odd_trail_rooted_balance R B z hz.isTrail
    (residual_graph_cycle_odd g hg hd x R B hc hv z hz)
  have hp : p ∉ R := by
    have hadj := w.adj_getVert_succ (by have := hw.three_le_length; omega : 0 < w.length)
    have h := residual_graph_adj_outside_anchor_family g hg x R B hc ha hv _ _ hadj
    simpa using h.1
  have hq : q ∉ R := by
    have hadj := z.adj_getVert_succ (by have := hz.three_le_length; omega : 0 < z.length)
    have h := residual_graph_adj_outside_anchor_family g hg x R B hc ha hv _ _ hadj
    simpa using h.1
  have hnot := quartic_rooted_residual_balances_share_anchor g hg hd x R B hc hv
    P Q U V hP hQ hU hV p q hp hq he hf
  have hi : ((P ∪ Q) ∩ (U ∪ V)).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hnot
  obtain ⟨a,haI⟩ := hi
  obtain ⟨haw,haz⟩ := Finset.mem_inter.mp haI
  obtain ⟨e,hew,heB⟩ := hwe a haw
  obtain ⟨f,hfz,hfB⟩ := hze a haz
  have hef : e=f := by
    apply Sym2.ext
    intro a
    rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset,heB,hfB]
  exact ⟨e,hew,hef.symm ▸ hfz⟩

end MinModulus.Research
