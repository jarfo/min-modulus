import research.SingleRepeatGraphRealization
import research.ResidualCycleBalances
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Every trail in a residual graph has distinct anchor labels for its
successive edges. No validity assumptions are required for this labeling. -/
theorem residual_trail_anchor_labels {n : ℕ}
    (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    {u v : Fin n} (w : (residualFamilyGraph R B).Walk u v) (hw : w.IsTrail) :
    ∃ a : Fin w.length → Fin n, Function.Injective a ∧
      (∀ i, a i ∈ R) ∧
      (∀ i, (B (a i)).val=w.getVert i ::ₘ w.getVert (i+1) ::ₘ 0) := by
  classical
  have hex (i : Fin w.length) : ∃ a ∈ R,
      B a={w.getVert i,w.getVert (i+1)} := (w.adj_getVert_succ i.isLt).2
  choose a ha hB using hex
  refine ⟨a,?_,ha,?_⟩
  · intro i j hij
    have he : s(w.getVert i,w.getVert (i+1))=s(w.getVert j,w.getVert (j+1)) := by
      apply Sym2.ext
      intro b
      have h := (hB i).symm.trans ((congrArg B hij).trans (hB j))
      simpa only [Sym2.mem_iff,Finset.mem_insert,Finset.mem_singleton] using
        (show b ∈ ({w.getVert i,w.getVert (i+1)} : Finset (Fin n)) ↔
          b ∈ ({w.getVert j,w.getVert (j+1)} : Finset (Fin n)) from h ▸ Iff.rfl)
    have hh : w.edges[i.val]'(by simpa only [SimpleGraph.Walk.length_edges] using i.isLt)=
        w.edges[j.val]'(by simpa only [SimpleGraph.Walk.length_edges] using j.isLt) := by
      have edge (i : Fin w.length) :
          w.edges[i.val]'(by simpa only [SimpleGraph.Walk.length_edges] using i.isLt)=
            s(w.getVert i,w.getVert (i+1)) := by
        simp [SimpleGraph.Walk.edges,
          SimpleGraph.Walk.darts_getElem_eq_getVert]
      rw [edge i,edge j]
      exact he
    have hi : (⟨i.val,by simpa only [SimpleGraph.Walk.length_edges] using i.isLt⟩ : Fin w.edges.length)=
        ⟨j.val,by simpa only [SimpleGraph.Walk.length_edges] using j.isLt⟩ :=
      (List.nodup_iff_injective_getElem.mp hw.edges_nodup) hh
    exact Fin.ext (congrArg (fun z : Fin w.edges.length ↦ z.val) hi)
  · intro i
    rw [hB i]
    have hn := (w.adj_getVert_succ i.isLt).1
    simp only [Finset.insert_val,Finset.singleton_val]
    rw [Multiset.ndinsert_of_notMem (by simpa only [Multiset.mem_singleton] using hn)]
    rfl

/-- Every cycle in a valid quartic residual graph has odd length. -/
theorem residual_graph_cycle_odd {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    {p : Fin n} (w : (residualFamilyGraph R B).Walk p p) (hw : w.IsCycle) :
    Odd w.length := by
  classical
  by_contra ho
  have heven : Even w.length := Nat.not_odd_iff_even.mp ho
  obtain ⟨m,hm⟩ := heven
  have hlen : w.length=2*m := by omega
  have hmpos : 0 < m := by have := hw.three_le_length; omega
  obtain ⟨l,hl,hlR,hlB⟩ := residual_trail_anchor_labels R B w hw.isTrail
  let ev : Fin m → Fin w.length := fun i ↦ ⟨2*i.val,by omega⟩
  let od : Fin m → Fin w.length := fun i ↦ ⟨2*i.val+1,by omega⟩
  have hev : Function.Injective (fun i ↦ l (ev i)) := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [ev] at h
    exact Fin.ext (by omega)
  have hod : Function.Injective (fun i ↦ l (od i)) := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [od] at h
    exact Fin.ext (by omega)
  have hdis : ∀ i j, l (ev i) ≠ l (od j) := by
    intro i j h
    have h := congrArg Fin.val (hl h)
    simp only [ev,od] at h
    omega
  apply no_even_residual_cycle hmpos g hg hd x R B hc hv
    (fun i ↦ l (ev i)) (fun i ↦ l (od i))
    (fun i ↦ w.getVert (2*i.val)) (fun i ↦ w.getVert (2*i.val+1))
    (finRotate m) hev hod hdis (fun i ↦ hlR (ev i)) (fun i ↦ hlR (od i))
  · intro i
    exact hlB (ev i)
  · intro i
    have hnext : w.getVert (2*i.val+1+1)=w.getVert (2*(finRotate m i).val) := by
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
      by_cases hi : i=Fin.last t
      · subst i
        simp only [Fin.val_last,finRotate_last,Fin.val_zero,mul_zero]
        rw [show 2*t+1+1=w.length by omega,w.getVert_length,w.getVert_zero]
      · rw [coe_finRotate_of_ne_last hi]
        congr 1
    simpa only [od,hnext] using hlB (od i)

end MinModulus.Research
