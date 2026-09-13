import research.QuarticResidualGraph

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- The actual single-repeat fibre admits a simultaneous choice of
residual supports with their exact sizes, avoidance and value equations. -/
theorem exists_residual_family_of_single_repeat_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (x : G) :
    ∃ B : Fin n → Finset (Fin n),
      (∀ a ∈ singleRepeatFibre g k x, (B a).card=k) ∧
      (∀ a ∈ singleRepeatFibre g k x, a ∉ B a) ∧
      (∀ a ∈ singleRepeatFibre g k x, 2 • g a+(∑ i ∈ B a, g i)=x) := by
  classical
  let R := singleRepeatFibre g k x
  have hex : ∀ a ∈ R, ∃ S : Finset (Fin n),
      a ∈ S ∧ S.card=k+1 ∧ (∑ i ∈ S, g i)+g a=x := by
    intro a ha
    exact (mem_singleRepeatFibre g x a).mp ha
  let S : Fin n → Finset (Fin n) := fun a ↦
    if ha : a ∈ R then Classical.choose (hex a ha) else ∅
  have hS : ∀ a ∈ R, a ∈ S a ∧ (S a).card=k+1 ∧ (∑ i ∈ S a, g i)+g a=x := by
    intro a ha
    simpa only [S,dif_pos ha] using Classical.choose_spec (hex a ha)
  refine ⟨fun a ↦ (S a).erase a,?_,?_,?_⟩
  · intro a ha
    rw [Finset.card_erase_of_mem (hS a ha).1,(hS a ha).2.1]
    omega
  · intro a _
    exact Finset.notMem_erase a (S a)
  · intro a ha
    have he := Finset.sum_erase_add (S a) g (hS a ha).1
    calc
      _ = ((∑ i ∈ (S a).erase a, g i)+g a)+g a := by simp only [two_nsmul]; abel
      _ = (∑ i ∈ S a, g i)+g a := by rw [he]
      _ = x := (hS a ha).2.2

/-- The residual graph of a valid quartic fibre has exactly one edge per
anchor, since distinct anchors have distinct residual pairs. -/
theorem residual_graph_edge_card
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x) :
    Nat.card (residualFamilyGraph R B).edgeSet=R.card := by
  classical
  let H := residualFamilyGraph R B
  have hinj : Function.Injective (fun e : Sym2 (Fin n) ↦ e.toFinset) := by
    intro e f hef
    change e.toFinset=f.toFinset at hef
    apply Sym2.ext
    intro a
    rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset,hef]
  have himage : H.edgeFinset.image (fun e ↦ e.toFinset)=R.image B := by
    ext S
    constructor
    · intro hS
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hS
      have he' : e ∈ H.edgeSet := by simpa using he
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨_,a,ha,hB⟩ := he'
        exact Finset.mem_image.mpr ⟨a,ha,hB.trans Sym2.toFinset_mk_eq.symm⟩
    · intro hS
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨u,v,huv,hB⟩ := Finset.card_eq_two.mp (hc a ha)
      refine Finset.mem_image.mpr ⟨s(u,v),?_,?_⟩
      · apply SimpleGraph.mem_edgeFinset.mpr
        exact ⟨huv,a,ha,hB⟩
      · exact Sym2.toFinset_mk_eq.trans hB.symm
  have hB : Set.InjOn B R := by
    intro a ha b hb he
    exact residual_support_determines_anchor g hg hd x R B hv a b ha hb he
  change Nat.card H.edgeSet=R.card
  rw [Nat.card_eq_fintype_card,← H.edgeFinset_card,
    ← Finset.card_image_of_injective _ hinj,himage,Finset.card_image_iff.mpr hB]

end MinModulus.Research
