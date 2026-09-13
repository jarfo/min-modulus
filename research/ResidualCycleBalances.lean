import research.ResidualTradeRigidity

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Alternating distinct anchors cannot form an even residual cycle, or
any nonempty union of such alternating cycles. The permutation describes
how the second half of the edges reconnects the first half. -/
theorem no_even_residual_cycle
    {n m : ℕ} {G : Type*} [AddCommGroup G]
    (hm : 0 < m) (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (a b u v : Fin m → Fin n) (σ : Equiv.Perm (Fin m))
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (haR : ∀ i, a i ∈ R) (hbR : ∀ i, b i ∈ R)
    (he : ∀ i, (B (a i)).val=u i ::ₘ v i ::ₘ 0)
    (hf : ∀ i, (B (b i)).val=v i ::ₘ u (σ i) ::ₘ 0) : False := by
  classical
  let P := Finset.univ.image a
  let Q := Finset.univ.image b
  have hP : P ⊆ R := by
    intro c hh
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    exact haR i
  have hQ : Q ⊆ R := by
    intro c hh
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    exact hbR i
  have hsum : (∑ c ∈ P, (B c).val)=(∑ c ∈ Q, (B c).val) := by
    dsimp [P,Q]
    rw [Finset.sum_image (fun i _ j _ hh ↦ ha hh),
      Finset.sum_image (fun i _ j _ hh ↦ hb hh)]
    simp_rw [he,hf,← Multiset.singleton_add,add_zero,Finset.sum_add_distrib]
    rw [Equiv.sum_comp σ (fun i ↦ ({u i} : Multiset (Fin n)))]
    exact add_comm _ _
  have hPQ := residual_aggregate_determines_anchor_subset (by omega : 0 < 2)
    g hg hd x R B hc hv P Q hP hQ hsum
  let i : Fin m := ⟨0,hm⟩
  have hmem : a i ∈ Q := by
    rw [← hPQ]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  obtain ⟨j,_,hji⟩ := Finset.mem_image.mp hmem
  exact hab i j hji.symm

/-- The alternating edges of an odd residual cycle give a rooted balance
with two copies of its initial vertex. -/
theorem odd_residual_cycle_balance {n m : ℕ}
    (B : Fin n → Finset (Fin n))
    (a u : Fin (m+1) → Fin n) (b v : Fin m → Fin n)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (he : ∀ i, (B (a i.castSucc)).val=u i.castSucc ::ₘ v i ::ₘ 0)
    (hf : ∀ i, (B (b i)).val=v i ::ₘ u i.succ ::ₘ 0)
    (hlast : (B (a (Fin.last m))).val=u (Fin.last m) ::ₘ u 0 ::ₘ 0) :
    (∑ c ∈ Finset.univ.image a, (B c).val)=
      (∑ c ∈ Finset.univ.image b, (B c).val)+(u 0 ::ₘ u 0 ::ₘ 0) := by
  classical
  rw [Finset.sum_image (fun i _ j _ hh ↦ ha hh),
    Finset.sum_image (fun i _ j _ hh ↦ hb hh),Fin.sum_univ_castSucc]
  simp_rw [he,hf,hlast,← Multiset.singleton_add,add_zero,Finset.sum_add_distrib]
  have hu : (∑ i : Fin m, ({u i.castSucc} : Multiset (Fin n)))+{u (Fin.last m)}=
      {u 0}+(∑ i : Fin m, ({u i.succ} : Multiset (Fin n))) := by
    exact (Fin.sum_univ_castSucc (fun i : Fin (m+1) ↦ ({u i} : Multiset (Fin n)))).symm.trans
      (Fin.sum_univ_succ (fun i : Fin (m+1) ↦ ({u i} : Multiset (Fin n))))
  calc
    _ = ((∑ i : Fin m, ({u i.castSucc} : Multiset (Fin n)))+{u (Fin.last m)})+
        (∑ i : Fin m, ({v i} : Multiset (Fin n)))+{u 0} := by ac_rfl
    _ = ({u 0}+(∑ i : Fin m, ({u i.succ} : Multiset (Fin n))))+
        (∑ i : Fin m, ({v i} : Multiset (Fin n)))+{u 0} := by rw [hu]
    _ = _ := by ac_rfl

end MinModulus.Research
