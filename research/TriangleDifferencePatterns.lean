import MinModulus.TriplingClosure
import research.SingleRepeatFibres

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A balanced three-edge pattern with a repeated source and a repeated
target has an L-shape with four distinct endpoints. -/
theorem repeated_balanced_three_edges_l_shape
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (p₀ p₁ p₂ q₀ q₁ q₂ : Fin n)
    (hc : ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n)).card=3)
    (hn : p₀≠q₀ ∧ p₁≠q₁ ∧ p₂≠q₂)
    (hs : g p₀+g p₁+g p₂=g q₀+g q₁+g q₂)
    (hp : p₀=p₁ ∨ p₀=p₂ ∨ p₁=p₂)
    (hq : q₀=q₁ ∨ q₀=q₂ ∨ q₁=q₂) :
    ∃ u v w z : Fin n,
      u≠v ∧ u≠w ∧ u≠z ∧ v≠w ∧ v≠z ∧ w≠z ∧
      ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n))=
        {(u,v),(u,z),(w,v)} ∧
      2 • (g u-g v)=g z-g w := by
  classical
  let F : Finset (Fin n × Fin n) := {(p₀,q₀),(p₁,q₁),(p₂,q₂)}
  have hnl : ∀ e ∈ F, e.1≠e.2 := by
    intro e he
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2
  have build (u v w z : Fin n)
      (hF : F={(u,v),(u,z),(w,v)})
      (he : g u+g u+g w=g v+g v+g z) :
      u≠v ∧ u≠w ∧ u≠z ∧ v≠w ∧ v≠z ∧ w≠z ∧
      F={(u,v),(u,z),(w,v)} ∧ 2 • (g u-g v)=g z-g w := by
    have huv : u≠v := hnl (u,v) (by rw [hF]; simp)
    have huz : u≠z := hnl (u,z) (by rw [hF]; simp)
    have hwv : w≠v := hnl (w,v) (by rw [hF]; simp)
    have huw : u≠w := by
      intro h
      have hcard : F.card ≤ 2 := by
        rw [hF,← h]
        simpa only [Finset.insert_eq_of_mem (by simp : (u,v)∈({(u,z),(u,v)} : Finset (Fin n × Fin n)))] using
          (Finset.card_le_two (a := (u,z)) (b := (u,v)))
      change F.card=3 at hc
      omega
    have hvz : v≠z := by
      intro h
      have hcard : F.card ≤ 2 := by
        rw [hF,← h,Finset.insert_idem]
        exact Finset.card_le_two
      change F.card=3 at hc
      omega
    have hwz : w≠z := by
      intro h
      rw [h] at he
      exact huv (validTuple_injective g hg (hinj _ _ (add_right_cancel he)))
    refine ⟨huv,huw,huz,hwv.symm,hvz,hwz,hF,?_⟩
    rw [nsmul_sub,sub_eq_sub_iff_add_eq_add]
    simpa only [two_nsmul,add_assoc,add_comm,add_left_comm] using he
  have hne₀₁ : (p₀,q₀)≠(p₁,q₁) := by
    intro h
    have hh : ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n)).card ≤ 2 := by
      rw [h,Finset.insert_idem]
      exact Finset.card_le_two
    omega
  have hne₀₂ : (p₀,q₀)≠(p₂,q₂) := by
    intro h
    have hh : ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n)).card ≤ 2 := by
      rw [h,Finset.insert_eq_of_mem (by simp)]
      exact Finset.card_le_two
    omega
  have hne₁₂ : (p₁,q₁)≠(p₂,q₂) := by
    intro h
    have hh : ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n)).card ≤ 2 := by
      rw [h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
      exact Finset.card_le_two
    omega
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · exact False.elim (hne₀₁ (Prod.ext hp hq))
  · refine ⟨p₀,q₀,p₂,q₁,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · refine ⟨p₁,q₁,p₂,q₀,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]; tauto
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · refine ⟨p₀,q₀,p₁,q₂,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]; tauto
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · exact False.elim (hne₀₂ (Prod.ext hp hq))
  · refine ⟨p₂,q₂,p₁,q₀,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]; tauto
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · refine ⟨p₁,q₁,p₀,q₂,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]; tauto
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · refine ⟨p₂,q₂,p₀,q₁,build _ _ _ _ ?_ ?_⟩
    · ext e; simp only [F,Finset.mem_insert,Finset.mem_singleton,hp,hq]; tauto
    · simpa only [hp,hq,add_assoc,add_comm,add_left_comm] using hs
  · exact False.elim (hne₁₂ (Prod.ext hp hq))

/-- The coordinate pairs representing the doubled edges of a genuine
triangle are distinct nonloops, and their source and target sums agree. -/
theorem represented_triangle_image_edges
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (a b c p₀ p₁ p₂ q₀ q₁ q₂ : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (h₀ : 2 • (g a-g b)=g p₀-g q₀)
    (h₁ : 2 • (g b-g c)=g p₁-g q₁)
    (h₂ : 2 • (g c-g a)=g p₂-g q₂) :
    ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n)).card=3 ∧
    (p₀≠q₀ ∧ p₁≠q₁ ∧ p₂≠q₂) ∧
    g p₀+g p₁+g p₂=g q₀+g q₁+g q₂ := by
  classical
  have hd (x y z w : Fin n) (hxy : x≠y)
      (he : 2 • (g x-g y)=2 • (g z-g w)) : x=z ∧ y=w := by
    exact pair_eq_of_sub_eq_sub_of_validTuple hinj g hg x y z w hxy
      (hinj _ _ (by simpa only [two_nsmul] using he))
  have hnl (x y p q : Fin n) (hxy : x≠y)
      (he : 2 • (g x-g y)=g p-g q) : p≠q := by
    intro hpq
    rw [hpq,sub_self,two_nsmul] at he
    have he' : (g x-g y)+(g x-g y)=(0:G)+0 := by simpa only [zero_add] using he
    exact hxy (validTuple_injective g hg (sub_eq_zero.mp (hinj _ _ he')))
  have hne₀₁ : (p₀,q₀)≠(p₁,q₁) := by
    intro he
    have hpq := Prod.mk.inj he
    exact hab (hd a b b c hab (h₀.trans (by simpa only [hpq.1,hpq.2] using h₁.symm))).1
  have hne₀₂ : (p₀,q₀)≠(p₂,q₂) := by
    intro he
    have hpq := Prod.mk.inj he
    exact hac (hd a b c a hab (h₀.trans (by simpa only [hpq.1,hpq.2] using h₂.symm))).1
  have hne₁₂ : (p₁,q₁)≠(p₂,q₂) := by
    intro he
    have hpq := Prod.mk.inj he
    exact hbc (hd b c c a hbc (h₁.trans (by simpa only [hpq.1,hpq.2] using h₂.symm))).1
  refine ⟨by simp [hne₀₁,hne₀₂,hne₁₂],
    ⟨hnl a b p₀ q₀ hab h₀,hnl b c p₁ q₁ hbc h₁,hnl c a p₂ q₂ hac.symm h₂⟩,?_⟩
  apply sub_eq_zero.mp
  calc
    _ = (g p₀-g q₀)+(g p₁-g q₁)+(g p₂-g q₂) := by abel
    _ = 2 • (g a-g b)+2 • (g b-g c)+2 • (g c-g a) := by rw [h₀,h₁,h₂]
    _ = 0 := by simp only [two_nsmul]; abel

/-- If the three source coordinates in a balanced simple triangle are
distinct, validity forces one of the two directed three-cycles. -/
theorem squarefree_balanced_three_edges_cycle
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (p₀ p₁ p₂ q₀ q₁ q₂ : Fin n)
    (hp : p₀≠p₁ ∧ p₀≠p₂ ∧ p₁≠p₂)
    (hn : p₀≠q₀ ∧ p₁≠q₁ ∧ p₂≠q₂)
    (hs : g p₀+g p₁+g p₂=g q₀+g q₁+g q₂) :
    (q₀=p₁ ∧ q₁=p₂ ∧ q₂=p₀) ∨ (q₀=p₂ ∧ q₁=p₀ ∧ q₂=p₁) := by
  classical
  have hm : ({q₀,q₁,q₂} : Multiset (Fin n))=({p₀,p₁,p₂} : Finset (Fin n)).val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg
    · simp [hp.1,hp.2.1,hp.2.2]
    · simpa [hp.1,hp.2.1,hp.2.2,add_assoc] using hs.symm
  have hnd : ({q₀,q₁,q₂} : Multiset (Fin n)).Nodup := hm.symm ▸ Finset.nodup _
  have hq : q₀≠q₁ ∧ q₀≠q₂ ∧ q₁≠q₂ := by simpa [Multiset.nodup_cons,and_assoc] using hnd
  have hmem (q : Fin n) (hq' : q=q₀ ∨ q=q₁ ∨ q=q₂) : q=p₀ ∨ q=p₁ ∨ q=p₂ := by
    have hh : q ∈ ({p₀,p₁,p₂} : Finset (Fin n)).val := by rw [← hm]; simpa using hq'
    simpa only [Finset.mem_val,Finset.mem_insert,Finset.mem_singleton] using hh
  have hq₀ := hmem q₀ (Or.inl rfl)
  have hq₁ := hmem q₁ (Or.inr (Or.inl rfl))
  have hq₂ := hmem q₂ (Or.inr (Or.inr rfl))
  rcases hq₀ with h₀ | h₀ | h₀ <;> rcases hq₁ with h₁ | h₁ | h₁ <;>
    rcases hq₂ with h₂ | h₂ | h₂ <;> simp_all

/-- Every represented triangle lies in a positive or negative affine
doubling domain, unless its image edges have the four-endpoint L-shape. -/
theorem represented_triangle_affine_or_l_shape
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (a b c p₀ p₁ p₂ q₀ q₁ q₂ : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (h₀ : 2 • (g a-g b)=g p₀-g q₀)
    (h₁ : 2 • (g b-g c)=g p₁-g q₁)
    (h₂ : 2 • (g c-g a)=g p₂-g q₂) :
    (∃ x y z : Fin n, ∃ t : G,
      g x+t=2 • g a ∧ g y+t=2 • g b ∧ g z+t=2 • g c) ∨
    (∃ x y z : Fin n, ∃ t : G,
      g x+2 • g a=t ∧ g y+2 • g b=t ∧ g z+2 • g c=t) ∨
    (∃ u v w z : Fin n,
      u≠v ∧ u≠w ∧ u≠z ∧ v≠w ∧ v≠z ∧ w≠z ∧
      ({(p₀,q₀),(p₁,q₁),(p₂,q₂)} : Finset (Fin n × Fin n))=
        {(u,v),(u,z),(w,v)} ∧ 2 • (g u-g v)=g z-g w) := by
  obtain ⟨hc,hn,hs⟩ := represented_triangle_image_edges hinj g hg
    a b c p₀ p₁ p₂ q₀ q₁ q₂ hab hac hbc h₀ h₁ h₂
  have cycle (hh : (q₀=p₁ ∧ q₁=p₂ ∧ q₂=p₀) ∨
      (q₀=p₂ ∧ q₁=p₀ ∧ q₂=p₁)) :
      (∃ x y z : Fin n, ∃ t : G,
        g x+t=2 • g a ∧ g y+t=2 • g b ∧ g z+t=2 • g c) ∨
      (∃ x y z : Fin n, ∃ t : G,
        g x+2 • g a=t ∧ g y+2 • g b=t ∧ g z+2 • g c=t) := by
    rcases hh with ⟨hh₀,hh₁,hh₂⟩ | ⟨hh₀,hh₁,hh₂⟩
    · left
      refine ⟨p₀,p₁,p₂,2 • g a-g p₀,?_,?_,?_⟩
      · abel
      · have he := h₀
        rw [nsmul_sub,hh₀] at he
        have he' : 2 • g a-g p₀=2 • g b-g p₁ := by
          apply sub_eq_sub_iff_add_eq_add.mpr
          simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp he
        rw [he']; abel
      · have he := h₂
        rw [nsmul_sub,hh₂] at he
        have he' : 2 • g a-g p₀=2 • g c-g p₂ := by
          apply sub_eq_sub_iff_add_eq_add.mpr
          simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp he).symm
        rw [he']; abel
    · right
      refine ⟨p₂,p₀,p₁,g p₂+2 • g a,rfl,?_,?_⟩
      · have he := h₀
        rw [nsmul_sub,hh₀] at he
        simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp he).symm
      · have he := h₂
        rw [nsmul_sub,hh₂] at he
        simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp he
  by_cases hp : p₀=p₁ ∨ p₀=p₂ ∨ p₁=p₂
  · by_cases hq : q₀=q₁ ∨ q₀=q₂ ∨ q₁=q₂
    · exact Or.inr (Or.inr (repeated_balanced_three_edges_l_shape hinj g hg
        p₀ p₁ p₂ q₀ q₁ q₂ hc hn hs hp hq))
    · have hq' : q₀≠q₁ ∧ q₀≠q₂ ∧ q₁≠q₂ := by tauto
      have hh := squarefree_balanced_three_edges_cycle g hg q₀ q₁ q₂ p₀ p₁ p₂
        hq' ⟨hn.1.symm,hn.2.1.symm,hn.2.2.symm⟩ hs.symm
      have hh' : (q₀=p₁ ∧ q₁=p₂ ∧ q₂=p₀) ∨ (q₀=p₂ ∧ q₁=p₀ ∧ q₂=p₁) := by
        rcases hh with ⟨h₀,h₁,h₂⟩ | ⟨h₀,h₁,h₂⟩
        · exact Or.inr ⟨h₂.symm,h₀.symm,h₁.symm⟩
        · exact Or.inl ⟨h₁.symm,h₂.symm,h₀.symm⟩
      rcases cycle hh' with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
  · have hp' : p₀≠p₁ ∧ p₀≠p₂ ∧ p₁≠p₂ := by tauto
    rcases cycle (squarefree_balanced_three_edges_cycle g hg p₀ p₁ p₂ q₀ q₁ q₂ hp' hn hs) with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)

end MinModulus.Research
