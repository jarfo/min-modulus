import research.TriangleDifferencePatterns

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The unordered repeated endpoint pair determines the unoriented
six-edge image of an L-shape. -/
theorem l_shape_symmetric_edges_eq_of_repeated_pair_eq
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (u v w z u' v' w' z' : Fin n)
    (huv : u≠v) (hwz : w≠z)
    (he : ({u,v} : Finset (Fin n))={u',v'})
    (h : 2 • (g u-g v)=g z-g w)
    (h' : 2 • (g u'-g v')=g z'-g w') :
    ({(u,v),(u,z),(w,v),(v,u),(z,u),(v,w)} : Finset (Fin n × Fin n))=
      {(u',v'),(u',z'),(w',v'),(v',u'),(z',u'),(v',w')} := by
  classical
  have hu : u=u' ∨ u=v' := by
    have hh : u ∈ ({u',v'} : Finset (Fin n)) := by rw [← he]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hv : v=u' ∨ v=v' := by
    have hh : v ∈ ({u',v'} : Finset (Fin n)) := by rw [← he]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (huv (hu.trans hv.symm))
  · subst u'; subst v'
    obtain ⟨hz,hw⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg z w z' w' hwz.symm
      (h.symm.trans h')
    subst z'; subst w'; rfl
  · subst v'; subst u'
    have hh : g z-g w=g w'-g z' := by
      calc
        _ = 2 • (g u-g v) := h.symm
        _ = -(2 • (g v-g u)) := by simp only [two_nsmul]; abel
        _ = -(g z'-g w') := congrArg Neg.neg h'
        _ = _ := by abel
    obtain ⟨hz,hw⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg z w w' z' hwz.symm hh
    subst w'; subst z'
    ext e
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  · exact False.elim (huv (hu.trans hv.symm))

/-- A represented triangle's vertex support is recovered from its image
edges even when each image edge may be read in either direction. -/
theorem represented_triangle_support_subset_of_symmetric_image_subset
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (a b p q r s : Fin 3 → Fin n)
    (ha : Function.Injective a)
    (hd : ∀ i, 2 • (g (a i)-g (a (i+1)))=g (p i)-g (q i))
    (he : ∀ i, 2 • (g (b i)-g (b (i+1)))=g (r i)-g (s i))
    (hsub : (Finset.univ.image (fun i ↦ (p i,q i))) ⊆
      (Finset.univ.image (fun i ↦ (r i,s i))) ∪
      (Finset.univ.image (fun i ↦ (s i,r i)))) :
    Finset.univ.image a ⊆ Finset.univ.image b := by
  classical
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  have hai : a i≠a (i+1) := by
    intro hh
    have hh' := ha hh
    have hhval := congrArg Fin.val hh'
    fin_cases i <;> norm_num [Fin.val_add] at hhval
  have hm := hsub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    have hpq := Prod.mk.inj hj
    have hh : 2 • (g (a i)-g (a (i+1)))=2 • (g (b j)-g (b (j+1))) := by
      rw [hd,he,hpq.1,hpq.2]
    have hh' := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg
      (a i) (a (i+1)) (b j) (b (j+1)) hai
      (hinj _ _ (by simpa only [two_nsmul] using hh))
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hh'.1.symm⟩
  · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    have hpq := Prod.mk.inj hj
    have hh : 2 • (g (a i)-g (a (i+1)))=2 • (g (b (j+1))-g (b j)) := by
      calc
        _ = g (p i)-g (q i) := hd i
        _ = -(g (r j)-g (s j)) := by rw [hpq.1,hpq.2]; abel
        _ = -(2 • (g (b j)-g (b (j+1)))) := congrArg Neg.neg (he j).symm
        _ = _ := by simp only [two_nsmul]; abel
    have hh' := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg
      (a i) (a (i+1)) (b (j+1)) (b j) hai
      (hinj _ _ (by simpa only [two_nsmul] using hh))
    exact Finset.mem_image.mpr ⟨j+1,Finset.mem_univ _,hh'.1.symm⟩

/-- Two represented L-shaped triangles with the same unordered repeated
endpoint pair have the same anchor support. -/
theorem represented_l_shape_triangle_support_eq
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (a b p q r s : Fin 3 → Fin n)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (u v w z u' v' w' z' : Fin n)
    (huv : u≠v) (hwz : w≠z)
    (hp : ∀ i, 2 • (g (a i)-g (a (i+1)))=g (p i)-g (q i))
    (hr : ∀ i, 2 • (g (b i)-g (b (i+1)))=g (r i)-g (s i))
    (hF : Finset.univ.image (fun i ↦ (p i,q i))={(u,v),(u,z),(w,v)})
    (hF' : Finset.univ.image (fun i ↦ (r i,s i))={(u',v'),(u',z'),(w',v')})
    (he : ({u,v} : Finset (Fin n))={u',v'})
    (h : 2 • (g u-g v)=g z-g w)
    (h' : 2 • (g u'-g v')=g z'-g w') :
    Finset.univ.image a=Finset.univ.image b := by
  classical
  have symm_edges (p q : Fin 3 → Fin n) (u v w z : Fin n)
      (hF : Finset.univ.image (fun i ↦ (p i,q i))={(u,v),(u,z),(w,v)}) :
      Finset.univ.image (fun i ↦ (p i,q i)) ∪ Finset.univ.image (fun i ↦ (q i,p i))=
        {(u,v),(u,z),(w,v),(v,u),(z,u),(v,w)} := by
    have heq : Finset.univ.image (fun i ↦ (q i,p i))=
        (Finset.univ.image (fun i ↦ (p i,q i))).image Prod.swap := by
      rw [Finset.image_image]
      rfl
    rw [heq,hF]
    ext e
    simp only [Finset.mem_union,Finset.image_insert,Finset.image_singleton,
      Prod.swap_prod_mk,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have heq := (symm_edges p q u v w z hF).trans
    ((l_shape_symmetric_edges_eq_of_repeated_pair_eq hinj g hg
      u v w z u' v' w' z' huv hwz he h h').trans
        (symm_edges r s u' v' w' z' hF').symm)
  apply Finset.Subset.antisymm
  · apply represented_triangle_support_subset_of_symmetric_image_subset hinj g hg a b p q r s ha hp hr
    intro e he
    rw [← heq]
    exact Finset.mem_union_left _ he
  · apply represented_triangle_support_subset_of_symmetric_image_subset hinj g hg b a r s p q hb hr hp
    intro e he
    rw [heq]
    exact Finset.mem_union_left _ he

/-- Any family of represented triangles having an L-shaped image has
at most one member for each unordered pair of coordinates. -/
theorem exceptional_triangle_family_card_le_choose_two
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (Ts : Finset (Finset (Fin n)))
    (hTs : ∀ T ∈ Ts, ∃ a p q : Fin 3 → Fin n, ∃ u v w z : Fin n,
      Function.Injective a ∧ T=Finset.univ.image a ∧ u≠v ∧ w≠z ∧
      (∀ i, 2 • (g (a i)-g (a (i+1)))=g (p i)-g (q i)) ∧
      Finset.univ.image (fun i ↦ (p i,q i))={(u,v),(u,z),(w,v)} ∧
      2 • (g u-g v)=g z-g w) :
    Ts.card ≤ n.choose 2 := by
  classical
  choose a p q u v w z ha hT huv hwz hd hF hr using
    (fun T : Ts ↦ hTs T.val T.property)
  let f : Ts → Finset (Fin n) := fun T ↦ {u T,v T}
  have hmaps : ∀ T ∈ (Finset.univ : Finset Ts),
      f T ∈ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro T _
    simp [f,Finset.mem_powersetCard,huv T]
  have hfi : Set.InjOn f (Finset.univ : Finset Ts) := by
    intro A _ B _ he
    apply Subtype.ext
    rw [hT A,hT B]
    exact represented_l_shape_triangle_support_eq hinj g hg
      (a A) (a B) (p A) (q A) (p B) (q B) (ha A) (ha B)
      (u A) (v A) (w A) (z A) (u B) (v B) (w B) (z B)
      (huv A) (hwz A) (hd A) (hd B) (hF A) (hF B) he (hr A) (hr B)
  have hc := Finset.card_le_card_of_injOn f hmaps hfi
  simpa only [Finset.card_univ,Fintype.card_coe,Finset.card_powersetCard,Fintype.card_fin] using hc

end MinModulus.Research
