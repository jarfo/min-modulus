import research.AffineDomainTriangleCounts
import research.ExceptionalTriangleCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Every three-element represented support is contained in a full
positive or negative affine domain, or has the parametrized L-shape
witness required by the exceptional-triangle counting theorem. -/
theorem represented_triangle_support_trichotomy
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (T : Finset (Fin n)) (hTc : T.card=3)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a≠b → ∃ p q, 2 • (g a-g b)=g p-g q) :
    (∃ t, T ⊆ positiveAffineDomain g t) ∨
    (∃ t, T ⊆ negativeAffineDomain g t) ∨
    (∃ a p q : Fin 3 → Fin n, ∃ u v w z : Fin n,
      Function.Injective a ∧ T=Finset.univ.image a ∧ u≠v ∧ w≠z ∧
      (∀ i, 2 • (g (a i)-g (a (i+1)))=g (p i)-g (q i)) ∧
      Finset.univ.image (fun i ↦ (p i,q i))={(u,v),(u,z),(w,v)} ∧
      2 • (g u-g v)=g z-g w) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hTc
  obtain ⟨p₀,q₀,h₀⟩ := hT a (by simp) b (by simp) hab
  obtain ⟨p₁,q₁,h₁⟩ := hT b (by simp) c (by simp) hbc
  obtain ⟨p₂,q₂,h₂⟩ := hT c (by simp) a (by simp) hac.symm
  rcases represented_triangle_affine_or_l_shape hinj g hg
    a b c p₀ p₁ p₂ q₀ q₁ q₂ hab hac hbc h₀ h₁ h₂ with hp | hn | he
  · obtain ⟨x,y,z,t,hx,hy,hz⟩ := hp
    left
    refine ⟨t,?_⟩
    intro i hi
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi : i=a ∨ i=b ∨ i=c) with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hy⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hz⟩
  · obtain ⟨x,y,z,t,hx,hy,hz⟩ := hn
    right; left
    refine ⟨t,?_⟩
    intro i hi
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi : i=a ∨ i=b ∨ i=c) with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hy⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hz⟩
  · obtain ⟨u,v,w,z,huv,_,_,_,_,hwz,hF,hr⟩ := he
    right; right
    refine ⟨![a,b,c],![p₀,p₁,p₂],![q₀,q₁,q₂],u,v,w,z,?_,?_,huv,hwz,?_,?_,hr⟩
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact False.elim (hab hij)
        | exact False.elim (hab hij.symm)
        | exact False.elim (hac hij)
        | exact False.elim (hac hij.symm)
        | exact False.elim (hbc hij)
        | exact False.elim (hbc hij.symm)
    · rw [show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
      simp
    · intro i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
    · rw [show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
      simpa using hF

/-- A family of represented triangles contained in no full affine
domain has at most binomial(n,2) members. -/
theorem represented_triangle_family_outside_affine_card_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (Ts : Finset (Finset (Fin n)))
    (hTs : ∀ T ∈ Ts, T.card=3 ∧
      ∀ a ∈ T, ∀ b ∈ T, a≠b → ∃ p q, 2 • (g a-g b)=g p-g q)
    (hout : ∀ T ∈ Ts, (∀ t, ¬ T ⊆ positiveAffineDomain g t) ∧
      (∀ t, ¬ T ⊆ negativeAffineDomain g t)) : Ts.card ≤ n.choose 2 := by
  apply exceptional_triangle_family_card_le_choose_two hinj g hg Ts
  intro T hT
  rcases represented_triangle_support_trichotomy hinj g hg T (hTs T hT).1 (hTs T hT).2 with
    ⟨t,ht⟩ | ⟨t,ht⟩ | he
  · exact False.elim ((hout T hT).1 t ht)
  · exact False.elim ((hout T hT).2 t ht)
  · exact he

/-- A finite family of represented triangles is controlled by the
largest positive affine domain, the cyclic negative-domain bound and
at most binomial(n,2) exceptional supports. -/
theorem represented_triangle_family_card_upper_bound
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (Ts : Finset (Finset (Fin n)))
    (hTs : ∀ T ∈ Ts, T.card=3 ∧
      ∀ a ∈ T, ∀ b ∈ T, a≠b → ∃ p q, 2 • (g a-g b)=g p-g q)
    (M : ℕ) (hM : ∀ t, (positiveAffineDomain g t).card ≤ M) :
    6*Ts.card ≤ (2*(M-2)+(n-2)+6)*n.choose 2 := by
  classical
  let P : Finset (Finset (Fin n)) :=
    (Finset.univ.image (positiveAffineDomain g)).biUnion (fun S ↦ S.powersetCard 3)
  let Q : Finset (Finset (Fin n)) :=
    (Finset.univ.image (negativeAffineDomain g)).biUnion (fun S ↦ S.powersetCard 3)
  let E := Ts \ (P∪Q)
  have hP (T : Finset (Fin n)) (hc : T.card=3) (t : ZMod N)
      (ht : T ⊆ positiveAffineDomain g t) : T ∈ P := by
    exact Finset.mem_biUnion.mpr ⟨positiveAffineDomain g t,
      Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩,Finset.mem_powersetCard.mpr ⟨ht,hc⟩⟩
  have hQ (T : Finset (Fin n)) (hc : T.card=3) (t : ZMod N)
      (ht : T ⊆ negativeAffineDomain g t) : T ∈ Q := by
    exact Finset.mem_biUnion.mpr ⟨negativeAffineDomain g t,
      Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩,Finset.mem_powersetCard.mpr ⟨ht,hc⟩⟩
  have hE : E.card ≤ n.choose 2 := by
    apply represented_triangle_family_outside_affine_card_le hinj g hg E
    · intro T hT
      exact hTs T (Finset.mem_sdiff.mp hT).1
    · intro T hT
      obtain ⟨hTT,hTn⟩ := Finset.mem_sdiff.mp hT
      constructor
      · intro t ht
        exact hTn (Finset.mem_union_left _ (hP T (hTs T hTT).1 t ht))
      · intro t ht
        exact hTn (Finset.mem_union_right _ (hQ T (hTs T hTT).1 t ht))
  have hPc : P.card ≤ ∑ S ∈ Finset.univ.image (positiveAffineDomain g), S.card.choose 3 := by
    simpa only [P,Finset.card_powersetCard] using
      (Finset.card_biUnion_le :
        ((Finset.univ.image (positiveAffineDomain g)).biUnion (fun S ↦ S.powersetCard 3)).card ≤
          ∑ S ∈ Finset.univ.image (positiveAffineDomain g), (S.powersetCard 3).card)
  have hQc : Q.card ≤ ∑ S ∈ Finset.univ.image (negativeAffineDomain g), S.card.choose 3 := by
    simpa only [Q,Finset.card_powersetCard] using
      (Finset.card_biUnion_le :
        ((Finset.univ.image (negativeAffineDomain g)).biUnion (fun S ↦ S.powersetCard 3)).card ≤
          ∑ S ∈ Finset.univ.image (negativeAffineDomain g), (S.powersetCard 3).card)
  have hPbound : 3*P.card ≤ (M-2)*n.choose 2 :=
    (Nat.mul_le_mul_left 3 hPc).trans
      (positive_affine_domain_family_triangle_count_le hinj g hg Finset.univ M (fun t _ ↦ hM t))
  have hQbound : 6*Q.card ≤ (n-2)*n.choose 2 :=
    (Nat.mul_le_mul_left 6 hQc).trans
      (negative_affine_domain_family_triangle_count_le hinj g hg Finset.univ)
  have hcover : Ts ⊆ (P∪Q)∪E := by
    intro T hT
    by_cases hPQ : T ∈ P∪Q
    · exact Finset.mem_union_left _ hPQ
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hT,hPQ⟩)
  have hc : Ts.card ≤ P.card+Q.card+E.card := by
    have h₀ := Finset.card_le_card hcover
    have h₁ := Finset.card_union_le (P∪Q) E
    have h₂ := Finset.card_union_le P Q
    omega
  calc
    _ ≤ 6*(P.card+Q.card+E.card) := Nat.mul_le_mul_left 6 hc
    _ = 2*(3*P.card)+6*Q.card+6*E.card := by omega
    _ ≤ 2*((M-2)*n.choose 2)+(n-2)*n.choose 2+6*n.choose 2 := by omega
    _ = _ := by ring

end MinModulus.Research
