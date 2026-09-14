import research.SquarefreeDoubleCoinDecomposition
import MinModulus.UniqueSums
import MinModulus.G1OddPrimarySingletonComplement

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Independent pairs of doubling relations produce exponentially many distinct
squarefree remainders at a single value in degree three times the number of pairs. -/
theorem independent_doubling_rectangles_force_many_layers
    {m n N : ℕ} [NeZero N] (g : Fin n → ZMod N)
    (E : Fin m × Fin 4 → Fin n) (hE : Function.Injective E)
    (hleft : ∀ j, 2 • g (E (j,0))=g (E (j,1)))
    (hright : ∀ j, 2 • g (E (j,2))=g (E (j,3))) :
    ∃ x : ZMod N,
      2^m ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦
        S.card=m ∧ ∃ y ∈ actualFibreCoinCover g m, (∑ i ∈ S, g i)+2 • y=x)).card := by
  classical
  let a (U : Finset (Fin m)) (j : Fin m) : Fin n := E (j,if j ∈ U then 1 else 3)
  let b (U : Finset (Fin m)) (j : Fin m) : Fin n := E (j,if j ∈ U then 2 else 0)
  let S (U : Finset (Fin m)) : Finset (Fin n) := Finset.univ.image (a U)
  let T (U : Finset (Fin m)) : Finset (Fin n) := Finset.univ.image (b U)
  have ha (U) : Function.Injective (a U) := by
    intro i j h
    exact congrArg Prod.fst (hE h)
  have hb (U) : Function.Injective (b U) := by
    intro i j h
    exact congrArg Prod.fst (hE h)
  have hSc (U) : (S U).card=m := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ (ha U)]
    simp
  have hTc (U) : (T U).card=m := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ (hb U)]
    simp
  have hrecover (U : Finset (Fin m)) (j : Fin m) : E (j,1) ∈ S U ↔ j ∈ U := by
    constructor
    · intro hj
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
      have hp := hE hi
      have hij : i=j := congrArg Prod.fst hp
      subst i
      have hsecond := congrArg Prod.snd hp
      by_contra h
      simp only [if_neg h] at hsecond
      exact (by decide : (3 : Fin 4) ≠ 1) hsecond
    · intro hj
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by simp only [a,if_pos hj]⟩
  have hSi : Function.Injective S := by
    intro U V h
    ext j
    rw [← hrecover U j,← hrecover V j,h]
  let x : ZMod N := ∑ j : Fin m, (g (E (j,1))+g (E (j,3)))
  have hvalue (U) : (∑ i ∈ S U, g i)+2 • (∑ i ∈ T U, g i)=x := by
    dsimp only [S,T]
    rw [Finset.sum_image (fun i _ j _ h ↦ ha U h),
      Finset.sum_image (fun i _ j _ h ↦ hb U h),Finset.smul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ U
    · simp only [a,b,if_pos hj,hright j]
    · simp only [a,b,if_neg hj,hleft j,add_comm]
  let F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦
    S.card=m ∧ ∃ y ∈ actualFibreCoinCover g m, (∑ i ∈ S, g i)+2 • y=x)
  have hmap : ∀ U ∈ (Finset.univ : Finset (Finset (Fin m))), S U ∈ F := by
    intro U _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hSc U,∑ i ∈ T U, g i,?_,hvalue U⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(T U).val,hTc U,by simp⟩
  have hc := Finset.card_le_card_of_injOn S hmap hSi.injOn
  refine ⟨x,?_⟩
  simpa only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using hc

/-- At every central degree 3m of the valid binary Mersenne tuple of length 6m,
one repeated value lies in at least 2^m distinct fixed-remainder layers.
Thus validity and odd modulus do not impose a constant layer-multiplicity cap. -/
theorem mersenne_central_degree_exponential_layer_overlap
    (m : ℕ) (hm : 1 ≤ m) [NeZero (2^(6*m)-1)] :
    let g : Fin (6*m) → ZMod (2^(6*m)-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^(6*m)-1))
    ValidTuple g ∧ ∃ x ∈ repeatedCoinCover g (3*m),
      2^m ≤ ((Finset.univ : Finset (Finset (Fin (6*m)))).filter (fun S ↦
        S.card=m ∧ ∃ y ∈ actualFibreCoinCover g m, (∑ i ∈ S, g i)+2 • y=x)).card := by
  classical
  dsimp only
  let g : Fin (6*m) → ZMod (2^(6*m)-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^(6*m)-1))
  have hg : ValidTuple g := by
    have hbase : ValidTuple (fun i : Fin (6*m) ↦ (a i.val : ZMod (2^(6*m)-1))) :=
      validTuple_fixed_of_valid (by
        simpa using valid_gap (n:=6*m) (t:=0) (by omega) (by simpa using (by omega : 1 ≤ 6*m)))
    have ht := validTuple_sub_const _ hbase (-1)
    have hp (i : Fin (6*m)) :
        (a i.val : ZMod (2^(6*m)-1))-(-1)=g i := by
      rw [a,Nat.cast_sub Nat.one_le_two_pow,Nat.cast_one]
      dsimp only [g]
      abel
    simpa only [hp] using ht
  let E : Fin m × Fin 4 → Fin (6*m) := fun js ↦ ⟨4*js.1.val+js.2.val,by omega⟩
  have hE : Function.Injective E := by
    rintro ⟨i,s⟩ ⟨j,t⟩ h
    have hv : 4*i.val+s.val=4*j.val+t.val := congrArg Fin.val h
    have hij : i=j := Fin.ext (by omega)
    have hst : s=t := Fin.ext (by omega)
    exact Prod.ext hij hst
  have hl (j : Fin m) : 2 • g (E (j,0))=g (E (j,1)) := by
    change 2 • ((2^(4*j.val) : ℕ) : ZMod (2^(6*m)-1))=
      ((2^(4*j.val+1) : ℕ) : ZMod (2^(6*m)-1))
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_two,two_nsmul]
  have hr (j : Fin m) : 2 • g (E (j,2))=g (E (j,3)) := by
    change 2 • ((2^(4*j.val+2) : ℕ) : ZMod (2^(6*m)-1))=
      ((2^(4*j.val+3) : ℕ) : ZMod (2^(6*m)-1))
    have he : 4*j.val+3=(4*j.val+2)+1 := by omega
    rw [he]
    rw [pow_succ (2 : ℕ) (4*j.val+2),Nat.cast_mul,Nat.cast_ofNat,mul_two,two_nsmul]
  obtain ⟨x,hx⟩ := independent_doubling_rectangles_force_many_layers g E hE hl hr
  let F := (Finset.univ : Finset (Finset (Fin (6*m)))).filter (fun S ↦
    S.card=m ∧ ∃ y ∈ actualFibreCoinCover g m, (∑ i ∈ S, g i)+2 • y=x)
  have hF : F.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by positivity : 0 < 2^m) hx)
  obtain ⟨S,hS⟩ := hF
  obtain ⟨hc,y,hy,he⟩ := (Finset.mem_filter.mp hS).2
  have hD : x ∈ repeatedCoinCover g (3*m) :=
    (mem_repeatedCoinCover_iff_squarefree_double g x).mpr ⟨S,m,y,hm,by omega,hy,he⟩
  exact ⟨hg,x,hD,hx⟩

end MinModulus.Research
