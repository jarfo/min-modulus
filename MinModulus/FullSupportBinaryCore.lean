import MinModulus.BinaryCoreDivisibility

namespace MinModulus
open Finset
open scoped Classical

/-- Both sides of a full-support binary core sum to a half of the total
shifted tuple sum. No division by two or validity is required. -/
theorem two_nsmul_full_binary_core_sum_eq_total
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ tupleBinaryCollisionCores g b)
    (hfull : uv.1 ∪ uv.2=Finset.univ) :
    2 • (∑ i ∈ uv.1, (g i+b))=∑ i, (g i+b) := by
  have hu := (Finset.mem_filter.mp huv).2
  have hs : (∑ i ∈ uv.1 ∪ uv.2, (g i+b))=
      (∑ i ∈ uv.1, (g i+b))+(∑ i ∈ uv.2, (g i+b)) := Finset.sum_union hu.1
  rw [hfull,← hu.2.1] at hs
  simpa only [two_nsmul] using hs.symm

/-- Under a two-point fibre cap, the value of its positive side uniquely
determines a full-support oriented binary core. -/
theorem full_support_binary_core_eq_of_equal_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (uv st : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hst : st ∈ tupleBinaryCollisionCores g b)
    (huFull : uv.1 ∪ uv.2=Finset.univ) (hsFull : st.1 ∪ st.2=Finset.univ)
    (he : (∑ i ∈ uv.1, (g i+b))=∑ i ∈ st.1, (g i+b)) : uv=st := by
  classical
  have hu := (Finset.mem_filter.mp huv).2
  have hs := (Finset.mem_filter.mp hst).2
  have hcomp (A B : Finset (Fin n)) (hd : Disjoint A B) (hf : A ∪ B=Finset.univ) :
      B=Finset.univ \ A := by
    ext i
    have hcover : i ∈ A ∨ i ∈ B := Finset.mem_union.mp (by rw [hf]; exact Finset.mem_univ _)
    have hdis : i ∈ A → i ∈ B → False := fun ha hb ↦ Finset.disjoint_left.mp hd ha hb
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have huc := hcomp uv.1 uv.2 hu.1 huFull
  have hsc := hcomp st.1 st.2 hs.1 hsFull
  have hne : uv.1 ≠ uv.2 := by
    intro hh
    have hc := hu.2.2
    rw [hh] at hc
    omega
  have hsEither : st.1=uv.1 ∨ st.1=uv.2 := by
    by_cases h1 : st.1=uv.1
    · exact Or.inl h1
    by_cases h2 : st.1=uv.2
    · exact Or.inr h2
    have hthree : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦
        (∑ i ∈ U, (g i+b))=∑ i ∈ uv.1, (g i+b))).card := by
      apply Finset.two_lt_card_iff.mpr
      refine ⟨uv.1,uv.2,st.1,?_,?_,?_,hne,fun hh ↦ h1 hh.symm,fun hh ↦ h2 hh.symm⟩ <;>
        apply Finset.mem_filter.mpr <;> refine ⟨Finset.mem_univ _,?_⟩
      · rfl
      · exact hu.2.1.symm
      · exact he.symm
    have ht := hcap (∑ i ∈ uv.1, (g i+b))
    omega
  rcases hsEither with h | h
  · have ht : st.2=uv.2 := by rw [hsc,h,← huc]
    exact Prod.ext h.symm ht.symm
  · have ht : st.2=uv.1 := by rw [hsc,h,huc]; simp
    have hc := hu.2.2
    have hc' := hs.2.2
    rw [h,ht] at hc'
    omega

/-- If doubling is injective and fibres have at most two points, there
is at most one full-support oriented binary core. -/
theorem full_support_binary_core_eq_of_doubling_injective
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hdouble : Function.Injective (fun z : G ↦ 2 • z))
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (uv st : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hst : st ∈ tupleBinaryCollisionCores g b)
    (huFull : uv.1 ∪ uv.2=Finset.univ) (hsFull : st.1 ∪ st.2=Finset.univ) : uv=st := by
  apply full_support_binary_core_eq_of_equal_sum g b hcap uv st huv hst huFull hsFull
  exact hdouble ((two_nsmul_full_binary_core_sum_eq_total g b uv huv huFull).trans
    (two_nsmul_full_binary_core_sum_eq_total g b st hst hsFull).symm)

/-- Under injective doubling and a two-point fibre cap, at most one
actual binary core can use every coordinate. -/
theorem full_support_binary_core_card_le_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hdouble : Function.Injective (fun z : G ↦ 2 • z))
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro uv huv st hst
  exact full_support_binary_core_eq_of_doubling_injective g b hdouble hcap uv st
    (Finset.mem_filter.mp huv).1 (Finset.mem_filter.mp hst).1
    (Finset.mem_filter.mp huv).2 (Finset.mem_filter.mp hst).2

/-- Odd intrinsic loss gives a unique full-support core when doubling
is injective and the valid tuple has no triple fibres. -/
theorem exists_unique_full_support_binary_core_of_odd_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hdouble : Function.Injective (fun z : G ↦ 2 • z))
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  obtain ⟨uv,huv,hfull⟩ := exists_full_support_binary_core_of_odd_intrinsic_loss g hg b hcap hodd
  refine ⟨uv,⟨huv,hfull⟩,?_⟩
  intro st hst
  exact full_support_binary_core_eq_of_doubling_injective g b hdouble hcap st uv
    hst.1 huv hst.2 hfull

/-- At odd nonzero cyclic modulus, doubling is injective, so odd loss
and a two-point fibre cap give a unique full-support relation core. -/
theorem exists_unique_full_support_binary_core_of_odd_modulus_loss
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  apply exists_unique_full_support_binary_core_of_odd_loss g hg b ?_ ?_ hodd
  · intro u v he
    exact add_self_injective_zmod hN u v (by simpa only [two_nsmul] using he)
  · intro z
    convert hcap z using 1
    congr

/-- Small odd intrinsic loss extracts a unique full-support signed
relation in the original odd-modulus tuple. -/
theorem exists_unique_full_support_binary_core_of_odd_modulus_small_loss
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  apply exists_unique_full_support_binary_core_of_odd_modulus_loss hN g hg b ?_ hodd
  intro z
  convert tuple_subset_fibre_card_le_two_of_small_intrinsic_loss g b hsmall z using 1
  congr

end MinModulus
