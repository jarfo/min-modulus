import MinModulus.AffineChainForest

namespace MinModulus
open Finset

/-- A unit difference normalizes two coordinates of any valid tuple over a ring. -/
theorem exists_normalized_valid_of_unit_difference
    {R : Type*} [Ring R] [Nontrivial R] {n : ℕ}
    (g : Fin (n+2) → R) (hg : ValidTuple g)
    (a b : Fin (n+2)) (hu : IsUnit (g b-g a)) :
    ∃ w : Fin (n+2) → R, ValidTuple w ∧ w 0=0 ∧ w 1=1 := by
  classical
  obtain ⟨u,hu⟩ := hu
  have hab : a ≠ b := by
    intro h
    have hz : (u : R)=0 := by simpa only [h,sub_self] using hu
    exact Units.ne_zero u hz
  let s : Equiv.Perm (Fin (n+2)) := Equiv.swap 0 a
  let t : Fin (n+2) := s b
  have ht : t ≠ 0 := by
    intro h
    have hh : s b=s a := by simpa [t,s] using h
    exact hab (s.injective hh).symm
  let e : Equiv.Perm (Fin (n+2)) := (Equiv.swap 1 t).trans s
  have he0 : e 0=a := by
    dsimp [e]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp : (0 : Fin (n+2)) ≠ 1) ht.symm]
    simp [s]
  have he1 : e 1=b := by simp [e,t,s]
  let φ : R →+ R := {
    toFun := fun x ↦ (↑u⁻¹ : R)*x
    map_zero' := mul_zero _
    map_add' := mul_add _ }
  have hφ : Function.Injective φ := by
    intro x y h
    exact (Units.isUnit u⁻¹).mul_left_cancel h
  let w : Fin (n+2) → R := fun i ↦ φ (g (e i)-g a)
  refine ⟨w,validTuple_comp (validTuple_sub_const _
    (validTuple_embedding e.toEmbedding g hg) (g a)) φ hφ,?_,?_⟩
  · simp [w,he0]
  · simp [w,he1,φ,← hu]

/-- Subbinary validity cannot lie in a proper residue-class coset. -/
theorem exists_nonzero_cast_difference_of_valid_subbinary
    {n N p : ℕ} [NeZero N] [NeZero p] (hd : p ∣ N)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (hN : N < 2^(n+1)) (h1 : (1 : ZMod p) ≠ 0) :
    ∃ i, ZMod.castHom hd (ZMod p) (g i-g 0) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  let φ : ZMod N →+ ZMod p := (ZMod.castHom hd (ZMod p)).toAddMonoidHom
  have ht : φ.ker = ⊤ :=
    subgroup_eq_top_of_valid_subbinary_translate g hg (by simpa [ZMod.card] using hN)
      (-g 0) φ.ker (by
        intro i
        change ZMod.castHom hd (ZMod p) (g i + -g 0) = 0
        simpa only [sub_eq_add_neg] using hn i)
  have hz : φ 1=0 := AddMonoidHom.mem_ker.mp (ht ▸ AddSubgroup.mem_top 1)
  apply h1
  change (ZMod.castHom hd (ZMod p)) 1 = 0 at hz
  simpa only [map_one] using hz

/-- Any actual natural multiplicity rival contradicts validity after reduction. -/
theorem not_validTuple_natCast_of_checked_rival
    {n N : ℕ} (a k : Fin n → ℕ)
    (hsum : (∑ i, k i)=n) (hne : ∃ i, k i ≠ 1)
    (hval : (∑ i, k i*a i)%N=(∑ i, a i)%N) :
    ¬ ValidTuple (fun i ↦ (a i : ZMod N)) := by
  intro hg
  have hh : ((∑ i, k i*a i : ℕ) : ZMod N)=((∑ i, a i : ℕ) : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hval
  have hvalue : (∑ i, k i • (a i : ZMod N))=∑ i, (a i : ZMod N) := by
    simpa only [Nat.cast_sum,Nat.cast_mul,nsmul_eq_mul] using hh
  obtain ⟨i,hi⟩ := hne
  exact hi (hg k hsum hvalue i)

end MinModulus
