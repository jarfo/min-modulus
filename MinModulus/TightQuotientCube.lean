import MinModulus.CycleInvolutionLift
import MinModulus.G1SaturatedOverlap

/-!
# Extract actual dyadic structure at tight cyclic quotient capacity

An injective binary subset cube filling an even cyclic group contains
an actual half coordinate. A faithful character factors the complete
subset sum; its vanishing forces that coordinate. No ValidTuple premise
is assumed about the quotient cube. Deleting the half coordinate and
reducing the ACTUAL remainder preserves injectivity and bijectivity.

Iteration classifies every tight cube in ZMod (2^k): an actual
permutation places its ith coordinate at residue 2^i modulo 2^(i+1).
Thus every two-adic level occurs exactly once, without an SI premise.
At exact outside capacity this applies to ANY actual full-cover fibre,
providing half-coset and full dyadic-structure consumers. Arbitrary
critical full coverage or tightness is not extracted; G1/G2/G3 stay open.
-/

namespace MinModulus
open Finset

/-- Factor the character sum over ALL subsets, without any tuple
validity or injectivity assumption. -/
theorem sum_addChar_all_subsets_eq_prod
    {k : ℕ} {G : Type*} [AddCommGroup G]
    {R : Type*} [CommSemiring R] (q : Fin k → G) (χ : AddChar G R) :
    (∑ S : Finset (Fin k), χ (∑ i ∈ S, q i))=∏ i, (1+χ (q i)) := by
  classical
  have hmap (S : Finset (Fin k)) : χ (∑ i ∈ S, q i)=∏ i ∈ S, χ (q i) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => rw [Finset.sum_insert hi,χ.map_add_eq_mul,Finset.prod_insert hi,ih]
  simp_rw [hmap]
  simpa using (Finset.prod_one_add (f := fun i : Fin k ↦ χ (q i)) Finset.univ).symm

/-- Exact subset-sum filling of an even cyclic group forces an
ACTUAL coordinate equal to its unique nonzero involution. No ValidTuple
hypothesis is assumed about the quotient cube. -/
theorem exists_half_coordinate_of_bijective_subset_sums
    {k M : ℕ} [NeZero M] (q : Fin k → ZMod (2*M))
    (hbij : Function.Bijective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)) :
    ∃ j, q j=(M : ZMod (2*M)) := by
  classical
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  let χ : AddChar (ZMod (2*M)) ℂ := ZMod.stdAddChar
  have hinj : Function.Injective χ := ZMod.injective_stdAddChar
  have hhalf : (M : ZMod (2*M)) ≠ 0 := half_ne_zero rfl hM
  have hχne : χ (M : ZMod (2*M)) ≠ 1 := by
    intro heq
    apply hhalf
    apply hinj
    simpa only [χ.map_zero_eq_one] using heq
  have hχhalf : χ (M : ZMod (2*M))=-1 := by
    have hp : χ (M : ZMod (2*M))*χ (M : ZMod (2*M))=1 := by
      rw [← χ.map_add_eq_mul,half_add_half rfl,χ.map_zero_eq_one]
    exact (mul_self_eq_one_iff.mp hp).resolve_left hχne
  have hχ : χ ≠ 0 := by
    intro hz
    apply hχne
    rw [hz]
    rfl
  have hsum : (∑ z : ZMod (2*M), χ z)=0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχ
  let E : Finset (Fin k) ≃ ZMod (2*M) := Equiv.ofBijective _ hbij
  have hall : (∑ S : Finset (Fin k), χ (∑ i ∈ S, q i))=0 := by
    rw [← hsum]
    exact Fintype.sum_equiv E _ _ (fun _ ↦ rfl)
  rw [sum_addChar_all_subsets_eq_prod] at hall
  obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp hall
  refine ⟨j,hinj ?_⟩
  rw [hχhalf]
  linear_combination hj

/-- An injective cube at exact cyclic capacity is bijective and
therefore exposes an actual half coordinate. -/
theorem exists_half_coordinate_of_tight_subset_cube
    {k M : ℕ} [NeZero M] (hcard : 2^k=2*M) (q : Fin k → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)) :
    ∃ j, q j=(M : ZMod (2*M)) := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  apply exists_half_coordinate_of_bijective_subset_sums q
  refine ⟨hi,?_⟩
  by_contra hnot
  have hlt := Fintype.card_lt_of_injective_not_surjective _ hi hnot
  simp only [Fintype.card_finset,Fintype.card_fin,ZMod.card,hcard] at hlt
  omega

/-- At exact even quotient capacity, ANY actual full-cover fibre
forces an outside coordinate in the quotient's half coset. No SI,
cycle, zero-entry, or one-escape premise is used. -/
theorem exists_outside_half_of_tight_actual_fibre_cover
    {m k D M : ℕ} [NeZero D] [NeZero M] (hm : 0 < m) (hcard : 2^k=2*D)
    (g : Fin (m+k) → ZMod ((2*D)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom (2*D) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ j, ZMod.castHom (dvd_mul_right (2*D) M) (ZMod (2*D)) (g (Fin.natAdd m j))=(D : ZMod (2*D)) := by
  letI : NeZero ((2*D)*M) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (NeZero.ne D)) (NeZero.ne M)⟩
  exact exists_half_coordinate_of_tight_subset_cube hcard _
    (quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover)

/-- Deleting an ACTUAL half coordinate and reducing the remaining
coordinates preserves subset-sum injectivity. This is a cube theorem,
not an assumption that the quotient tuple itself is valid. -/
theorem subset_sum_injective_after_deleting_half_coordinate
    {k M : ℕ} [NeZero M] (q : Fin (k+1) → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (j : Fin (k+1)) (hj : q j=(M : ZMod (2*M))) :
    Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S,
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (q (j.succAbove i))) := by
  classical
  intro S T heq
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hsum (A : Finset (Fin k)) : (∑ i ∈ A.image j.succAbove, q i)=∑ i ∈ A, q (j.succAbove i) := by
    rw [Finset.sum_image (fun _ _ _ _ h ↦ Fin.succAbove_right_injective h)]
  have hnot (A : Finset (Fin k)) : j ∉ A.image j.succAbove := by
    intro hm
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
    exact Fin.succAbove_ne j i he
  have hproj : π (∑ i ∈ S.image j.succAbove, q i)=π (∑ i ∈ T.image j.succAbove, q i) := by
    rw [hsum,hsum,map_sum,map_sum]
    exact heq
  rcases eq_or_eq_add_half_of_castHom_eq _ _ hproj with hz | hh
  · exact Finset.image_injective Fin.succAbove_right_injective (hi hz)
  · have hcollision : (∑ i ∈ S.image j.succAbove, q i)=∑ i ∈ insert j (T.image j.succAbove), q i := by
      rw [Finset.sum_insert (hnot T),hj]
      simpa only [add_comm] using hh
    have hsets := hi hcollision
    exact False.elim ((hnot S) (hsets.symm ▸ Finset.mem_insert_self j (T.image j.succAbove)))

/-- Exact subset-sum filling descends to the ACTUAL retained half
quotient after deleting a half coordinate. Both bijectivity and the
actual tuple are preserved, so this extraction can be iterated. -/
theorem bijective_subset_sums_after_deleting_half_coordinate
    {k M : ℕ} [NeZero M] (q : Fin (k+1) → ZMod (2*M))
    (hbij : Function.Bijective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (j : Fin (k+1)) (hj : q j=(M : ZMod (2*M))) :
    Function.Bijective (fun S : Finset (Fin k) ↦ ∑ i ∈ S,
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (q (j.succAbove i))) := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective _ hbij)
  simp only [Fintype.card_finset,Fintype.card_fin,ZMod.card,pow_succ'] at hcard
  have hsmall : 2^k=M := by omega
  have hi := subset_sum_injective_after_deleting_half_coordinate q hbij.1 j hj
  refine ⟨hi,?_⟩
  by_contra hnot
  have hlt := Fintype.card_lt_of_injective_not_surjective _ hi hnot
  simp only [Fintype.card_finset,Fintype.card_fin,ZMod.card,hsmall] at hlt
  omega

/-- Exact cyclic binary capacity forces one ACTUAL coordinate at
each two-adic level. The permutation and residues are extracted by
repeated half-coordinate deletion; no validity or SI premise is used. -/
theorem exists_perm_dyadic_residues_of_injective_subset_sums
    {k : ℕ} (q : Fin k → ZMod (2^k))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)) :
    ∃ E : Equiv.Perm (Fin k), ∀ i, (q (E i)).val % 2^(i.val+1)=2^i.val := by
  induction k with
  | zero => exact ⟨Equiv.refl _,fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
    revert q
    rw [show (2 : ℕ)^(k+1)=2*2^k by rw [pow_succ']]
    intro q hi
    letI : NeZero (2^k) := ⟨pow_ne_zero _ (by omega)⟩
    obtain ⟨j,hj⟩ := exists_half_coordinate_of_tight_subset_cube
      (show (2 : ℕ)^(k+1)=2*2^k by rw [pow_succ']) q hi
    let q' : Fin k → ZMod (2^k) := fun i ↦
      ZMod.castHom (dvd_mul_left (2^k) 2) (ZMod (2^k)) (q (j.succAbove i))
    have hi' := subset_sum_injective_after_deleting_half_coordinate q hi j hj
    obtain ⟨e,he⟩ := ih q' hi'
    let F : Fin (k+1) → Fin (k+1) := Fin.lastCases j (fun i ↦ j.succAbove (e i))
    have hF : Function.Injective F := by
      intro a b
      refine Fin.lastCases ?_ (fun a ↦ ?_) a
      · refine Fin.lastCases (by intro; rfl) (fun b ↦ ?_) b
        intro h
        exact False.elim (Fin.ne_succAbove j (e b) (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using h))
      · refine Fin.lastCases ?_ (fun b ↦ ?_) b
        · intro h
          exact False.elim (Fin.succAbove_ne j (e a) (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using h))
        · intro h
          apply congrArg Fin.castSucc
          apply e.injective
          apply Fin.succAbove_right_injective
          simpa only [F,Fin.lastCases_castSucc] using h
    let E : Equiv.Perm (Fin (k+1)) := Equiv.ofBijective F ⟨hF,Finite.injective_iff_surjective.mp hF⟩
    refine ⟨E,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · have hp : 2^k < 2*2^k := by
        have hpos : 0 < (2 : ℕ)^k := by positivity
        omega
      simp only [E,Equiv.ofBijective_apply,F,Fin.lastCases_last,Fin.val_last,hj,ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt hp]
      rw [pow_succ',Nat.mod_eq_of_lt hp]
    · have hval : (q' (e i)).val=(q (j.succAbove (e i))).val % 2^k := by
        dsimp [q']
        rw [← ZMod.natCast_val,ZMod.val_natCast]
      have hres := he i
      rw [hval,Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : i.val+1 ≤ k))] at hres
      simpa only [E,Equiv.ofBijective_apply,F,Fin.lastCases_castSucc,Fin.val_castSucc] using hres

/-- At exact power-of-two quotient capacity, any ACTUAL full-cover
fibre forces its outside quotient coordinates to occupy every dyadic
level exactly once, with an actual permutation supplied. -/
theorem exists_perm_dyadic_quotient_residues_of_tight_actual_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+k) → ZMod ((2^k)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom (2^k) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ E : Equiv.Perm (Fin k), ∀ i,
      (ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m (E i)))).val %
        2^(i.val+1)=2^i.val := by
  letI : NeZero ((2^k)*M) := ⟨Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (NeZero.ne M)⟩
  exact exists_perm_dyadic_residues_of_injective_subset_sums _
    (quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover)

end MinModulus
