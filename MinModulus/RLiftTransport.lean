import MinModulus.RLiftSmallK
import MinModulus.ReflectedValid

/-!
# Affine transport: the R-lift exclusion theorem

A valid `(m+3)`-tuple modulo `4M` whose deletion-child modulo `2M` is an
affine image of the reflected tuple is normalized — by reindexing,
translation, and unit scaling — to a sheeted lift of the exact parent
`rliftParentE`, which the complete extra dispatch excludes.
-/

set_option maxHeartbeats 1600000

namespace MinModulus

open Finset

/-! ## Validity transport -/

/-- Validity is invariant under reindexing. -/
lemma validTuple_reindex {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (E : Fin n ≃ Fin n) (hv : ValidTuple g) :
    ValidTuple (fun j => g (E j)) := by
  intro κ hsum hval
  have hs : ∑ i, κ (E.symm i) = n := by
    rw [Equiv.sum_comp E.symm κ]
    exact hsum
  have hw : ∑ i, κ (E.symm i) • g i = ∑ i, g i := by
    calc ∑ i, κ (E.symm i) • g i
        = ∑ j, κ (E.symm (E j)) • g (E j) := (Equiv.sum_comp E _).symm
      _ = ∑ j, κ j • g (E j) := by simp
      _ = ∑ j, g (E j) := hval
      _ = ∑ i, g i := Equiv.sum_comp E g
  have h1 := hv (fun i => κ (E.symm i)) hs hw
  intro i
  have h2 := h1 (E i)
  simpa using h2

/-- Validity is invariant under translation. -/
lemma validTuple_translate {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (c : G) (hv : ValidTuple g) :
    ValidTuple (fun i => g i + c) := by
  intro κ hsum hval
  apply hv κ hsum
  have h1 : ∑ i, κ i • (g i + c) = (∑ i, κ i • g i) + (∑ i, κ i) • c := by
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib, Finset.sum_smul]
  have h2 : ∑ i, (g i + c) = (∑ i, g i) + n • c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
  rw [h1, h2, hsum] at hval
  exact add_right_cancel hval

/-- Validity is invariant under multiplication by a unit. -/
lemma validTuple_unit_mul {n N : ℕ} (g : Fin n → ZMod N)
    (u : (ZMod N)ˣ) (hv : ValidTuple g) :
    ValidTuple (fun i => (u : ZMod N) * g i) := by
  have hinj : Function.Injective (fun x : ZMod N => (u : ZMod N) * x) := by
    intro x y hxy
    have h := congrArg (fun z => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * z) hxy
    simpa [← mul_assoc, Units.inv_mul] using h
  exact validTuple_comp hv (AddMonoidHom.mulLeft (u : ZMod N)) hinj

/-! ## The reduction homomorphism -/

lemma rlift_half_dvd (m : ℕ) : (2 ^ (m + 2) - 2) ∣ (2 ^ (m + 3) - 4) := by
  refine ⟨2, ?_⟩
  have hpow : (2 : ℕ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ (m + 2) := Nat.one_le_pow _ _ (by norm_num)
  omega

lemma rlift_modulus_pos (m : ℕ) : 0 < 2 ^ (m + 3) - 4 := by
  have hpow : (2 : ℕ) ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

lemma rlift_half_pos (m : ℕ) : 0 < 2 ^ (m + 2) - 2 := by
  have hpow : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- Reduction from the parent modulus `4M` to the child modulus `2M`. -/
def rliftReduce (m : ℕ) :
    ZMod (2 ^ (m + 3) - 4) →+* ZMod (2 ^ (m + 2) - 2) :=
  ZMod.castHom (rlift_half_dvd m) _

/-- The kernel of the reduction is `{0, sheet}`. -/
lemma rliftReduce_kernel (m : ℕ) (x : ZMod (2 ^ (m + 3) - 4))
    (hx : rliftReduce m x = 0) : x = 0 ∨ x = sheet m := by
  haveI : NeZero (2 ^ (m + 3) - 4) := ⟨by have := rlift_modulus_pos m; omega⟩
  haveI : NeZero (2 ^ (m + 2) - 2) := ⟨by have := rlift_half_pos m; omega⟩
  have hval : ((x.val : ℕ) : ZMod (2 ^ (m + 3) - 4)) = x :=
    ZMod.natCast_rightInverse x
  have hred : rliftReduce m ((x.val : ℕ) : ZMod (2 ^ (m + 3) - 4))
      = ((x.val : ℕ) : ZMod (2 ^ (m + 2) - 2)) := map_natCast _ _
  rw [hval, hx] at hred
  have hdvd : (2 ^ (m + 2) - 2) ∣ x.val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hred.symm
  obtain ⟨c, hc⟩ := hdvd
  have hlt : x.val < 2 ^ (m + 3) - 4 := ZMod.val_lt x
  have hmod : (2 : ℕ) ^ (m + 3) - 4 = 2 * (2 ^ (m + 2) - 2) := by
    have hpow : (2 : ℕ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
    have h1 : (1 : ℕ) ≤ 2 ^ (m + 2) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hc2 : c < 2 := by
    by_contra hcon
    have hcon' : 2 ≤ c := Nat.not_lt.mp hcon
    have h2 : (2 ^ (m + 2) - 2) * 2 ≤ (2 ^ (m + 2) - 2) * c :=
      Nat.mul_le_mul_left _ hcon'
    have h3 := rlift_half_pos m
    omega
  interval_cases c
  · left
    rw [← hval, hc]
    simp
  · right
    rw [← hval, hc]
    have hsheet : (2 ^ (m + 2) - 2) * 1 = 2 * (2 ^ (m + 1) - 1) := by
      have hpow : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [hsheet]
    rfl

/-- The reduction of the parent's child coordinates is the reflected
tuple. -/
lemma rliftReduce_parent_castSucc (m e : ℕ) (i : Fin (m + 2)) :
    rliftReduce m
        ((rliftParentE m e (Fin.castSucc i) : ℕ) : ZMod (2 ^ (m + 3) - 4))
      = reflectedTupleE m i := by
  rw [map_natCast]
  refine Fin.cases ?_ (fun i1 => ?_) i
  · rw [show Fin.castSucc (0 : Fin (m + 2)) = (0 : Fin (m + 3)) from by
      apply Fin.ext; simp]
    rw [show (rliftParentE m e 0 : ℕ) = 0 from by
      rw [rliftParentE, Fin.cons_zero]]
    rw [show reflectedTupleE m 0 = 0 from by
      rw [reflectedTupleE, Fin.cons_zero]]
    simp
  · refine Fin.cases ?_ (fun j => ?_) i1
    · rw [show Fin.castSucc (Fin.succ (0 : Fin (m + 1)))
          = Fin.succ (0 : Fin (m + 2)) from by apply Fin.ext; simp]
      rw [show (rliftParentE m e (Fin.succ (0 : Fin (m + 2))) : ℕ) = 1 from by
        rw [rliftParentE, Fin.cons_succ, Fin.cons_zero]]
      rw [show reflectedTupleE m (Fin.succ (0 : Fin (m + 1))) = 1 from by
        rw [reflectedTupleE, Fin.cons_succ, Fin.cons_zero]]
      simp
    · have hc : Fin.castSucc (Fin.succ (Fin.succ j))
          = Fin.succ (Fin.succ (Fin.castSucc j)) := by
        apply Fin.ext
        simp
      rw [hc]
      show ((rliftParentE m e
          (Fin.succ (Fin.succ (Fin.castSucc j))) : ℕ) :
            ZMod (2 ^ (m + 2) - 2))
        = reflectedTupleE m (Fin.succ (Fin.succ j))
      rw [rliftParentE, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
      show (((2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1) : ℕ)) :
          ZMod (2 ^ (m + 2) - 2))
        = reflectedTupleE m (Fin.succ (Fin.succ j))
      rw [reflectedTupleE, Fin.cons_succ, Fin.cons_succ]
      have h1 : (1 : ℕ) ≤ 2 ^ (j.val + 1) :=
        Nat.one_le_pow _ _ (by norm_num)
      have h2 : (2 : ℕ) ^ (j.val + 1) ≤ 2 ^ (m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.cast_sub (by omega)]

/-! ## The R-lift exclusion theorem -/

/-- **The R-lift exclusion.**  For even `m ≥ 2`, no valid `(m+3)`-tuple
modulo `4M = 2^(m+3) − 4` has a deletion-child modulo `2M = 2^(m+2) − 2`
which is an affine image of the reflected tuple: deleting the coordinate
`d` and reducing, the remaining coordinates are `a · R_σ(i) + b` for a
unit `a`, a shift `b`, and a reindexing `σ`. -/
theorem rlift_exclusion (m : ℕ) (hm2 : 2 ≤ m) (hme : Even m)
    (G : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4))
    (d : Fin (m + 3)) (σ : Fin (m + 2) ≃ Fin (m + 2))
    (a : (ZMod (2 ^ (m + 2) - 2))ˣ) (b : ZMod (2 ^ (m + 2) - 2))
    (hchild : ∀ i : Fin (m + 2),
        rliftReduce m (G (d.succAbove (σ i)))
          = (a : ZMod (2 ^ (m + 2) - 2)) * reflectedTupleE m i + b) :
    ¬ ValidTuple G := by
  intro hv
  haveI : NeZero (2 ^ (m + 3) - 4) := ⟨by have := rlift_modulus_pos m; omega⟩
  haveI : NeZero (2 ^ (m + 2) - 2) := ⟨by have := rlift_half_pos m; omega⟩
  -- the reindexing map: child coordinates first, the deleted one last
  set f : Fin (m + 3) → Fin (m + 3) :=
    Fin.lastCases d (fun i => d.succAbove (σ i)) with hf
  have hfcs : ∀ i : Fin (m + 2),
      f (Fin.castSucc i) = d.succAbove (σ i) := by
    intro i
    rw [hf]
    exact Fin.lastCases_castSucc ..
  have hflast : f (Fin.last (m + 2)) = d := by
    rw [hf]
    exact Fin.lastCases_last ..
  have hfinj : Function.Injective f := by
    intro x y hxy
    induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last => rfl
      | cast y1 =>
        rw [hflast, hfcs y1] at hxy
        exact absurd hxy.symm (Fin.succAbove_ne d (σ y1))
    | cast x1 =>
      induction y using Fin.lastCases with
      | last =>
        rw [hflast, hfcs x1] at hxy
        exact absurd hxy (Fin.succAbove_ne d (σ x1))
      | cast y1 =>
        rw [hfcs x1, hfcs y1] at hxy
        have h1 := Fin.succAbove_right_injective (p := d) hxy
        have h2 := σ.injective h1
        rw [h2]
  set E : Fin (m + 3) ≃ Fin (m + 3) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj) with hE
  have hv1 : ValidTuple (fun j => G (f j)) := validTuple_reindex G E hv
  -- the unit and translation lifts
  set α : ℕ := (a : ZMod (2 ^ (m + 2) - 2)).val with hα
  have hcop : Nat.Coprime α (2 ^ (m + 2) - 2) :=
    ZMod.val_coe_unit_coprime a
  have h2dvd : (2 : ℕ) ∣ (2 ^ (m + 2) - 2) := by
    have hpow : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    exact ⟨2 ^ (m + 1) - 1, by
      have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega⟩
  have hcop2 : Nat.Coprime α 2 := Nat.Coprime.coprime_dvd_right h2dvd hcop
  have hcop4 : Nat.Coprime α (2 ^ (m + 3) - 4) := by
    have hmod : (2 : ℕ) ^ (m + 3) - 4 = 2 * (2 ^ (m + 2) - 2) := by
      have hpow : (2 : ℕ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
      have h1 : (1 : ℕ) ≤ 2 ^ (m + 2) := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [hmod]
    exact Nat.Coprime.mul_right hcop2 hcop
  set Au : (ZMod (2 ^ (m + 3) - 4))ˣ := ZMod.unitOfCoprime α hcop4 with hAu
  set B : ZMod (2 ^ (m + 3) - 4) := ((b.val : ℕ) : ZMod (2 ^ (m + 3) - 4))
    with hB
  set G₂ : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4) :=
    fun j => ((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) : ZMod (2 ^ (m + 3) - 4))
      * (G (f j) + -B) with hG₂
  have hv2 : ValidTuple G₂ :=
    validTuple_unit_mul _ Au⁻¹ (validTuple_translate _ (-B) hv1)
  -- reduction facts
  have hredB : rliftReduce m B = b := by
    rw [hB, map_natCast]
    exact ZMod.natCast_rightInverse b
  have hredA : rliftReduce m ((Au : (ZMod (2 ^ (m + 3) - 4))ˣ) :
      ZMod (2 ^ (m + 3) - 4)) = (a : ZMod (2 ^ (m + 2) - 2)) := by
    rw [hAu, ZMod.coe_unitOfCoprime, map_natCast, hα]
    exact ZMod.natCast_rightInverse _
  have hredAinv : rliftReduce m
      (((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ)) : ZMod (2 ^ (m + 3) - 4))
      = ((a⁻¹ : (ZMod (2 ^ (m + 2) - 2))ˣ) : ZMod (2 ^ (m + 2) - 2)) := by
    have h1 : rliftReduce m ((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) :
          ZMod (2 ^ (m + 3) - 4))
        * rliftReduce m ((Au : (ZMod (2 ^ (m + 3) - 4))ˣ) :
          ZMod (2 ^ (m + 3) - 4)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hredA] at h1
    calc rliftReduce m ((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) :
          ZMod (2 ^ (m + 3) - 4))
        = rliftReduce m ((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) :
            ZMod (2 ^ (m + 3) - 4))
          * ((a : ZMod (2 ^ (m + 2) - 2))
            * ((a⁻¹ : (ZMod (2 ^ (m + 2) - 2))ˣ) :
              ZMod (2 ^ (m + 2) - 2))) := by
          rw [Units.mul_inv, mul_one]
      _ = (rliftReduce m ((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) :
            ZMod (2 ^ (m + 3) - 4)) * (a : ZMod (2 ^ (m + 2) - 2)))
          * ((a⁻¹ : (ZMod (2 ^ (m + 2) - 2))ˣ) :
            ZMod (2 ^ (m + 2) - 2)) := by ring
      _ = ((a⁻¹ : (ZMod (2 ^ (m + 2) - 2))ˣ) :
            ZMod (2 ^ (m + 2) - 2)) := by rw [h1, one_mul]
  -- the normalized child is the exact reflected tuple
  have hchild2 : ∀ i : Fin (m + 2),
      rliftReduce m (G₂ (Fin.castSucc i)) = reflectedTupleE m i := by
    intro i
    rw [hG₂]
    show rliftReduce m
        (((Au⁻¹ : (ZMod (2 ^ (m + 3) - 4))ˣ) : ZMod (2 ^ (m + 3) - 4))
          * (G (f (Fin.castSucc i)) + -B)) = reflectedTupleE m i
    rw [hfcs i, map_mul, map_add, map_neg, hredAinv, hchild i, hredB,
      add_neg_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  -- the extra and the sheet bits
  set e : ℕ := (G₂ (Fin.last (m + 2))).val with he
  set β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4) :=
    fun j => G₂ j - ((rliftParentE m e j : ℕ) : ZMod (2 ^ (m + 3) - 4))
    with hβd
  have hβ : ∀ j, β j = 0 ∨ β j = sheet m := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      left
      rw [hβd]
      show G₂ (Fin.last (m + 2))
          - ((rliftParentE m e (Fin.last (m + 2)) : ℕ) :
            ZMod (2 ^ (m + 3) - 4)) = 0
      rw [show rliftParentE m e (Fin.last (m + 2)) = e from
        rliftParentE_last m e]
      rw [he, ZMod.natCast_rightInverse (G₂ (Fin.last (m + 2)))]
      exact sub_self _
    | cast i =>
      apply rliftReduce_kernel
      rw [hβd]
      show rliftReduce m (G₂ (Fin.castSucc i)
          - ((rliftParentE m e (Fin.castSucc i) : ℕ) :
            ZMod (2 ^ (m + 3) - 4))) = 0
      rw [map_sub, hchild2 i, rliftReduce_parent_castSucc m e i, sub_self]
  have hg : ∀ j, G₂ j
      = ((rliftParentE m e j : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β j := by
    intro j
    rw [hβd]
    ring
  exact rliftParentE_not_valid_even m e hm2 hme hβ hg hv2

end MinModulus
