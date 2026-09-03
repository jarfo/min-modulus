/-
# External/internal row partition

Turn the retained mixed normal form into explicit finite index sets.  The
external and internal rows partition all selected owners, whose cardinality
is at least `d-1`.  Every external row comes with a chosen nonzero coordinate
outside both the center range and the transversal; unless the internal set
is empty, all internal rows are exact signed pairs to one common undeleted
pivot.
-/
import Mathlib.Combinatorics.Pigeonhole
import MinModulus.G1PrivateHeavyJointFiberAlgebra
import MinModulus.G1OddPrimaryFullCycleRetainedMixed

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- Exact threshold form of the external-coordinate pigeonhole principle:
either the ambient set pays `K` slots per coordinate, or one coordinate is
used by more than `K` external rows. -/
theorem finiteMap_capacity_or_largeFiber
    {α β : Type*} [Fintype α] [DecidableEq β]
    (R : Finset β) (f : α → β)
    (hf : ∀ a : α, f a ∈ R) (K : ℕ) :
    Fintype.card α ≤ R.card * K ∨
      ∃ x ∈ R,
        K < (Finset.univ.filter (fun a : α ↦ f a = x)).card := by
  by_cases hcap : Fintype.card α ≤ R.card * K
  · exact Or.inl hcap
  · right
    have hlarge : R.card * K < (Finset.univ : Finset α).card := by
      simpa using Nat.lt_of_not_ge hcap
    exact Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.univ) (t := R) (f := f)
      (fun a _ha ↦ hf a) hlarge

/-- Two indices in one component of a doubling permutation differ by a
power-of-two iterate. -/
theorem sameCycle_doubling_eq_pow_two_nsmul
    {α : Type*} [Finite α] (R : Equiv.Perm α)
    (x : α → G) (hdouble : ∀ i, x (R i) = 2 • x i)
    {u v : α} (hsame : R.SameCycle u v) :
    ∃ k : ℕ, x v = (2 ^ k) • x u := by
  obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
  refine ⟨k, ?_⟩
  rw [← hk]
  exact apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
    R x hdouble k u

/-- Componentwise comparison of two rows satisfying one affine owner law.
Under a doubling recurrence, their target difference is the same slope
times a Mersenne multiple of the first owner displacement. -/
theorem sameCycle_affineTargets_sub_eq_mersenne_nsmul
    {α : Type*} [Finite α] (R : Equiv.Perm α)
    (x target : α → G) (hdouble : ∀ i, x (R i) = 2 • x i)
    {u v : α} (hsame : R.SameCycle u v)
    (epsilon : ℤ) (offset : G)
    (hu : target u = epsilon • x u + offset)
    (hv : target v = epsilon • x v + offset) :
    ∃ k : ℕ,
      target v - target u = epsilon • ((2 ^ k - 1) • x u) := by
  obtain ⟨k, hk⟩ :=
    sameCycle_doubling_eq_pow_two_nsmul R x hdouble hsame
  refine ⟨k, ?_⟩
  rw [hv, hu, hk]
  have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hsplit : (2 ^ k) • x u = (2 ^ k - 1) • x u + x u := by
    have hcoeff := congrArg (fun a : ℕ ↦ a • x u)
      (Nat.sub_add_cancel hone).symm
    simpa [add_nsmul, one_nsmul] using hcoeff
  rw [hsplit, smul_add]
  abel

/-- The finite set of possible nonzero coefficient values at one coordinate
of an `n`-coordinate witness. -/
noncomputable def witnessNonzeroCoefficientLevels (n : ℕ) : Finset ℤ :=
  insert (-1) (Finset.Icc 1 (n : ℤ))

/-- There are exactly `n + 1` possible nonzero coefficient levels. -/
theorem card_witnessNonzeroCoefficientLevels (n : ℕ) :
    (witnessNonzeroCoefficientLevels n).card = n + 1 := by
  rw [witnessNonzeroCoefficientLevels, Finset.card_insert_of_notMem]
  · simp
  · simp

/-- A nonzero coefficient of a witness is either `-1` or lies between `1`
and `n`. -/
theorem witness_nonzeroCoefficient_mem_levels
    (g : Fin n → G) {h : G} {c : Fin n → ℤ}
    (hc : Witness g h c) {i : Fin n} (hi : c i ≠ 0) :
    c i ∈ witnessNonzeroCoefficientLevels n := by
  by_cases hminus : c i = -1
  · simp [witnessNonzeroCoefficientLevels, hminus]
  · have hlower : 1 ≤ c i := by
      have := hc.2.1 i
      omega
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates
      g hc hminus
    have hcard := card_witnessOmissionCoordinates_le c
    have hcardInt :
        ((witnessOmissionCoordinates c).card : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hcard
    simp [witnessNonzeroCoefficientLevels, hlower, hupper.trans hcardInt]

/-- Matrix structure carried by rows with one fixed retained external
coordinate and one fixed nonzero coefficient there.  The owner columns are
distinct deleted coordinates, each row is nonzero on its own owner and zero
on every other owner, and the complete coefficient rows remain distinct. -/
def FixedExternalCoefficientPrivateFiber
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) {E : Finset ↥J} (F : Finset ↥E)
    (x : Fin n) (lambda : ℤ) : Prop :=
  x ∉ Finset.univ.image center ∧ x ∉ B ∧ lambda ≠ 0 ∧
    Function.Injective (fun f : ↥F ↦
      center (P.symm (((f : ↥E) : ↥J) : Fin d))) ∧
    Function.Injective (fun f : ↥F ↦ coeff ((f : ↥E) : ↥J)) ∧
    (∀ f : ↥F,
      center (P.symm (((f : ↥E) : ↥J) : Fin d)) ∈ B ∧
      coeff ((f : ↥E) : ↥J) x = lambda ∧
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) ≠ 0) ∧
    (∀ (f : ↥F) i, i ∈ B →
      i ≠ center (P.symm (((f : ↥E) : ↥J) : Fin d)) →
      coeff ((f : ↥E) : ↥J) i = 0) ∧
    ∀ f k : ↥F, f ≠ k →
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((k : ↥E) : ↥J) : Fin d))) = 0

/-- The nonzero elements of the cyclic subgroup generated by `y`. -/
noncomputable def nonzeroZMultiples [Fintype G] (y : G) :
    Finset (AddSubgroup.zmultiples y) :=
  by
    classical
    exact Finset.univ.erase 0

/-- The nonzero part of `zmultiples y` has one fewer element than the order
of `y`. -/
theorem card_nonzeroZMultiples [Fintype G] (y : G) :
    (nonzeroZMultiples y).card = addOrderOf y - 1 := by
  classical
  calc
    (nonzeroZMultiples y).card =
        Fintype.card (AddSubgroup.zmultiples y) - 1 := by
      simp [nonzeroZMultiples]
    _ = addOrderOf y - 1 := by rw [Fintype.card_zmultiples]

/-- A fixed private external fiber either fits injectively among the nonzero
targets in `zmultiples y`, or two rows have the same target.  In the collision
case validity forces directed coefficient gaps in both directions.  The gaps
are distinct, avoid the common external column, and each lies at the gaining
row's owner or outside the deletion set. -/
theorem fixedExternalCoefficientPrivateFiber_card_le_order_sub_one_or_pairGaps
    [Fintype G] (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) :
    F.card ≤ addOrderOf y - 1 ∨
      ∃ f k : ↥F, f ≠ k ∧
        scalar ((f : ↥E) : ↥J) • y =
          scalar ((k : ↥E) : ↥J) • y ∧
        ∃ i j : Fin n,
          coeff ((f : ↥E) : ↥J) i + 2 ≤
            coeff ((k : ↥E) : ↥J) i ∧
          coeff ((k : ↥E) : ↥J) j + 2 ≤
            coeff ((f : ↥E) : ↥J) j ∧
          (i = center (P.symm (((k : ↥E) : ↥J) : Fin d)) ∨ i ∉ B) ∧
          (j = center (P.symm (((f : ↥E) : ↥J) : Fin d)) ∨ j ∉ B) ∧
          i ≠ j ∧ i ≠ x ∧ j ≠ x := by
  classical
  rcases hfiber with
    ⟨_hxOutside, _hxNotB, _hlambda, _hownerInj, hcoeffInj,
      hrowData, hprivacy, _hoffdiag⟩
  let target : ↥F → AddSubgroup.zmultiples y := fun f ↦
    ⟨scalar ((f : ↥E) : ↥J) • y,
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _⟩
  let R : Finset (AddSubgroup.zmultiples y) := nonzeroZMultiples y
  have htargetMem : ∀ f : ↥F, target f ∈ R := by
    intro f
    have hne : target f ≠ (0 : AddSubgroup.zmultiples y) := by
      intro hzero
      apply (hrows ((f : ↥E) : ↥J)).1
      exact congrArg Subtype.val hzero
    simpa [R, nonzeroZMultiples] using hne
  rcases finiteMap_capacity_or_largeFiber R target htargetMem 1 with
      hcap | ⟨z, _hzR, hlarge⟩
  · left
    simpa [R, card_nonzeroZMultiples] using hcap
  · right
    obtain ⟨f, hf, k, hk, hfk⟩ := Finset.one_lt_card.mp hlarge
    have htargetEq : target f = target k := by
      exact ((Finset.mem_filter.mp hf).2).trans
        ((Finset.mem_filter.mp hk).2).symm
    have htargetEq' :
        scalar ((f : ↥E) : ↥J) • y =
          scalar ((k : ↥E) : ↥J) • y := by
      exact congrArg Subtype.val htargetEq
    have hwf := (hrows ((f : ↥E) : ↥J)).2
    have hwk := (hrows ((k : ↥E) : ↥J)).2
    rw [← htargetEq'] at hwk
    have hcoeffNe : coeff ((f : ↥E) : ↥J) ≠
        coeff ((k : ↥E) : ↥J) := hcoeffInj.ne hfk
    obtain ⟨i, hi⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hwf hwk hcoeffNe
    obtain ⟨j, hj⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hwk hwf hcoeffNe.symm
    have hiLocation :
        i = center (P.symm (((k : ↥E) : ↥J) : Fin d)) ∨ i ∉ B := by
      by_cases hiB : i ∈ B
      · left
        by_contra hiOwner
        have hkZero := hprivacy k i hiB hiOwner
        have hfloor := hwf.2.1 i
        omega
      · exact Or.inr hiB
    have hjLocation :
        j = center (P.symm (((f : ↥E) : ↥J) : Fin d)) ∨ j ∉ B := by
      by_cases hjB : j ∈ B
      · left
        by_contra hjOwner
        have hfZero := hprivacy f j hjB hjOwner
        have hfloor := hwk.2.1 j
        omega
      · exact Or.inr hjB
    have hij : i ≠ j := by
      intro hij
      subst j
      omega
    have hix : i ≠ x := by
      intro hix
      subst i
      have hfX := (hrowData f).2.1
      have hkX := (hrowData k).2.1
      omega
    have hjx : j ≠ x := by
      intro hjx
      subst j
      have hfX := (hrowData f).2.1
      have hkX := (hrowData k).2.1
      omega
    exact ⟨f, k, hfk, htargetEq', i, j, hi, hj,
      hiLocation, hjLocation, hij, hix, hjx⟩

/-- Two equal-target rows in a fixed private external fiber either expose a
coefficient at least two on one of their private owner diagonals, or force
two mutually directed gaps at distinct retained coordinates away from the
common external column. -/
theorem fixedExternalCoefficientPrivateFiber_equalTarget_pair_heavyDiagonal_or_externalGaps
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (f k : ↥F) (hfk : f ≠ k)
    (htarget : scalar ((f : ↥E) : ↥J) • y =
      scalar ((k : ↥E) : ↥J) • y) :
    2 ≤ coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) ∨
      2 ≤ coeff ((k : ↥E) : ↥J)
          (center (P.symm (((k : ↥E) : ↥J) : Fin d))) ∨
      ∃ i j : Fin n,
        i ∉ B ∧ j ∉ B ∧ i ≠ j ∧ i ≠ x ∧ j ≠ x ∧
        coeff ((f : ↥E) : ↥J) i + 2 ≤
          coeff ((k : ↥E) : ↥J) i ∧
        coeff ((k : ↥E) : ↥J) j + 2 ≤
          coeff ((f : ↥E) : ↥J) j := by
  rcases hfiber with
    ⟨_hxOutside, _hxNotB, _hlambda, _hownerInj, hcoeffInj,
      hrowData, hprivacy, hoffdiag⟩
  by_cases hfHeavy : 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d)))
  · exact Or.inl hfHeavy
  by_cases hkHeavy : 2 ≤ coeff ((k : ↥E) : ↥J)
      (center (P.symm (((k : ↥E) : ↥J) : Fin d)))
  · exact Or.inr (Or.inl hkHeavy)
  right
  right
  have hwf := (hrows ((f : ↥E) : ↥J)).2
  have hwk := (hrows ((k : ↥E) : ↥J)).2
  rw [← htarget] at hwk
  have hcoeffNe : coeff ((f : ↥E) : ↥J) ≠
      coeff ((k : ↥E) : ↥J) := hcoeffInj.ne hfk
  obtain ⟨i, hi⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg hwf hwk hcoeffNe
  obtain ⟨j, hj⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg hwk hwf hcoeffNe.symm
  have hiOutside : i ∉ B := by
    intro hiB
    by_cases hiOwner :
        i = center (P.symm (((k : ↥E) : ↥J) : Fin d))
    · rw [hiOwner, hoffdiag f k hfk] at hi
      omega
    · have hkZero := hprivacy k i hiB hiOwner
      have hfloor := hwf.2.1 i
      omega
  have hjOutside : j ∉ B := by
    intro hjB
    by_cases hjOwner :
        j = center (P.symm (((f : ↥E) : ↥J) : Fin d))
    · rw [hjOwner, hoffdiag k f hfk.symm] at hj
      omega
    · have hfZero := hprivacy f j hjB hjOwner
      have hfloor := hwk.2.1 j
      omega
  have hij : i ≠ j := by
    intro hij
    subst j
    omega
  have hix : i ≠ x := by
    intro hix
    subst i
    have hfX := (hrowData f).2.1
    have hkX := (hrowData k).2.1
    omega
  have hjx : j ≠ x := by
    intro hjx
    subst j
    have hfX := (hrowData f).2.1
    have hkX := (hrowData k).2.1
    omega
  exact ⟨i, j, hiOutside, hjOutside, hij, hix, hjx, hi, hj⟩

/-- Rows in `S` whose private owner diagonal is at least two. -/
def fixedExternalFiberHeavyDiagonalRows
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (S : Finset ↥F) : Finset ↥F :=
  S.filter (fun f ↦ 2 ≤ coeff ((f : ↥E) : ↥J)
    (center (P.symm (((f : ↥E) : ↥J) : Fin d))))

/-- Rows in `S` whose private owner diagonal is below two. -/
def fixedExternalFiberLightDiagonalRows
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (S : Finset ↥F) : Finset ↥F :=
  S.filter (fun f ↦ ¬ 2 ≤ coeff ((f : ↥E) : ↥J)
    (center (P.symm (((f : ↥E) : ↥J) : Fin d))))

/-- Exact row partition into owner-heavy and light diagonals. -/
theorem card_fixedExternalFiberHeavy_add_light
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (S : Finset ↥F) :
    (fixedExternalFiberHeavyDiagonalRows center P coeff S).card +
      (fixedExternalFiberLightDiagonalRows center P coeff S).card = S.card := by
  classical
  rw [fixedExternalFiberHeavyDiagonalRows,
    fixedExternalFiberLightDiagonalRows]
  exact Finset.card_filter_add_card_filter_not (s := S)
    (fun f : ↥F ↦ 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))))

/-- Removing a retained coordinate from the complement of `B` leaves
exactly `n - |B| - 1` coordinates. -/
theorem card_univ_sdiff_erase_of_not_mem
    (B : Finset (Fin n)) (x : Fin n) (hx : x ∉ B) :
    ((Finset.univ \ B).erase x).card = n - B.card - 1 := by
  rw [Finset.card_erase_of_mem]
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩

/-- Quadratic gap frontier for any same-target subfamily of a fixed private
external fiber.  Every ordered pair of light-diagonal rows receives a
directed gap outside `B` and away from the common external column.  Hence
either those `|L|(|L|-1)` pairs fit at `K` per retained gap coordinate, or
one coordinate supports more than `K` directed gaps. -/
theorem fixedExternalCoefficientPrivateFiber_repeatedTarget_lightGapFrontier
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (S : Finset ↥F)
    (htarget : ∀ f ∈ S, ∀ k ∈ S,
      scalar ((f : ↥E) : ↥J) • y =
        scalar ((k : ↥E) : ↥J) • y) :
    let L := fixedExternalFiberLightDiagonalRows center P coeff S
    ∃ gapCoord : ↥L.offDiag → Fin n,
      (∀ p : ↥L.offDiag,
        gapCoord p ∉ B ∧ gapCoord p ≠ x ∧
          coeff ((p.1.1 : ↥E) : ↥J) (gapCoord p) + 2 ≤
            coeff ((p.1.2 : ↥E) : ↥J) (gapCoord p)) ∧
      ∀ K : ℕ,
        L.card * (L.card - 1) ≤
            (n - B.card - 1) * K ∨
          ∃ i ∈ (Finset.univ \ B).erase x,
            K < (Finset.univ.filter
              (fun p : ↥L.offDiag ↦ gapCoord p = i)).card := by
  classical
  let L := fixedExternalFiberLightDiagonalRows center P coeff S
  have hgapExists : ∀ p : ↥L.offDiag,
      ∃ i : Fin n, i ∉ B ∧ i ≠ x ∧
        coeff ((p.1.1 : ↥E) : ↥J) i + 2 ≤
          coeff ((p.1.2 : ↥E) : ↥J) i := by
    intro p
    have hp := Finset.mem_offDiag.mp p.property
    have hpFirstData : p.1.1 ∈ S ∧
        coeff ((p.1.1 : ↥E) : ↥J)
          (center (P.symm (((p.1.1 : ↥E) : ↥J) : Fin d))) ≤ 1 := by
      simpa [L, fixedExternalFiberLightDiagonalRows] using hp.1
    have hpSecondData : p.1.2 ∈ S ∧
        coeff ((p.1.2 : ↥E) : ↥J)
          (center (P.symm (((p.1.2 : ↥E) : ↥J) : Fin d))) ≤ 1 := by
      simpa [L, fixedExternalFiberLightDiagonalRows] using hp.2.1
    have hpFirst : p.1.1 ∈ S := by
      exact hpFirstData.1
    have hpSecond : p.1.2 ∈ S := by
      exact hpSecondData.1
    have hfirstLight : ¬ 2 ≤ coeff ((p.1.1 : ↥E) : ↥J)
        (center (P.symm (((p.1.1 : ↥E) : ↥J) : Fin d))) := by
      omega
    have hsecondLight : ¬ 2 ≤ coeff ((p.1.2 : ↥E) : ↥J)
        (center (P.symm (((p.1.2 : ↥E) : ↥J) : Fin d))) := by
      omega
    rcases fixedExternalCoefficientPrivateFiber_equalTarget_pair_heavyDiagonal_or_externalGaps
        g hg y B center P scalar coeff F x lambda hfiber hrows
        p.1.1 p.1.2 hp.2.2 (htarget p.1.1 hpFirst p.1.2 hpSecond) with
      hfirst | hsecond | ⟨i, _j, hiB, _hjB, _hij, hix, _hjx, hi, _hj⟩
    · exact False.elim (hfirstLight hfirst)
    · exact False.elim (hsecondLight hsecond)
    · exact ⟨i, hiB, hix, hi⟩
  choose gapCoord hgap using hgapExists
  refine ⟨gapCoord, hgap, ?_⟩
  let R : Finset (Fin n) := (Finset.univ \ B).erase x
  have hgapMem : ∀ p : ↥L.offDiag, gapCoord p ∈ R := by
    intro p
    exact Finset.mem_erase.mpr
      ⟨(hgap p).2.1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (hgap p).1⟩⟩
  intro K
  have hRcard : R.card = n - B.card - 1 := by
    exact card_univ_sdiff_erase_of_not_mem B x hfiber.2.1
  have hpairCard : Fintype.card ↥L.offDiag =
      L.card * (L.card - 1) := by
    rw [Fintype.card_coe, Finset.offDiag_card,
      Nat.mul_sub_left_distrib, Nat.mul_one]
  have hfrontier := finiteMap_capacity_or_largeFiber
    R gapCoord hgapMem K
  rw [hpairCard] at hfrontier
  simpa [R, hRcard] using hfrontier

/-- Light rows whose coefficient at `w` is positive. -/
def fixedExternalFiberPositiveRowsAt
    {d : ℕ} {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (L : Finset ↥F) (w : Fin n) :
    Finset ↥F :=
  L.filter (fun f ↦ 1 ≤ coeff ((f : ↥E) : ↥J) w)

/-- Ordered light-row pairs carrying a directed coefficient gap at `w`. -/
def fixedExternalFiberDirectedGapPairsAt
    {d : ℕ} {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (L : Finset ↥F) (w : Fin n) :
    Finset (↥F × ↥F) :=
  L.offDiag.filter (fun p ↦
    coeff ((p.1 : ↥E) : ↥J) w + 2 ≤
      coeff ((p.2 : ↥E) : ↥J) w)

/-- Every directed gap at `w` points into a row positive at `w`; forgetting
the source embeds the relation into `L × positiveRowsAt(w)`. -/
theorem card_fixedExternalFiberDirectedGapPairsAt_le
    (g : Fin n → G) (y : G) {d : ℕ} {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (L : Finset ↥F) (w : Fin n)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j)) :
    (fixedExternalFiberDirectedGapPairsAt coeff L w).card ≤
      L.card * (fixedExternalFiberPositiveRowsAt coeff L w).card := by
  classical
  let Q := fixedExternalFiberDirectedGapPairsAt coeff L w
  let P := fixedExternalFiberPositiveRowsAt coeff L w
  have hsubset : Q ⊆ L.product P := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpOff := Finset.mem_offDiag.mp hpData.1
    apply Finset.mem_product.mpr
    refine ⟨hpOff.1, Finset.mem_filter.mpr ⟨hpOff.2.1, ?_⟩⟩
    have hfloor := (hrows ((p.1 : ↥E) : ↥J)).2.1 w
    omega
  have hcard := Finset.card_le_card hsubset
  simpa [Q, P, Finset.card_product] using hcard

/-- A selected fixed-coordinate fiber from the adaptive frontier is bounded
by light-row count times the number of gaining rows positive there. -/
theorem card_selectedFixedExternalGapFiber_le_light_mul_positiveRows
    (g : Fin n → G) (y : G) {d : ℕ} {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (L : Finset ↥F)
    (gapCoord : ↥L.offDiag → Fin n)
    (hgap : ∀ p : ↥L.offDiag,
      coeff ((p.1.1 : ↥E) : ↥J) (gapCoord p) + 2 ≤
        coeff ((p.1.2 : ↥E) : ↥J) (gapCoord p))
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j)) (w : Fin n) :
    (Finset.univ.filter
        (fun p : ↥L.offDiag ↦ gapCoord p = w)).card ≤
      L.card * (fixedExternalFiberPositiveRowsAt coeff L w).card := by
  classical
  let S : Finset ↥L.offDiag := Finset.univ.filter
    (fun p : ↥L.offDiag ↦ gapCoord p = w)
  let Q := fixedExternalFiberDirectedGapPairsAt coeff L w
  have hselected : S.card ≤ Q.card := by
    refine Finset.card_le_card_of_injOn (s := S) (t := Q)
      (fun p : ↥L.offDiag ↦ p.val) ?_ Subtype.val_injective.injOn
    intro p hp
    have hpEq := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨p.property, ?_⟩
    simpa [hpEq] using hgap p
  have hrelation := card_fixedExternalFiberDirectedGapPairsAt_le
    g y scalar coeff L w hrows
  exact hselected.trans hrelation

/-- If at most two coordinates survive deletion, every owner-heavy row in a
fixed private external coefficient fiber is forced to be a pure edge.  Its
two omissions are the common external coordinate and the other retained
coordinate; in particular the fixed external coefficient is `-1` and the
private owner coefficient is exactly `2`. -/
theorem fixedExternalCoefficientPrivateFiber_heavyDiagonal_twoRetained_shape
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F)
    (hheavy : 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))))
    (hretained : n - B.card ≤ 2) :
    lambda = -1 ∧
      ∃ z : Fin n,
        z ∉ B ∧ z ≠ x ∧
        (∀ i, coeff ((f : ↥E) : ↥J) i = -1 ↔ i = x ∨ i = z) ∧
        coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = 2 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z := by
  classical
  rcases hfiber with
    ⟨_hxOutside, hxNotB, hlambdaNonzero, _hownerInj, _hcoeffInj,
      hrowData, hprivacy, _hoffdiag⟩
  let c : Fin n → ℤ := coeff ((f : ↥E) : ↥J)
  let o : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let O : Finset (Fin n) := witnessOmissionCoordinates c
  have hc : Witness g (scalar ((f : ↥E) : ↥J) • y) c := by
    simpa [c] using hrows ((f : ↥E) : ↥J)
  have hoB : o ∈ B := by
    simpa [o] using (hrowData f).1
  have hcx : c x = lambda := by
    simpa [c] using (hrowData f).2.1
  have hheavy' : 2 ≤ c o := by
    simpa [c, o] using hheavy
  have hOexact : ExactOmissions c O := by
    simpa [O] using witnessOmissionCoordinates_exact c
  have hOsub : O ⊆ Finset.univ \ B := by
    intro i hiO
    have hiMinus : c i = -1 := (hOexact i).2 hiO
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiB
    by_cases hio : i = o
    · subst i
      omega
    · have hiZero : c i = 0 := by
        simpa [c, o] using hprivacy f i hiB hio
      omega
  have hcompCard : (Finset.univ \ B).card = n - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp
  have hOcardUpper : O.card ≤ 2 := by
    have hle := Finset.card_le_card hOsub
    rw [hcompCard] at hle
    omega
  have hoNotMinus : c o ≠ -1 := by omega
  have hdiagUpper := witness_coeff_le_card_witnessOmissionCoordinates
    g hc hoNotMinus
  have hOcardLower : 2 ≤ O.card := by
    have hle : (2 : ℤ) ≤ (O.card : ℤ) := hheavy'.trans hdiagUpper
    exact_mod_cast hle
  have hOcard : O.card = 2 := by omega
  have hdiag : c o = 2 := by
    rw [hOcard] at hdiagUpper
    omega
  obtain ⟨a, b, hab, hOeq⟩ := Finset.card_eq_two.mp hOcard
  have homit : ∀ i, c i = -1 ↔ i = a ∨ i = b := by
    intro i
    simpa [hOeq] using hOexact i
  have hlambda : lambda = -1 := by
    by_contra hlambdaMinus
    have hlambdaPositive : 1 ≤ lambda := by
      have hfloor := hc.2.1 x
      omega
    have hxNotMinus : c x ≠ -1 := by
      rw [hcx]
      exact hlambdaMinus
    have hoa : o ≠ a := by
      intro hoa
      exact hoNotMinus ((homit o).2 (Or.inl hoa))
    have hob : o ≠ b := by
      intro hob
      exact hoNotMinus ((homit o).2 (Or.inr hob))
    have hxa : x ≠ a := by
      intro hxa
      exact hxNotMinus ((homit x).2 (Or.inl hxa))
    have hxb : x ≠ b := by
      intro hxb
      exact hxNotMinus ((homit x).2 (Or.inr hxb))
    have hox : o ≠ x := by
      intro hox
      subst x
      exact hxNotB hoB
    have hsum := witness_two_coeff_sum_le_two_of_exact_pair
      g hc a b o x hab homit hoa hob hxa hxb hox
    rw [hdiag, hcx] at hsum
    omega
  have hxO : x ∈ O := (hOexact x).1 (by rw [hcx, hlambda])
  have hOone : 1 < O.card := by omega
  obtain ⟨u, huO, z, hzO, huz⟩ := Finset.one_lt_card.mp hOone
  obtain ⟨z, hzO, hzx⟩ : ∃ z ∈ O, z ≠ x := by
    by_cases hux : u = x
    · refine ⟨z, hzO, ?_⟩
      intro hzx
      exact huz (hux.trans hzx.symm)
    · exact ⟨u, huO, hux⟩
  have hzNotB : z ∉ B := (Finset.mem_sdiff.mp (hOsub hzO)).2
  have hOeqXZ : O = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem hOcard hxO hzO hzx.symm
  have homitXZ : ∀ i, c i = -1 ↔ i = x ∨ i = z := by
    intro i
    simpa [hOeqXZ] using hOexact i
  have hox : o ≠ x := by
    intro hox
    subst x
    exact hxNotB hoB
  have hoz : o ≠ z := by
    intro hoz
    subst z
    exact hzNotB hoB
  have hshape : c = pureEdgeCoeffs o x z :=
    exactPair_coeff_two_eq_pureEdgeCoeffs
      g hc x z o hzx.symm homitXZ hox hoz hdiag
  refine ⟨hlambda, z, hzNotB, hzx, ?_, ?_, ?_⟩
  · simpa [c] using homitXZ
  · simpa [c, o] using hdiag
  · simpa [c, o] using hshape

/-- In the two-retained-coordinate regime, two distinct owner-heavy rows at
the same target force the G1 common-touch conclusion.  Their rigid shapes
have the same two omissions, so equality of targets gives equality of the
doubled owner values; uniqueness of the nonzero involution then supplies a
half-pair deletion coordinate. -/
theorem fixedExternalCoefficientPrivateFiber_equalTarget_twoHeavy_twoRetained_commonTouched
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (y : G) (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f k : ↥F) (hfk : f ≠ k)
    (htarget : scalar ((f : ↥E) : ↥J) • y =
      scalar ((k : ↥E) : ↥J) • y)
    (hfHeavy : 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))))
    (hkHeavy : 2 ≤ coeff ((k : ↥E) : ↥J)
      (center (P.symm (((k : ↥E) : ↥J) : Fin d))))
    (hretained : n - B.card ≤ 2) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  classical
  rcases
      fixedExternalCoefficientPrivateFiber_heavyDiagonal_twoRetained_shape
        g y B center P scalar coeff F x lambda hfiber hrows f hfHeavy
          hretained with
    ⟨_hlambda, zf, hzfNotB, hzfNeX, hfOmit, hfTwo, _hfShape⟩
  rcases
      fixedExternalCoefficientPrivateFiber_heavyDiagonal_twoRetained_shape
        g y B center P scalar coeff F x lambda hfiber hrows k hkHeavy
          hretained with
    ⟨_hlambda', zk, hzkNotB, hzkNeX, hkOmit, hkTwo, _hkShape⟩
  rcases hfiber with
    ⟨_hxOutside, hxNotB, _hlambdaNonzero, hownerInj, _hcoeffInj,
      hrowData, _hprivacy, _hoffdiag⟩
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotB⟩
  have hzfC : zf ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzfNotB⟩
  have hzkC : zk ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzkNotB⟩
  have hCcardUpper : (Finset.univ \ B).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hpairSub : ({x, zf} : Finset (Fin n)) ⊆ Finset.univ \ B := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hxC
    · exact hzfC
  have hpairCard : ({x, zf} : Finset (Fin n)).card = 2 := by
    exact Finset.card_pair hzfNeX.symm
  have hCcard : (Finset.univ \ B).card = 2 := by
    have hlower := Finset.card_le_card hpairSub
    rw [hpairCard] at hlower
    omega
  have hCeq : Finset.univ \ B = {x, zf} :=
    finset_eq_pair_of_card_eq_two_of_mem
      hCcard hxC hzfC hzfNeX.symm
  have hzkPair : zk = x ∨ zk = zf := by
    have : zk ∈ ({x, zf} : Finset (Fin n)) := by
      rw [← hCeq]
      exact hzkC
    simpa using this
  have hzkEq : zk = zf := by
    rcases hzkPair with hzkx | hzkf
    · exact False.elim (hzkNeX hzkx)
    · exact hzkf
  subst zk
  let of : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let ok : Fin n := center (P.symm (((k : ↥E) : ↥J) : Fin d))
  have hofB : of ∈ B := by
    simpa [of] using (hrowData f).1
  have hokB : ok ∈ B := by
    simpa [ok] using (hrowData k).1
  have hofx : of ≠ x := by
    intro hofx
    subst x
    exact hxNotB hofB
  have hofz : of ≠ zf := by
    intro hofz
    subst zf
    exact hzfNotB hofB
  have hokx : ok ≠ x := by
    intro hokx
    subst x
    exact hxNotB hokB
  have hokz : ok ≠ zf := by
    intro hokz
    subst zf
    exact hzfNotB hokB
  have hofk : of ≠ ok := by
    simpa [of, ok] using hownerInj.ne hfk
  have hwf : Witness g (scalar ((f : ↥E) : ↥J) • y)
      (coeff ((f : ↥E) : ↥J)) := hrows ((f : ↥E) : ↥J)
  have hwk : Witness g (scalar ((f : ↥E) : ↥J) • y)
      (coeff ((k : ↥E) : ↥J)) := by
    rw [htarget]
    exact hrows ((k : ↥E) : ↥J)
  have hdoubles : (2 : ℤ) • g of = (2 : ℤ) • g ok :=
    two_smul_eq_of_same_exact_pair_coeff_two
      g hwf hwk x zf of ok hzfNeX.symm hofx hofz hokx hokz
        hfOmit hkOmit (by simpa [of] using hfTwo)
          (by simpa [ok] using hkTwo)
  exact common_touched_of_two_smul_eq
    g hg hh hne hunique hofk hdoubles

/-- Two distinct light-diagonal rows cannot have the same target when at most
two coordinates survive deletion.  Validity would require two distinct
external gap coordinates away from the common external column, producing
three distinct retained coordinates. -/
theorem fixedExternalCoefficientPrivateFiber_equalTarget_twoLight_twoRetained_false
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (f k : ↥F) (hfk : f ≠ k)
    (htarget : scalar ((f : ↥E) : ↥J) • y =
      scalar ((k : ↥E) : ↥J) • y)
    (hfLight : ¬ 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))))
    (hkLight : ¬ 2 ≤ coeff ((k : ↥E) : ↥J)
      (center (P.symm (((k : ↥E) : ↥J) : Fin d))))
    (hretained : n - B.card ≤ 2) : False := by
  classical
  rcases
      fixedExternalCoefficientPrivateFiber_equalTarget_pair_heavyDiagonal_or_externalGaps
        g hg y B center P scalar coeff F x lambda hfiber hrows
          f k hfk htarget with
    hfHeavy | hkHeavy | ⟨i, j, hiB, hjB, hij, hix, hjx, _hi, _hj⟩
  · exact hfLight hfHeavy
  · exact hkLight hkHeavy
  · have hxB : x ∉ B := hfiber.2.1
    have htripleSub : ({x, i, j} : Finset (Fin n)) ⊆
        Finset.univ \ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjB⟩
    have htripleCard : ({x, i, j} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · simpa using hij
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun hxi ↦ hix hxi.symm, fun hxj ↦ hjx hxj.symm⟩
    have hlower := Finset.card_le_card htripleSub
    rw [htripleCard] at hlower
    have hupper : (Finset.univ \ B).card ≤ 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
      simpa using hretained
    omega

/-- The only possible distinct equal-target pair left in the two-retained
regime has a rigid adjacent-pure-edge form: the heavy row is centered at its
private owner and omits the two retained coordinates, while the light row is
centered at the second retained coordinate and omits the common column and
its own private owner. -/
theorem fixedExternalCoefficientPrivateFiber_equalTarget_heavyLight_twoRetained_shapes
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (f k : ↥F) (hfk : f ≠ k)
    (htarget : scalar ((f : ↥E) : ↥J) • y =
      scalar ((k : ↥E) : ↥J) • y)
    (hfHeavy : 2 ≤ coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))))
    (hkLight : ¬ 2 ≤ coeff ((k : ↥E) : ↥J)
      (center (P.symm (((k : ↥E) : ↥J) : Fin d))))
    (hretained : n - B.card ≤ 2) :
    lambda = -1 ∧
      ∃ z : Fin n,
        z ∉ B ∧ z ≠ x ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z ∧
        coeff ((k : ↥E) : ↥J) =
          pureEdgeCoeffs z x
            (center (P.symm (((k : ↥E) : ↥J) : Fin d))) := by
  classical
  rcases
      fixedExternalCoefficientPrivateFiber_heavyDiagonal_twoRetained_shape
        g y B center P scalar coeff F x lambda hfiber
          (fun j ↦ (hrows j).2) f hfHeavy hretained with
    ⟨hlambda, z, hzNotB, hzNeX, hfOmit, _hfTwo, hfShape⟩
  rcases hfiber with
    ⟨_hxOutside, hxNotB, _hlambdaNonzero, _hownerInj, hcoeffInj,
      hrowData, hprivacy, hoffdiag⟩
  let of : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let ok : Fin n := center (P.symm (((k : ↥E) : ↥J) : Fin d))
  let cf : Fin n → ℤ := coeff ((f : ↥E) : ↥J)
  let ck : Fin n → ℤ := coeff ((k : ↥E) : ↥J)
  have hofB : of ∈ B := by
    simpa [of] using (hrowData f).1
  have hokB : ok ∈ B := by
    simpa [ok] using (hrowData k).1
  have hokNonzero : ck ok ≠ 0 := by
    simpa [ck, ok] using (hrowData k).2.2
  have hkx : ck x = -1 := by
    have := (hrowData k).2.1
    simpa [ck, hlambda] using this
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotB⟩
  have hzC : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzNotB⟩
  have hCcardUpper : (Finset.univ \ B).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hpairSub : ({x, z} : Finset (Fin n)) ⊆ Finset.univ \ B := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hxC
    · exact hzC
  have hpairCard : ({x, z} : Finset (Fin n)).card = 2 :=
    Finset.card_pair hzNeX.symm
  have hCcard : (Finset.univ \ B).card = 2 := by
    have hlower := Finset.card_le_card hpairSub
    rw [hpairCard] at hlower
    omega
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem
      hCcard hxC hzC hzNeX.symm
  have hwf : Witness g (scalar ((f : ↥E) : ↥J) • y) cf := by
    simpa [cf] using (hrows ((f : ↥E) : ↥J)).2
  have hwk : Witness g (scalar ((f : ↥E) : ↥J) • y) ck := by
    rw [htarget]
    simpa [ck] using (hrows ((k : ↥E) : ↥J)).2
  have hcoeffNe : cf ≠ ck := by
    simpa [cf, ck] using hcoeffInj.ne hfk
  obtain ⟨i, hiGap⟩ :=
    exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hwf hwk hcoeffNe
  have hiNotB : i ∉ B := by
    intro hiB
    by_cases hiok : i = ok
    · subst i
      have hfZero : cf ok = 0 := by
        simpa [cf, ok] using hoffdiag f k hfk
      have hkLight' : ck ok ≤ 1 := by
        simpa [ck, ok] using (show
          coeff ((k : ↥E) : ↥J)
              (center (P.symm (((k : ↥E) : ↥J) : Fin d))) ≤ 1 by
            omega)
      omega
    · have hkZero : ck i = 0 := by
        simpa [ck, ok] using hprivacy k i hiB hiok
      have hfloor := hwf.2.1 i
      omega
  have hix : i ≠ x := by
    intro hix
    subst i
    have hfx : cf x = -1 := by
      simpa [cf] using (hfOmit x).2 (Or.inl rfl)
    omega
  have hiC : i ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiNotB⟩
  have hiz : i = z := by
    have hiPair : i = x ∨ i = z := by
      have : i ∈ ({x, z} : Finset (Fin n)) := by
        rw [← hCeq]
        exact hiC
      simpa using this
    rcases hiPair with hix' | hiz'
    · exact False.elim (hix hix')
    · exact hiz'
  subst i
  have hfz : cf z = -1 := by
    simpa [cf] using (hfOmit z).2 (Or.inr rfl)
  have hkzPositive : 1 ≤ ck z := by omega
  have hokx : ok ≠ x := by
    intro hokx
    subst x
    exact hxNotB hokB
  have hokz : ok ≠ z := by
    intro hokz
    subst z
    exact hzNotB hokB
  have hzeroOutside : ∀ a : Fin n,
      a ≠ x → a ≠ z → a ≠ ok → ck a = 0 := by
    intro a hax haz haok
    have haB : a ∈ B := by
      by_contra haNotB
      have haC : a ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haNotB⟩
      have haPair : a = x ∨ a = z := by
        have : a ∈ ({x, z} : Finset (Fin n)) := by
          rw [← hCeq]
          exact haC
        simpa using this
      exact haPair.elim hax haz
    simpa [ck, ok] using hprivacy k a haB haok
  have hrestrict :
      ∑ a ∈ ({x, z, ok} : Finset (Fin n)), ck a = ∑ a, ck a := by
    exact Finset.sum_subset (by simp) (by
      intro a _ ha
      apply hzeroOutside a
      · intro hax
        exact ha (by simp [hax])
      · intro haz
        exact ha (by simp [haz])
      · intro haok
        exact ha (by simp [haok]))
  have hxNotPair : x ∉ ({z, ok} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hzNeX.symm, hokx.symm⟩
  have hzNotOwner : z ∉ ({ok} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hokz.symm
  have hsum : ck x + ck z + ck ok = 0 := by
    calc
      ck x + ck z + ck ok =
          ∑ a ∈ ({x, z, ok} : Finset (Fin n)), ck a := by
        rw [Finset.sum_insert hxNotPair, Finset.sum_insert hzNotOwner]
        simp [add_assoc]
      _ = ∑ a, ck a := hrestrict
      _ = 0 := hwk.2.2.1
  have hokFloor := hwk.2.1 ok
  have hokUpper : ck ok ≤ 1 := by
    simpa [ck, ok] using (show
      coeff ((k : ↥E) : ↥J)
          (center (P.symm (((k : ↥E) : ↥J) : Fin d))) ≤ 1 by
        omega)
  have hokMinus : ck ok = -1 := by omega
  have hkzTwo : ck z = 2 := by omega
  have hkOmit : ∀ a, ck a = -1 ↔ a = x ∨ a = ok := by
    intro a
    constructor
    · intro haMinus
      by_cases hax : a = x
      · exact Or.inl hax
      by_cases haz : a = z
      · subst a
        omega
      by_cases haok : a = ok
      · exact Or.inr haok
      · have haZero := hzeroOutside a hax haz haok
        omega
    · intro ha
      rcases ha with rfl | rfl
      · exact hkx
      · exact hokMinus
  have hkShape : ck = pureEdgeCoeffs z x ok :=
    exactPair_coeff_two_eq_pureEdgeCoeffs
      g hwk x ok z hokx.symm hkOmit hzNeX hokz.symm hkzTwo
  refine ⟨hlambda, z, hzNotB, hzNeX, ?_, ?_⟩
  · simpa [cf, of] using hfShape
  · simpa [ck, ok] using hkShape

/-- Under no common touch, every same-target subfamily of a fixed private
external fiber has at most two rows when at most two coordinates survive
deletion.  There is at most one owner-heavy row by the doubled-owner deletion
argument and at most one light row by the three-retained-coordinate gap
contradiction. -/
theorem fixedExternalCoefficientPrivateFiber_sameTarget_card_le_two_of_noCommonTouched
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : G) (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (S : Finset ↥F)
    (htarget : ∀ f ∈ S, ∀ k ∈ S,
      scalar ((f : ↥E) : ↥J) • y =
        scalar ((k : ↥E) : ↥J) • y)
    (hretained : n - B.card ≤ 2) : S.card ≤ 2 := by
  classical
  let H := fixedExternalFiberHeavyDiagonalRows center P coeff S
  let L := fixedExternalFiberLightDiagonalRows center P coeff S
  have hHcard : H.card ≤ 1 := by
    by_contra hH
    have hHtwo : 1 < H.card := by omega
    obtain ⟨f, hfH, k, hkH, hfk⟩ := Finset.one_lt_card.mp hHtwo
    have hfData : f ∈ S ∧
        2 ≤ coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) := by
      simpa [H, fixedExternalFiberHeavyDiagonalRows] using hfH
    have hkData : k ∈ S ∧
        2 ≤ coeff ((k : ↥E) : ↥J)
          (center (P.symm (((k : ↥E) : ↥J) : Fin d))) := by
      simpa [H, fixedExternalFiberHeavyDiagonalRows] using hkH
    apply hno
    exact
      fixedExternalCoefficientPrivateFiber_equalTarget_twoHeavy_twoRetained_commonTouched
        g hg hh hne hunique y B center P scalar coeff F x lambda hfiber
          (fun j ↦ (hrows j).2) f k hfk
          (htarget f hfData.1 k hkData.1) hfData.2 hkData.2 hretained
  have hLcard : L.card ≤ 1 := by
    by_contra hL
    have hLtwo : 1 < L.card := by omega
    obtain ⟨f, hfL, k, hkL, hfk⟩ := Finset.one_lt_card.mp hLtwo
    have hfData : f ∈ S ∧
        ¬ 2 ≤ coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) := by
      simpa [L, fixedExternalFiberLightDiagonalRows] using hfL
    have hkData : k ∈ S ∧
        ¬ 2 ≤ coeff ((k : ↥E) : ↥J)
          (center (P.symm (((k : ↥E) : ↥J) : Fin d))) := by
      simpa [L, fixedExternalFiberLightDiagonalRows] using hkL
    exact
      fixedExternalCoefficientPrivateFiber_equalTarget_twoLight_twoRetained_false
        g hg y B center P scalar coeff F x lambda hfiber hrows
          f k hfk (htarget f hfData.1 k hkData.1)
          hfData.2 hkData.2 hretained
  have hpartition : H.card + L.card = S.card := by
    simpa [H, L] using
      card_fixedExternalFiberHeavy_add_light center P coeff S
  omega

/-- Quantitative target-capacity consequence of the two-retained rigidity:
under no common touch, every nonzero target in `zmultiples y` supports at most
two rows, so the whole fixed external coefficient fiber has cardinality at
most twice the punctured cyclic-subgroup order. -/
theorem fixedExternalCoefficientPrivateFiber_card_le_two_mul_order_sub_one_of_twoRetained
    [Fintype G] (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : G) (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card ≤ 2) :
    F.card ≤ 2 * (addOrderOf y - 1) := by
  classical
  let target : ↥F → AddSubgroup.zmultiples y := fun f ↦
    ⟨scalar ((f : ↥E) : ↥J) • y,
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _⟩
  let R : Finset (AddSubgroup.zmultiples y) := nonzeroZMultiples y
  have htargetMem : ∀ f : ↥F, target f ∈ R := by
    intro f
    have hneTarget : target f ≠ (0 : AddSubgroup.zmultiples y) := by
      intro hzero
      apply (hrows ((f : ↥E) : ↥J)).1
      exact congrArg Subtype.val hzero
    simpa [R, nonzeroZMultiples] using hneTarget
  rcases finiteMap_capacity_or_largeFiber R target htargetMem 2 with
      hcap | ⟨z, _hzR, hlarge⟩
  · simpa [R, card_nonzeroZMultiples, Nat.mul_comm, Fintype.card_coe]
      using hcap
  · let S : Finset ↥F :=
      Finset.univ.filter (fun f : ↥F ↦ target f = z)
    have htarget : ∀ f ∈ S, ∀ k ∈ S,
        scalar ((f : ↥E) : ↥J) • y =
          scalar ((k : ↥E) : ↥J) • y := by
      intro f hf k hk
      have hfEq : target f = z := by
        exact (Finset.mem_filter.mp hf).2
      have hkEq : target k = z := by
        exact (Finset.mem_filter.mp hk).2
      exact congrArg Subtype.val (hfEq.trans hkEq.symm)
    have hSle :=
      fixedExternalCoefficientPrivateFiber_sameTarget_card_le_two_of_noCommonTouched
        g hg hh hne hunique hno y B center P scalar coeff F x lambda
          hfiber hrows S htarget hretained
    have hlarge' : 2 < S.card := by
      simpa [S, Fintype.card_coe] using hlarge
    omega

/-- Complete coefficient classification of an arbitrary private external row
when exactly two coordinates survive deletion.  Besides its private owner,
the row is supported only on the common external coordinate `x` and the
other retained coordinate `z`.  The common coefficient has only the three
possible values `-1`, `1`, and `2`, and the remaining two coefficients are
then one of the displayed finite profiles. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_rowProfile
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F) (hretained : n - B.card = 2) :
    ∃ z : Fin n,
      z ∉ B ∧ z ≠ x ∧
      (∀ i : Fin n,
        i ≠ center (P.symm (((f : ↥E) : ↥J) : Fin d)) →
        i ≠ x → i ≠ z → coeff ((f : ↥E) : ↥J) i = 0) ∧
      ((lambda = -1 ∧
          ((coeff ((f : ↥E) : ↥J)
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = -1 ∧
              coeff ((f : ↥E) : ↥J) z = 2) ∨
            (coeff ((f : ↥E) : ↥J)
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = 1 ∧
              coeff ((f : ↥E) : ↥J) z = 0) ∨
            (coeff ((f : ↥E) : ↥J)
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = 2 ∧
              coeff ((f : ↥E) : ↥J) z = -1))) ∨
        (lambda = 1 ∧
          coeff ((f : ↥E) : ↥J)
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = -1 ∧
          coeff ((f : ↥E) : ↥J) z = 0) ∨
        (lambda = 2 ∧
          coeff ((f : ↥E) : ↥J)
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = -1 ∧
          coeff ((f : ↥E) : ↥J) z = -1)) := by
  classical
  rcases hfiber with
    ⟨_hxOutside, hxNotB, hlambdaNonzero, _hownerInj, _hcoeffInj,
      hrowData, hprivacy, _hoffdiag⟩
  let o : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let c : Fin n → ℤ := coeff ((f : ↥E) : ↥J)
  have hc : Witness g (scalar ((f : ↥E) : ↥J) • y) c := by
    simpa [c] using hrows ((f : ↥E) : ↥J)
  have hoB : o ∈ B := by
    simpa [o] using (hrowData f).1
  have hcx : c x = lambda := by
    simpa [c] using (hrowData f).2.1
  have hoNonzero : c o ≠ 0 := by
    simpa [c, o] using (hrowData f).2.2
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotB⟩
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hCone : 1 < (Finset.univ \ B).card := by omega
  obtain ⟨u, huC, z, hzC, huz⟩ := Finset.one_lt_card.mp hCone
  obtain ⟨z, hzC, hzNeX⟩ :
      ∃ z ∈ Finset.univ \ B, z ≠ x := by
    by_cases hux : u = x
    · refine ⟨z, hzC, ?_⟩
      intro hzx
      exact huz (hux.trans hzx.symm)
    · exact ⟨u, huC, hux⟩
  have hzNotB : z ∉ B := (Finset.mem_sdiff.mp hzC).2
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem
      hCcard hxC hzC hzNeX.symm
  have hox : o ≠ x := by
    intro hox
    subst x
    exact hxNotB hoB
  have hoz : o ≠ z := by
    intro hoz
    subst z
    exact hzNotB hoB
  have hzeroOutside : ∀ i : Fin n,
      i ≠ o → i ≠ x → i ≠ z → c i = 0 := by
    intro i hio hix hiz
    have hiB : i ∈ B := by
      by_contra hiNotB
      have hiC : i ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiNotB⟩
      have hiPair : i = x ∨ i = z := by
        have : i ∈ ({x, z} : Finset (Fin n)) := by
          rw [← hCeq]
          exact hiC
        simpa using this
      exact hiPair.elim hix hiz
    simpa [c, o] using hprivacy f i hiB hio
  have hrestrict :
      ∑ i ∈ ({o, x, z} : Finset (Fin n)), c i = ∑ i, c i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      apply hzeroOutside i
      · intro hio
        exact hi (by simp [hio])
      · intro hix
        exact hi (by simp [hix])
      · intro hiz
        exact hi (by simp [hiz]))
  have hoNotPair : o ∉ ({x, z} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hox, hoz⟩
  have hxNotZ : x ∉ ({z} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hzNeX.symm
  have hsum : c o + c x + c z = 0 := by
    calc
      c o + c x + c z =
          ∑ i ∈ ({o, x, z} : Finset (Fin n)), c i := by
        rw [Finset.sum_insert hoNotPair, Finset.sum_insert hxNotZ]
        simp [add_assoc]
      _ = ∑ i, c i := hrestrict
      _ = 0 := hc.2.2.1
  have hbalance : c o + lambda + c z = 0 := by
    rw [← hcx]
    exact hsum
  have hlambdaFloor := hc.2.1 x
  have hoFloor := hc.2.1 o
  have hzFloor := hc.2.1 z
  have hprofiles :
      (lambda = -1 ∧
          ((c o = -1 ∧ c z = 2) ∨
            (c o = 1 ∧ c z = 0) ∨
            (c o = 2 ∧ c z = -1))) ∨
        (lambda = 1 ∧ c o = -1 ∧ c z = 0) ∨
        (lambda = 2 ∧ c o = -1 ∧ c z = -1) := by
    omega
  refine ⟨z, hzNotB, hzNeX, ?_, ?_⟩
  · intro i hio hix hiz
    simpa [c, o] using hzeroOutside i hio hix hiz
  · simpa [c, o] using hprofiles

/-- Geometric form of the complete two-retained profile classification.
Every external row is either an exact signed pair between its private owner
and the common retained coordinate, or one of three pure edges on the owner
and the retained pair. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_signedPair_or_pureEdge
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F) (hretained : n - B.card = 2) :
    ∃ z : Fin n,
      z ∉ B ∧ z ≠ x ∧
      ((lambda = -1 ∧
          (coeff ((f : ↥E) : ↥J) =
              pureEdgeCoeffs z
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x ∨
            ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
              (coeff ((f : ↥E) : ↥J))
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x ∨
            coeff ((f : ↥E) : ↥J) =
              pureEdgeCoeffs
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z)) ∨
        (lambda = 1 ∧
          ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
            (coeff ((f : ↥E) : ↥J))
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
        (lambda = 2 ∧
          coeff ((f : ↥E) : ↥J) =
            pureEdgeCoeffs x
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) z)) := by
  classical
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_rowProfile
      g y B center P scalar coeff F x lambda hfiber hrows f hretained with
    ⟨z, hzNotB, hzNeX, hzero, hprofiles⟩
  let o : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let c : Fin n → ℤ := coeff ((f : ↥E) : ↥J)
  have hc : Witness g (scalar ((f : ↥E) : ↥J) • y) c := by
    simpa [c] using hrows ((f : ↥E) : ↥J)
  have hoB : o ∈ B := by
    simpa [o] using hfiber.2.2.2.2.2.1 f |>.1
  have hxNotB : x ∉ B := hfiber.2.1
  have hox : o ≠ x := by
    intro hox
    subst x
    exact hxNotB hoB
  have hoz : o ≠ z := by
    intro hoz
    subst z
    exact hzNotB hoB
  have hzero' : ∀ i : Fin n,
      i ≠ o → i ≠ x → i ≠ z → c i = 0 := by
    intro i hio hix hiz
    simpa [c, o] using hzero i hio hix hiz
  have hcx : c x = lambda := by
    simpa [c] using (hfiber.2.2.2.2.2.1 f).2.1
  have signedOwnerOne
      (hoOne : c o = 1) (hxMinus : c x = -1) (hzZero : c z = 0) :
      ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y) c o x := by
    have hzeroPair : ∀ i : Fin n, i ≠ o → i ≠ x → c i = 0 := by
      intro i hio hix
      by_cases hiz : i = z
      · subst i
        exact hzZero
      · exact hzero' i hio hix hiz
    have hrestrict :
        ∑ i ∈ ({o, x} : Finset (Fin n)), c i • g i =
          ∑ i, c i • g i := by
      exact Finset.sum_subset (by simp) (by
        intro i _ hi
        rw [hzeroPair i (by
          intro hio
          exact hi (by simp [hio])) (by
          intro hix
          exact hi (by simp [hix])), zero_zsmul])
    have htarget : scalar ((f : ↥E) : ↥J) • y = g o - g x := by
      calc
        scalar ((f : ↥E) : ↥J) • y = ∑ i, c i • g i := hc.2.2.2.symm
        _ = ∑ i ∈ ({o, x} : Finset (Fin n)), c i • g i := hrestrict.symm
        _ = g o - g x := by
          rw [Finset.sum_pair hox]
          simp [hoOne, hxMinus, sub_eq_add_neg]
    exact ⟨hox, ⟨Or.inl ⟨hoOne, hxMinus, htarget⟩, hzeroPair⟩⟩
  have signedOwnerMinus
      (hoMinus : c o = -1) (hxOne : c x = 1) (hzZero : c z = 0) :
      ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y) c o x := by
    have hzeroPair : ∀ i : Fin n, i ≠ o → i ≠ x → c i = 0 := by
      intro i hio hix
      by_cases hiz : i = z
      · subst i
        exact hzZero
      · exact hzero' i hio hix hiz
    have hrestrict :
        ∑ i ∈ ({o, x} : Finset (Fin n)), c i • g i =
          ∑ i, c i • g i := by
      exact Finset.sum_subset (by simp) (by
        intro i _ hi
        rw [hzeroPair i (by
          intro hio
          exact hi (by simp [hio])) (by
          intro hix
          exact hi (by simp [hix])), zero_zsmul])
    have htarget : scalar ((f : ↥E) : ↥J) • y = g x - g o := by
      calc
        scalar ((f : ↥E) : ↥J) • y = ∑ i, c i • g i := hc.2.2.2.symm
        _ = ∑ i ∈ ({o, x} : Finset (Fin n)), c i • g i := hrestrict.symm
        _ = g x - g o := by
          rw [Finset.sum_pair hox]
          simp [hoMinus, hxOne, sub_eq_add_neg]
          abel
    exact ⟨hox, ⟨Or.inr ⟨hoMinus, hxOne, htarget⟩, hzeroPair⟩⟩
  rcases hprofiles with
      ⟨hlambda, ⟨hoMinus, hzTwo⟩ |
        ⟨hoOne, hzZero⟩ | ⟨hoTwo, hzMinus⟩⟩ |
      ⟨hlambda, hoMinus, hzZero⟩ |
      ⟨hlambda, hoMinus, hzMinus⟩
  · have hoMinus' : c o = -1 := by simpa [c, o] using hoMinus
    have hzTwo' : c z = 2 := by simpa [c] using hzTwo
    have hxMinus : c x = -1 := by rw [hcx, hlambda]
    have homit : ∀ i, c i = -1 ↔ i = o ∨ i = x := by
      intro i
      constructor
      · intro hi
        by_cases hio : i = o
        · exact Or.inl hio
        by_cases hix : i = x
        · exact Or.inr hix
        by_cases hiz : i = z
        · subst i
          rw [hzTwo'] at hi
          norm_num at hi
        · have hiZero := hzero' i hio hix hiz
          omega
      · intro hi
        rcases hi with rfl | rfl
        · exact hoMinus'
        · exact hxMinus
    have hshape : c = pureEdgeCoeffs z o x :=
      exactPair_coeff_two_eq_pureEdgeCoeffs
        g hc o x z hox homit hoz.symm hzNeX hzTwo'
    refine ⟨z, hzNotB, hzNeX, Or.inl ⟨hlambda, Or.inl ?_⟩⟩
    simpa [c, o] using hshape
  · have hoOne' : c o = 1 := by simpa [c, o] using hoOne
    have hzZero' : c z = 0 := by simpa [c] using hzZero
    have hxMinus : c x = -1 := by rw [hcx, hlambda]
    have hsigned := signedOwnerOne hoOne' hxMinus hzZero'
    refine ⟨z, hzNotB, hzNeX, Or.inl ⟨hlambda, Or.inr (Or.inl ?_)⟩⟩
    simpa [c, o] using hsigned
  · have hoTwo' : c o = 2 := by simpa [c, o] using hoTwo
    have hzMinus' : c z = -1 := by simpa [c] using hzMinus
    have hxMinus : c x = -1 := by rw [hcx, hlambda]
    have homit : ∀ i, c i = -1 ↔ i = x ∨ i = z := by
      intro i
      constructor
      · intro hi
        by_cases hio : i = o
        · subst i
          rw [hoTwo'] at hi
          norm_num at hi
        by_cases hix : i = x
        · exact Or.inl hix
        by_cases hiz : i = z
        · exact Or.inr hiz
        · have hiZero := hzero' i hio hix hiz
          omega
      · intro hi
        rcases hi with rfl | rfl
        · exact hxMinus
        · exact hzMinus'
    have hshape : c = pureEdgeCoeffs o x z :=
      exactPair_coeff_two_eq_pureEdgeCoeffs
        g hc x z o hzNeX.symm homit hox hoz hoTwo'
    refine ⟨z, hzNotB, hzNeX, Or.inl ⟨hlambda, Or.inr (Or.inr ?_)⟩⟩
    simpa [c, o] using hshape
  · have hoMinus' : c o = -1 := by simpa [c, o] using hoMinus
    have hzZero' : c z = 0 := by simpa [c] using hzZero
    have hxOne : c x = 1 := by rw [hcx, hlambda]
    have hsigned := signedOwnerMinus hoMinus' hxOne hzZero'
    refine ⟨z, hzNotB, hzNeX, Or.inr (Or.inl ⟨hlambda, ?_⟩)⟩
    simpa [c, o] using hsigned
  · have hoMinus' : c o = -1 := by simpa [c, o] using hoMinus
    have hzMinus' : c z = -1 := by simpa [c] using hzMinus
    have hxTwo : c x = 2 := by rw [hcx, hlambda]
    have homit : ∀ i, c i = -1 ↔ i = o ∨ i = z := by
      intro i
      constructor
      · intro hi
        by_cases hio : i = o
        · exact Or.inl hio
        by_cases hix : i = x
        · subst i
          rw [hxTwo] at hi
          norm_num at hi
        by_cases hiz : i = z
        · exact Or.inr hiz
        · have hiZero := hzero' i hio hix hiz
          omega
      · intro hi
        rcases hi with rfl | rfl
        · exact hoMinus'
        · exact hzMinus'
    have hshape : c = pureEdgeCoeffs x o z :=
      exactPair_coeff_two_eq_pureEdgeCoeffs
        g hc o z x hoz homit hox.symm hzNeX.symm hxTwo
    refine ⟨z, hzNotB, hzNeX, Or.inr (Or.inr ⟨hlambda, ?_⟩)⟩
    simpa [c, o] using hshape

/-- The target represented by a pure-edge coefficient vector is its affine
edge value.  This form is convenient when row normal forms are compared with
the relative doubling recurrence. -/
theorem witness_target_eq_of_coeff_eq_pureEdgeCoeffs
    (g : Fin n → G) {target : G} {c : Fin n → ℤ}
    (hc : Witness g target c) (u v w : Fin n)
    (hshape : c = pureEdgeCoeffs u v w) :
    target = 2 • g u - g v - g w := by
  rw [hshape] at hc
  rw [← hc.2.2.2]
  simp [pureEdgeCoeffs, sub_smul, Finset.sum_sub_distrib]
  rw [two_zsmul, two_nsmul]

/-- Family-level affine target equations in the exact two-retained regime.
The second retained coordinate is chosen once for the entire fiber.  Every
row target is then one of three fixed affine laws in its private owner; for
`lambda = 1` or `lambda = 2` the law is already unique. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_familyAffineTargets
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2) :
    ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
      ∀ f : ↥F,
        let o := center (P.symm (((f : ↥E) : ↥J) : Fin d))
        let c := coeff ((f : ↥E) : ↥J)
        let target := scalar ((f : ↥E) : ↥J) • y
        (lambda = -1 ∧
            ((c o = -1 ∧ target = 2 • g z - g o - g x) ∨
              (c o = 1 ∧ target = g o - g x) ∨
              (c o = 2 ∧ target = 2 • g o - g x - g z))) ∨
          (lambda = 1 ∧ c o = -1 ∧ target = g x - g o) ∨
          (lambda = 2 ∧ c o = -1 ∧
            target = 2 • g x - g o - g z) := by
  classical
  have hxNotB : x ∉ B := hfiber.2.1
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxNotB⟩
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hCone : 1 < (Finset.univ \ B).card := by omega
  obtain ⟨u, huC, z, hzC, huz⟩ := Finset.one_lt_card.mp hCone
  obtain ⟨z, hzC, hzNeX⟩ :
      ∃ z ∈ Finset.univ \ B, z ≠ x := by
    by_cases hux : u = x
    · refine ⟨z, hzC, ?_⟩
      intro hzx
      exact huz (hux.trans hzx.symm)
    · exact ⟨u, huC, hux⟩
  have hzNotB : z ∉ B := (Finset.mem_sdiff.mp hzC).2
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem
      hCcard hxC hzC hzNeX.symm
  refine ⟨z, hzNotB, hzNeX, ?_⟩
  intro f
  let o : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  let target : G := scalar ((f : ↥E) : ↥J) • y
  let c : Fin n → ℤ := coeff ((f : ↥E) : ↥J)
  have hc : Witness g target c := by
    simpa [target, c] using hrows ((f : ↥E) : ↥J)
  have hcx : c x = lambda := by
    simpa [c] using (hfiber.2.2.2.2.2.1 f).2.1
  have hoB : o ∈ B := by
    simpa [o] using (hfiber.2.2.2.2.2.1 f).1
  have hox : o ≠ x := by
    intro hox
    subst x
    exact hxNotB hoB
  have hoz : o ≠ z := by
    intro hoz
    subst z
    exact hzNotB hoB
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_signedPair_or_pureEdge
      g y B center P scalar coeff F x lambda hfiber hrows f hretained with
    ⟨zf, hzfNotB, hzfNeX, hgeometry⟩
  have hzfC : zf ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzfNotB⟩
  have hzfEq : zf = z := by
    have hpair : zf = x ∨ zf = z := by
      have : zf ∈ ({x, z} : Finset (Fin n)) := by
        rw [← hCeq]
        exact hzfC
      simpa using this
    exact hpair.resolve_left hzfNeX
  subst zf
  rcases hgeometry with
      ⟨hlambda, hleft | hsigned | hright⟩ |
      ⟨hlambda, hsigned⟩ | ⟨hlambda, hcenter⟩
  · left
    refine ⟨hlambda, Or.inl ⟨?_, ?_⟩⟩
    · have hleft' : c = pureEdgeCoeffs z o x := by
        simpa [c, o] using hleft
      change c o = -1
      rw [hleft']
      simp [pureEdgeCoeffs, hoz, hox]
    · exact witness_target_eq_of_coeff_eq_pureEdgeCoeffs
        g hc z o x (by simpa [c, o] using hleft)
  · left
    refine ⟨hlambda, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    rcases hsigned.2.1 with hforward | hreverse
    · simpa [c, o] using hforward.1
    · have hxOne : c x = 1 := by simpa [c] using hreverse.2.1
      have hxMinus : c x = -1 := by rw [hcx, hlambda]
      omega
    · rcases hsigned.2.1 with hforward | hreverse
      · simpa [target, o] using hforward.2.2
      · have hxOne : c x = 1 := by simpa [c] using hreverse.2.1
        have hxMinus : c x = -1 := by rw [hcx, hlambda]
        omega
  · left
    refine ⟨hlambda, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · have hright' : c = pureEdgeCoeffs o x z := by
        simpa [c, o] using hright
      change c o = 2
      rw [hright']
      simp [pureEdgeCoeffs, hox, hoz]
    · exact witness_target_eq_of_coeff_eq_pureEdgeCoeffs
        g hc o x z (by simpa [c, o] using hright)
  · right
    left
    refine ⟨hlambda, ?_, ?_⟩
    rcases hsigned.2.1 with hforward | hreverse
    · have hxMinus : c x = -1 := by simpa [c] using hforward.2.1
      have hxOne : c x = 1 := by rw [hcx, hlambda]
      omega
    · simpa [c, o] using hreverse.1
    · rcases hsigned.2.1 with hforward | hreverse
      · have hxMinus : c x = -1 := by simpa [c] using hforward.2.1
        have hxOne : c x = 1 := by rw [hcx, hlambda]
        omega
      · simpa [target, o] using hreverse.2.2
  · right
    right
    refine ⟨hlambda, ?_, ?_⟩
    · have hcenter' : c = pureEdgeCoeffs x o z := by
        simpa [c, o] using hcenter
      change c o = -1
      rw [hcenter']
      simp [pureEdgeCoeffs, hox, hoz]
    · exact witness_target_eq_of_coeff_eq_pureEdgeCoeffs
        g hc x o z (by simpa [c, o] using hcenter)

/-- The constant-size alphabet for a common retained external coefficient
when exactly two coordinates survive deletion. -/
def twoRetainedExternalCoefficientLevels : Finset ℤ := {-1, 1, 2}

theorem card_twoRetainedExternalCoefficientLevels :
    twoRetainedExternalCoefficientLevels.card = 3 := by
  norm_num [twoRetainedExternalCoefficientLevels]

/-- Every nonempty fixed external coefficient fiber in the exact
two-retained regime uses one of the three profile-compatible levels. -/
theorem fixedExternalCoefficientPrivateFiber_lambda_mem_twoRetainedLevels
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F) (hretained : n - B.card = 2) :
    lambda ∈ twoRetainedExternalCoefficientLevels := by
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_rowProfile
      g y B center P scalar coeff F x lambda hfiber hrows f hretained with
    ⟨_z, _hzB, _hzx, _hzero, hprofiles⟩
  rcases hprofiles with ⟨hlambda, _hprofile⟩ |
      ⟨hlambda, _howner, _hz⟩ | ⟨hlambda, _howner, _hz⟩
  · simp [twoRetainedExternalCoefficientLevels, hlambda]
  · simp [twoRetainedExternalCoefficientLevels, hlambda]
  · simp [twoRetainedExternalCoefficientLevels, hlambda]

/-- Every coefficient in the exact two-retained alphabet is a unit modulo
an odd prime.  Thus projection to any odd-primary layer never erases the
common external column and it may be normalized without a coefficient loss.
-/
theorem twoRetainedExternalCoefficientLevel_isUnit_mod_odd
    {p : ℕ} (hpOdd : Odd p) {lambda : ℤ}
    (hlevel : lambda ∈ twoRetainedExternalCoefficientLevels) :
    IsUnit (lambda : ZMod p) := by
  simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
    Finset.mem_singleton] at hlevel
  rcases hlevel with hminus | hone | htwo
  · subst lambda
    simpa only [Int.cast_neg, Int.cast_one] using
      (isUnit_neg_one : IsUnit (-1 : ZMod p))
  · subst lambda
    simpa only [Int.cast_one] using (isUnit_one : IsUnit (1 : ZMod p))
  · subst lambda
    have hunit : IsUnit ((2 : ℕ) : ZMod p) :=
      (ZMod.isUnit_iff_coprime 2 p).mpr
        ((Nat.prime_two.coprime_iff_not_dvd).mpr hpOdd.not_two_dvd_nat)
    convert hunit using 1
    all_goals norm_num

/-- Fixed external fibers therefore retain an invertible common column in
every odd-prime projection of the cyclic-kernel arithmetic. -/
theorem fixedExternalCoefficientPrivateFiber_lambda_isUnit_mod_odd
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F) (hretained : n - B.card = 2)
    {p : ℕ} (hpOdd : Odd p) :
    IsUnit (lambda : ZMod p) := by
  exact twoRetainedExternalCoefficientLevel_isUnit_mod_odd hpOdd
    (fixedExternalCoefficientPrivateFiber_lambda_mem_twoRetainedLevels
      g y B center P scalar coeff F x lambda hfiber hrows f hretained)

/-- The private-owner coefficient of every row belongs to the same constant
three-element alphabet.  Combined with the common external coefficient, it
identifies one of the five affine row profiles. -/
theorem fixedExternalCoefficientPrivateFiber_ownerCoefficient_mem_twoRetainedLevels
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (f : ↥F) (hretained : n - B.card = 2) :
    coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) ∈
      twoRetainedExternalCoefficientLevels := by
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_familyAffineTargets
      g y B center P scalar coeff F x lambda hfiber hrows hretained with
    ⟨z, _hzB, _hzx, haffine⟩
  rcases haffine f with
      ⟨_hlambda, ⟨howner, _htarget⟩ |
        ⟨howner, _htarget⟩ | ⟨howner, _htarget⟩⟩ |
      ⟨_hlambda, howner, _htarget⟩ |
      ⟨_hlambda, howner, _htarget⟩
  all_goals simp [twoRetainedExternalCoefficientLevels, howner]

/-- Adaptive extraction of a uniform affine external-row profile.  At most
three owner coefficients occur, so either `3*K` rows pay for all profiles or
one subfamily of more than `K` rows obeys one fixed affine law in its owner.
The companion retained coordinate is common to the entire original fiber.
-/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_capacity_or_largeAffineProfile
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2) (K : ℕ) :
    ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
      (F.card ≤ 3 * K ∨
        ∃ mu ∈ twoRetainedExternalCoefficientLevels,
          K < (Finset.univ.filter (fun f : ↥F ↦
            coeff ((f : ↥E) : ↥J)
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)).card ∧
          ∀ f : ↥(Finset.univ.filter (fun f : ↥F ↦
              coeff ((f : ↥E) : ↥J)
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)),
            let o := center
              (P.symm (((((f : ↥F) : ↥E) : ↥J)) : Fin d))
            let target := scalar (((f : ↥F) : ↥E) : ↥J) • y
            (lambda = -1 ∧ mu = -1 ∧
                target = 2 • g z - g o - g x) ∨
              (lambda = -1 ∧ mu = 1 ∧ target = g o - g x) ∨
              (lambda = -1 ∧ mu = 2 ∧
                target = 2 • g o - g x - g z) ∨
              (lambda = 1 ∧ mu = -1 ∧ target = g x - g o) ∨
              (lambda = 2 ∧ mu = -1 ∧
                target = 2 • g x - g o - g z)) := by
  classical
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_familyAffineTargets
      g y B center P scalar coeff F x lambda hfiber hrows hretained with
    ⟨z, hzB, hzx, haffine⟩
  let ownerCoeff : ↥F → ℤ := fun f ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d)))
  have hownerMem : ∀ f : ↥F,
      ownerCoeff f ∈ twoRetainedExternalCoefficientLevels := by
    intro f
    exact fixedExternalCoefficientPrivateFiber_ownerCoefficient_mem_twoRetainedLevels
      g y B center P scalar coeff F x lambda hfiber hrows f hretained
  refine ⟨z, hzB, hzx, ?_⟩
  rcases finiteMap_capacity_or_largeFiber
      twoRetainedExternalCoefficientLevels ownerCoeff hownerMem K with
    hcap | ⟨mu, hmuLevel, hlarge⟩
  · left
    have hcap' : F.card ≤
        twoRetainedExternalCoefficientLevels.card * K := by
      simpa [Fintype.card_coe] using hcap
    simpa [card_twoRetainedExternalCoefficientLevels] using hcap'
  · right
    refine ⟨mu, hmuLevel, by simpa [ownerCoeff, Fintype.card_coe] using hlarge,
      ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    rcases haffine (f : ↥F) with
        ⟨hlambda, ⟨howner, htarget⟩ |
          ⟨howner, htarget⟩ | ⟨howner, htarget⟩⟩ |
        ⟨hlambda, howner, htarget⟩ |
        ⟨hlambda, howner, htarget⟩
    · exact Or.inl ⟨hlambda, by simpa [ownerCoeff] using hmu.symm.trans howner,
        htarget⟩
    · exact Or.inr (Or.inl
        ⟨hlambda, by simpa [ownerCoeff] using hmu.symm.trans howner, htarget⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨hlambda, by simpa [ownerCoeff] using hmu.symm.trans howner, htarget⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hlambda, by simpa [ownerCoeff] using hmu.symm.trans howner, htarget⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hlambda, by simpa [ownerCoeff] using hmu.symm.trans howner, htarget⟩)))

/-- A fixed external fiber contains more than `K` rows governed by one
affine law, with the common companion coordinate and owner coefficient made
explicit. -/
def FixedExternalTwoRetainedAffineProfileAbove
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (K : ℕ) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      K < (Finset.univ.filter (fun f : ↥F ↦
        coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)).card ∧
      ∀ f : ↥(Finset.univ.filter (fun f : ↥F ↦
          coeff ((f : ↥E) : ↥J)
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)),
        let o := center (P.symm (((((f : ↥F) : ↥E) : ↥J)) : Fin d))
        let target := scalar (((f : ↥F) : ↥E) : ↥J) • y
        (lambda = -1 ∧ mu = -1 ∧
            target = 2 • g z - g o - g x) ∨
          (lambda = -1 ∧ mu = 1 ∧ target = g o - g x) ∨
          (lambda = -1 ∧ mu = 2 ∧
            target = 2 • g o - g x - g z) ∨
          (lambda = 1 ∧ mu = -1 ∧ target = g x - g o) ∨
          (lambda = 2 ∧ mu = -1 ∧
            target = 2 • g x - g o - g z)

/-- A fiber above the external `1/12` scale contains an affine-homogeneous
subfamily above the `1/36` scale.  This composes the only remaining
three-profile loss without introducing any dimension-dependent factor. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_affineProfileAbove_of_largeFiber
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2)
    (hlarge : (d - 1) / 12 < F.card) :
    FixedExternalTwoRetainedAffineProfileAbove
      g y B center P scalar coeff F x lambda ((d - 1) / 36) := by
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_capacity_or_largeAffineProfile
      g y B center P scalar coeff F x lambda hfiber hrows hretained
        ((d - 1) / 36) with
    ⟨z, hzB, hzx, hcap | hprofile⟩
  · exfalso
    omega
  · exact ⟨z, hzB, hzx, hprofile⟩

/-- A private witness evaluated at any nonzero retained coordinate uses the
same constant three-level alphabet when exactly two coordinates survive.
This rowwise form does not presuppose that a larger fixed fiber has already
been selected. -/
theorem privateWitness_externalCoefficient_mem_twoRetainedLevels
    (g : Fin n → G) {target : G} {c : Fin n → ℤ}
    (hc : Witness g target c) (B : Finset (Fin n))
    (owner x : Fin n) (hownerB : owner ∈ B) (_howner : c owner ≠ 0)
    (hprivate : ∀ i, i ∈ B → i ≠ owner → c i = 0)
    (hxB : x ∉ B) (hx : c x ≠ 0) (hretained : n - B.card = 2) :
    c x ∈ twoRetainedExternalCoefficientLevels := by
  classical
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hCone : 1 < (Finset.univ \ B).card := by omega
  obtain ⟨u, huC, z, hzC, huz⟩ := Finset.one_lt_card.mp hCone
  obtain ⟨z, hzC, hzNeX⟩ :
      ∃ z ∈ Finset.univ \ B, z ≠ x := by
    by_cases hux : u = x
    · refine ⟨z, hzC, ?_⟩
      intro hzx
      exact huz (hux.trans hzx.symm)
    · exact ⟨u, huC, hux⟩
  have hzB : z ∉ B := (Finset.mem_sdiff.mp hzC).2
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem
      hCcard hxC hzC hzNeX.symm
  have hownerX : owner ≠ x := by
    intro hownerX
    subst x
    exact hxB hownerB
  have hownerZ : owner ≠ z := by
    intro hownerZ
    subst z
    exact hzB hownerB
  have hzeroOutside : ∀ i : Fin n,
      i ≠ owner → i ≠ x → i ≠ z → c i = 0 := by
    intro i hiOwner hix hiz
    have hiB : i ∈ B := by
      by_contra hiNotB
      have hiC : i ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiNotB⟩
      have hiPair : i = x ∨ i = z := by
        have : i ∈ ({x, z} : Finset (Fin n)) := by
          rw [← hCeq]
          exact hiC
        simpa using this
      exact hiPair.elim hix hiz
    exact hprivate i hiB hiOwner
  have hrestrict :
      ∑ i ∈ ({owner, x, z} : Finset (Fin n)), c i = ∑ i, c i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      apply hzeroOutside i
      · intro hiOwner
        exact hi (by simp [hiOwner])
      · intro hix
        exact hi (by simp [hix])
      · intro hiz
        exact hi (by simp [hiz]))
  have hownerNotPair : owner ∉ ({x, z} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hownerX, hownerZ⟩
  have hxNotZ : x ∉ ({z} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hzNeX.symm
  have hsum : c owner + c x + c z = 0 := by
    calc
      c owner + c x + c z =
          ∑ i ∈ ({owner, x, z} : Finset (Fin n)), c i := by
        rw [Finset.sum_insert hownerNotPair, Finset.sum_insert hxNotZ]
        simp [add_assoc]
      _ = ∑ i, c i := hrestrict
      _ = 0 := hc.2.2.1
  have hownerFloor := hc.2.1 owner
  have hxFloor := hc.2.1 x
  have hzFloor := hc.2.1 z
  have hlevel : c x = -1 ∨ c x = 1 ∨ c x = 2 := by omega
  rcases hlevel with hlevel | hlevel | hlevel
  · simp [twoRetainedExternalCoefficientLevels, hlevel]
  · simp [twoRetainedExternalCoefficientLevels, hlevel]
  · simp [twoRetainedExternalCoefficientLevels, hlevel]

/-- Constant-capacity adaptive external-row frontier in the exact
two-retained regime.  There are at most two eligible retained coordinates
and exactly three possible nonzero coefficient levels, so either `6*K` rows
pay for all labels or one fixed label supports more than `K` rows with the
full private diagonal-plus-common-column structure. -/
theorem twoRetainedExternalRows_capacity_or_largePrivateFiber
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (E : Finset ↥J)
    (supportCoord : ↥E → Fin n)
    (hsupport : ∀ e : ↥E,
      supportCoord e ∉ Finset.univ.image center ∧
      supportCoord e ∉ B ∧
      coeff (e : ↥J) (supportCoord e) ≠ 0)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hprivate : ∀ (j : ↥J) i, i ∈ B →
      i ≠ center (P.symm (j : Fin d)) → coeff j i = 0)
    (hcenterInj : Function.Injective center)
    (hownerMem : ∀ j : ↥J, center (P.symm (j : Fin d)) ∈ B)
    (howner : ∀ j : ↥J,
      coeff j (center (P.symm (j : Fin d))) ≠ 0)
    (hcoeffInj : Function.Injective coeff)
    (hretained : n - B.card = 2) (K : ℕ) :
    E.card ≤ 6 * K ∨
      ∃ z ∈ (((Finset.univ \ B) \
            (Finset.univ.image center : Finset (Fin n))).product
          twoRetainedExternalCoefficientLevels),
        K < (Finset.univ.filter (fun e : ↥E ↦
          (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z)).card ∧
        FixedExternalCoefficientPrivateFiber B center P coeff
          (Finset.univ.filter (fun e : ↥E ↦
            (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z))
          z.1 z.2 := by
  classical
  let R : Finset (Fin n) :=
    (Finset.univ \ B) \ Finset.univ.image center
  let level : ↥E → (Fin n × ℤ) := fun e ↦
    (supportCoord e, coeff (e : ↥J) (supportCoord e))
  have hsupportMem : ∀ e : ↥E, supportCoord e ∈ R := by
    intro e
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (hsupport e).2.1⟩,
        (hsupport e).1⟩
  have hlevelMem : ∀ e : ↥E,
      level e ∈ R.product twoRetainedExternalCoefficientLevels := by
    intro e
    exact Finset.mem_product.mpr
      ⟨hsupportMem e,
        privateWitness_externalCoefficient_mem_twoRetainedLevels
          g (hrows (e : ↥J)) B
          (center (P.symm ((e : ↥J) : Fin d))) (supportCoord e)
          (hownerMem (e : ↥J)) (howner (e : ↥J))
          (hprivate (e : ↥J)) (hsupport e).2.1
          (hsupport e).2.2 hretained⟩
  rcases finiteMap_capacity_or_largeFiber
      (R.product twoRetainedExternalCoefficientLevels)
      level hlevelMem K with hcap | ⟨z, hz, hlarge⟩
  · left
    have hcap' : E.card ≤
        (R.product twoRetainedExternalCoefficientLevels).card * K := by
      simpa [Fintype.card_coe] using hcap
    have hRsub : R ⊆ Finset.univ \ B := by
      intro i hi
      exact (Finset.mem_sdiff.mp hi).1
    have hRcard : R.card ≤ 2 := by
      have hle := Finset.card_le_card hRsub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)] at hle
      simpa [hretained] using hle
    have hproductCard :
        (R.product twoRetainedExternalCoefficientLevels).card ≤ 6 := by
      calc
        (R.product twoRetainedExternalCoefficientLevels).card =
            R.card * twoRetainedExternalCoefficientLevels.card :=
          Finset.card_product R twoRetainedExternalCoefficientLevels
        _ = R.card * 3 := by rw [card_twoRetainedExternalCoefficientLevels]
        _ ≤ 6 := by omega
    exact hcap'.trans (Nat.mul_le_mul_right K hproductCard)
  · right
    refine ⟨z, by simpa [R] using hz,
      by simpa [level, Fintype.card_coe] using hlarge, ?_⟩
    rcases Finset.mem_product.mp hz with ⟨hzR, hzLevel⟩
    have hzParts := Finset.mem_sdiff.mp hzR
    have hzNotB := (Finset.mem_sdiff.mp hzParts.1).2
    have hzOutside := hzParts.2
    have hzNonzero : z.2 ≠ 0 := by
      intro hzZero
      rw [hzZero] at hzLevel
      simp [twoRetainedExternalCoefficientLevels] at hzLevel
    have hfiberLevel : ∀ f : ↥(Finset.univ.filter
        (fun e : ↥E ↦ level e = z)), level (f : ↥E) = z := by
      intro f
      exact (Finset.mem_filter.mp f.property).2
    refine ⟨hzOutside, hzNotB, hzNonzero, ?_, ?_, ?_, ?_, ?_⟩
    · intro f k hownerEq
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact P.symm.injective (hcenterInj hownerEq)
    · intro f k hcoeffEq
      apply Subtype.ext
      apply Subtype.ext
      exact hcoeffInj hcoeffEq
    · intro f
      have hf := hfiberLevel f
      have hcoord : supportCoord (f : ↥E) = z.1 :=
        congrArg Prod.fst hf
      have hvalue :
          coeff ((f : ↥E) : ↥J) (supportCoord (f : ↥E)) = z.2 :=
        congrArg Prod.snd hf
      refine ⟨hownerMem ((f : ↥E) : ↥J), ?_,
        howner ((f : ↥E) : ↥J)⟩
      rw [← hcoord]
      exact hvalue
    · intro f i hiB hiOwner
      exact hprivate ((f : ↥E) : ↥J) i hiB hiOwner
    · intro f k hfk
      apply hprivate ((f : ↥E) : ↥J)
        (center (P.symm (((k : ↥E) : ↥J) : Fin d)))
        (hownerMem ((k : ↥E) : ↥J))
      intro hownerEq
      apply hfk
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact P.symm.injective (hcenterInj hownerEq.symm)

/-- Countable form of the retained external/internal row split. -/
def RetainedExternalInternalRowPartition
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ E I : Finset ↥J,
      d - 1 ≤ J.card ∧ Function.Injective coeff ∧
      (∀ j, scalar j • y ≠ 0 ∧
        Witness g (scalar j • y) (coeff j)) ∧
      (∀ (j : ↥J) x, x ∈ B →
        x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
      Function.Injective center ∧
      (∀ j : ↥J, center (P.symm (j : Fin d)) ∈ B) ∧
      (∀ j : ↥J, coeff j (center (P.symm (j : Fin d))) ≠ 0) ∧
      E ∪ I = Finset.univ ∧ Disjoint E I ∧
      E.card + I.card = J.card ∧ d - 1 ≤ E.card + I.card ∧
      (∀ j : ↥J, j ∈ E ↔
        HasRetainedExternalCenterSupport center B (coeff j)) ∧
      ∃ supportCoord : ↥E → Fin n,
        (∀ e : ↥E,
          supportCoord e ∉ Finset.univ.image center ∧
          supportCoord e ∉ B ∧
          coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
        (∀ K : ℕ,
          E.card ≤
              (((Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n))).card * K) ∨
            ∃ x ∈ (Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n)),
              K < (Finset.univ.filter
                (fun e : ↥E ↦ supportCoord e = x)).card) ∧
        (∀ K : ℕ,
          E.card ≤
              ((((Finset.univ \ B) \
                  (Finset.univ.image center : Finset (Fin n))).product
                (witnessNonzeroCoefficientLevels n)).card * K) ∨
            ∃ z ∈ ((Finset.univ \ B) \
                  (Finset.univ.image center : Finset (Fin n))).product
                (witnessNonzeroCoefficientLevels n),
              K < (Finset.univ.filter (fun e : ↥E ↦
                (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z)).card ∧
              FixedExternalCoefficientPrivateFiber B center P coeff
                (Finset.univ.filter (fun e : ↥E ↦
                  (supportCoord e,
                    coeff (e : ↥J) (supportCoord e)) = z)) z.1 z.2) ∧
        (I = ∅ ∨
        ∃ pivot : Fin d, center pivot ∉ B ∧
          ∀ j : ↥I,
            ExactSignedPairWitness g (scalar (j : ↥J) • y)
              (coeff (j : ↥J))
              (center (P.symm (j : Fin d))) (center pivot))

/-- Lossless row-partition payload specialized to an exact two-coordinate
quotient.  It retains the same external/internal sets and common-pivot arm,
but replaces the generic `(n+1)` coefficient capacity by the constant-six
adaptive frontier. -/
def TwoRetainedExternalInternalRowFrontier
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ E I : Finset ↥J,
      E ∪ I = Finset.univ ∧ Disjoint E I ∧
      E.card + I.card = J.card ∧ d - 1 ≤ E.card + I.card ∧
      (∀ j, scalar j • y ≠ 0 ∧
        Witness g (scalar j • y) (coeff j)) ∧
      ∃ supportCoord : ↥E → Fin n,
        (∀ e : ↥E,
          supportCoord e ∉ Finset.univ.image center ∧
          supportCoord e ∉ B ∧
          coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
        (∀ K : ℕ,
          E.card ≤ 6 * K ∨
            ∃ z ∈ (((Finset.univ \ B) \
                  (Finset.univ.image center : Finset (Fin n))).product
                twoRetainedExternalCoefficientLevels),
              K < (Finset.univ.filter (fun e : ↥E ↦
                (supportCoord e,
                  coeff (e : ↥J) (supportCoord e)) = z)).card ∧
              FixedExternalCoefficientPrivateFiber B center P coeff
                (Finset.univ.filter (fun e : ↥E ↦
                  (supportCoord e,
                    coeff (e : ↥J) (supportCoord e)) = z)) z.1 z.2) ∧
        (I = ∅ ∨
          ∃ pivot : Fin d, center pivot ∉ B ∧
            ∀ j : ↥I,
              ExactSignedPairWitness g (scalar (j : ↥J) • y)
                (coeff (j : ↥J))
                (center (P.symm (j : Fin d))) (center pivot))

/-- Extract the constant-six frontier from the exact rows and choices already
stored in `RetainedExternalInternalRowPartition`; no row, owner, coefficient,
or pivot data is reselected. -/
theorem twoRetainedExternalInternalRowFrontier_of_rowPartition
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hpart : RetainedExternalInternalRowPartition g y B center P J)
    (hretained : n - B.card = 2) :
    TwoRetainedExternalInternalRowFrontier g y B center P J := by
  classical
  rcases hpart with
    ⟨scalar, coeff, E, I, _hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner, hunion, hdisjoint, hcard, hlarge,
      _hEiff, supportCoord, hsupport, _hcoordFrontier,
      _hgenericLevelFrontier, hinternal⟩
  refine ⟨scalar, coeff, E, I, hunion, hdisjoint, hcard, hlarge,
    hrows, supportCoord, hsupport, ?_, hinternal⟩
  intro K
  exact twoRetainedExternalRows_capacity_or_largePrivateFiber
    g y B center P scalar coeff E supportCoord hsupport
      (fun j ↦ (hrows j).2) hprivate hcenterInj hownerMem howner
      hcoeffInj hretained K

/-- Quantitative external/internal alternative at the exact two-retained
endpoint.  Choosing the constant-capacity threshold `(d-1)/12` shows that
either the common-pivot internal class carries at least half of the required
rows, or one exact external `(coordinate, coefficient)` fiber has more than
one twelfth of them.  All row and fiber data are retained for the next
geometric comparison. -/
theorem twoRetainedExternalInternalRowFrontier_largeInternal_or_largeExternal
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hfrontier : TwoRetainedExternalInternalRowFrontier
      g y B center P J) :
    ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
      ∃ E I : Finset ↥J, ∃ supportCoord : ↥E → Fin n,
        E ∪ I = Finset.univ ∧ Disjoint E I ∧
        E.card + I.card = J.card ∧
        (∀ j, scalar j • y ≠ 0 ∧
          Witness g (scalar j • y) (coeff j)) ∧
        (∀ e : ↥E,
          supportCoord e ∉ Finset.univ.image center ∧
          supportCoord e ∉ B ∧
          coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
        ((d - 1 ≤ 2 * I.card ∧
            (I = ∅ ∨
              ∃ pivot : Fin d, center pivot ∉ B ∧
                ∀ j : ↥I,
                  ExactSignedPairWitness g (scalar (j : ↥J) • y)
                    (coeff (j : ↥J))
                    (center (P.symm (j : Fin d))) (center pivot))) ∨
          ∃ z ∈ (((Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n))).product
              twoRetainedExternalCoefficientLevels),
            (d - 1) / 12 < (Finset.univ.filter (fun e : ↥E ↦
              (supportCoord e,
                coeff (e : ↥J) (supportCoord e)) = z)).card ∧
            FixedExternalCoefficientPrivateFiber B center P coeff
              (Finset.univ.filter (fun e : ↥E ↦
                (supportCoord e,
                  coeff (e : ↥J) (supportCoord e)) = z)) z.1 z.2) := by
  classical
  rcases hfrontier with
    ⟨scalar, coeff, E, I, hunion, hdisjoint, hcard, hlarge,
      hrows, supportCoord, hsupport, hcapacity, hinternal⟩
  refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
    hrows, hsupport, ?_⟩
  rcases hcapacity ((d - 1) / 12) with hcap | hfiber
  · left
    refine ⟨?_, hinternal⟩
    omega
  · exact Or.inr hfiber

/-- Cycle-ready form of the exact two-retained row dichotomy.  Either the
common-pivot signed-pair class has half-density, or an external subfamily of
more than `(d-1)/36` rows has one fixed affine target law.  The original row
partition, witnesses, and fixed-fiber structure are all retained. -/
theorem twoRetainedExternalInternalRowFrontier_largeInternal_or_largeAffineExternal
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hfrontier : TwoRetainedExternalInternalRowFrontier
      g y B center P J)
    (hretained : n - B.card = 2) :
    ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
      ∃ E I : Finset ↥J, ∃ supportCoord : ↥E → Fin n,
        E ∪ I = Finset.univ ∧ Disjoint E I ∧
        E.card + I.card = J.card ∧
        (∀ j, scalar j • y ≠ 0 ∧
          Witness g (scalar j • y) (coeff j)) ∧
        (∀ e : ↥E,
          supportCoord e ∉ Finset.univ.image center ∧
          supportCoord e ∉ B ∧
          coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
        ((d - 1 ≤ 2 * I.card ∧
            (I = ∅ ∨
              ∃ pivot : Fin d, center pivot ∉ B ∧
                ∀ j : ↥I,
                  ExactSignedPairWitness g (scalar (j : ↥J) • y)
                    (coeff (j : ↥J))
                    (center (P.symm (j : Fin d))) (center pivot))) ∨
          ∃ label ∈ (((Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n))).product
              twoRetainedExternalCoefficientLevels),
            let F : Finset ↥E := Finset.univ.filter (fun e : ↥E ↦
              (supportCoord e,
                coeff (e : ↥J) (supportCoord e)) = label)
            FixedExternalCoefficientPrivateFiber
                B center P coeff F label.1 label.2 ∧
              FixedExternalTwoRetainedAffineProfileAbove
                g y B center P scalar coeff F label.1 label.2
                  ((d - 1) / 36)) := by
  classical
  rcases twoRetainedExternalInternalRowFrontier_largeInternal_or_largeExternal
      g y B center P J hfrontier with
    ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, hinternal | hexternal⟩
  · refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, Or.inl hinternal⟩
  · refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, Or.inr ?_⟩
    rcases hexternal with ⟨label, hlabel, hlarge, hfiber⟩
    refine ⟨label, hlabel, hfiber, ?_⟩
    exact fixedExternalCoefficientPrivateFiber_twoRetained_affineProfileAbove_of_largeFiber
      g y B center P scalar coeff
        (Finset.univ.filter (fun e : ↥E ↦
          (supportCoord e, coeff (e : ↥J) (supportCoord e)) = label))
        label.1 label.2 hfiber (fun j ↦ (hrows j).2) hretained hlarge

/-- Extract the explicit finite partition and one retained support coordinate
per external row from the retained mixed normal form. -/
theorem retainedExternalInternalRowPartition_of_mixed
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hout : CycleCenterSparseRetainedExternalOrCommonPivot
      g y B center P J) :
    RetainedExternalInternalRowPartition g y B center P J := by
  classical
  rcases hout with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hall | ⟨pivot, hpivot, hmixed⟩⟩
  all_goals
    let E : Finset ↥J := Finset.univ.filter
      (fun j ↦ HasRetainedExternalCenterSupport center B (coeff j))
    let I : Finset ↥J := Finset.univ \ E
    have hEiff : ∀ j : ↥J, j ∈ E ↔
        HasRetainedExternalCenterSupport center B (coeff j) := by
      intro j
      simp [E]
    have hunion : E ∪ I = Finset.univ := by
      ext j
      simp [I]
    have hdisjoint : Disjoint E I := by
      rw [Finset.disjoint_left]
      intro j hjE hjI
      exact (Finset.mem_sdiff.mp hjI).2 hjE
    have hcard : E.card + I.card = J.card := by
      have hpartition := Finset.card_sdiff_add_card_inter
        (Finset.univ : Finset ↥J) E
      have hEsub : E ⊆ (Finset.univ : Finset ↥J) := Finset.subset_univ E
      rw [Finset.inter_eq_right.mpr hEsub, Finset.card_univ] at hpartition
      change E.card + (Finset.univ \ E).card = J.card
      simp only [Fintype.card_coe] at hpartition
      omega
    have hsupport : ∀ e : ↥E,
        ∃ x : Fin n,
          x ∉ Finset.univ.image center ∧ x ∉ B ∧
            coeff (e : ↥J) x ≠ 0 := by
      intro e
      exact (hEiff (e : ↥J)).mp e.property
    choose supportCoord hsupportCoord using hsupport
    let R : Finset (Fin n) :=
      (Finset.univ \ B) \ Finset.univ.image center
    have hsupportMem : ∀ e : ↥E, supportCoord e ∈ R := by
      intro e
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (hsupportCoord e).2.1⟩,
          (hsupportCoord e).1⟩
    have hfrontier : ∀ K : ℕ,
        E.card ≤ R.card * K ∨
          ∃ x ∈ R,
            K < (Finset.univ.filter
              (fun e : ↥E ↦ supportCoord e = x)).card := by
      intro K
      simpa [Fintype.card_coe] using
        finiteMap_capacity_or_largeFiber R supportCoord hsupportMem K
    let level : ↥E → (Fin n × ℤ) :=
      fun e ↦ (supportCoord e, coeff (e : ↥J) (supportCoord e))
    have hlevelMem : ∀ e : ↥E,
        level e ∈ R.product (witnessNonzeroCoefficientLevels n) := by
      intro e
      exact Finset.mem_product.mpr
        ⟨hsupportMem e,
          witness_nonzeroCoefficient_mem_levels g
            (hrows (e : ↥J)).2 (hsupportCoord e).2.2⟩
    have hlevelFrontier : ∀ K : ℕ,
        E.card ≤
            (R.product (witnessNonzeroCoefficientLevels n)).card * K ∨
          ∃ z ∈ R.product (witnessNonzeroCoefficientLevels n),
            K < (Finset.univ.filter
              (fun e : ↥E ↦ level e = z)).card ∧
            FixedExternalCoefficientPrivateFiber B center P coeff
              (Finset.univ.filter (fun e : ↥E ↦ level e = z)) z.1 z.2 := by
      intro K
      rcases finiteMap_capacity_or_largeFiber
          (R.product (witnessNonzeroCoefficientLevels n))
          level hlevelMem K with hcap | ⟨z, hz, hlarge⟩
      · exact Or.inl (by simpa [Fintype.card_coe] using hcap)
      · right
        refine ⟨z, hz, by simpa [Fintype.card_coe] using hlarge, ?_⟩
        rcases Finset.mem_product.mp hz with ⟨hzR, hzLevel⟩
        have hzParts := Finset.mem_sdiff.mp hzR
        have hzNotB := (Finset.mem_sdiff.mp hzParts.1).2
        have hzOutside := hzParts.2
        have hzNonzero : z.2 ≠ 0 := by
          intro hzZero
          rw [hzZero] at hzLevel
          simp [witnessNonzeroCoefficientLevels] at hzLevel
        have hfiberLevel : ∀ f : ↥(Finset.univ.filter
            (fun e : ↥E ↦ level e = z)), level (f : ↥E) = z := by
          intro f
          exact (Finset.mem_filter.mp f.property).2
        refine ⟨hzOutside, hzNotB, hzNonzero, ?_, ?_, ?_, ?_, ?_⟩
        · intro f k hownerEq
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact P.symm.injective (hcenterInj hownerEq)
        · intro f k hcoeffEq
          apply Subtype.ext
          apply Subtype.ext
          exact hcoeffInj hcoeffEq
        · intro f
          have hf := hfiberLevel f
          have hcoord : supportCoord (f : ↥E) = z.1 :=
            congrArg Prod.fst hf
          have hvalue :
              coeff ((f : ↥E) : ↥J) (supportCoord (f : ↥E)) = z.2 :=
            congrArg Prod.snd hf
          refine ⟨hownerMem ((f : ↥E) : ↥J), ?_,
            howner ((f : ↥E) : ↥J)⟩
          rw [← hcoord]
          exact hvalue
        · intro f i hiB hiOwner
          exact hprivate ((f : ↥E) : ↥J) i hiB hiOwner
        · intro f k hfk
          apply hprivate ((f : ↥E) : ↥J)
            (center (P.symm (((k : ↥E) : ↥J) : Fin d)))
            (hownerMem ((k : ↥E) : ↥J))
          intro hownerEq
          apply hfk
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact P.symm.injective (hcenterInj hownerEq.symm)
  · refine ⟨scalar, coeff, E, I, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hunion, hdisjoint, hcard, ?_, hEiff, supportCoord, hsupportCoord,
      by simpa [R] using hfrontier,
      by simpa [R, level] using hlevelFrontier, Or.inl ?_⟩
    · omega
    · ext j
      simp [I, E, hall j]
  · refine ⟨scalar, coeff, E, I, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hunion, hdisjoint, hcard, ?_, hEiff, supportCoord, hsupportCoord,
      by simpa [R] using hfrontier,
      by simpa [R, level] using hlevelFrontier, ?_⟩
    · omega
    · by_cases hI : I = ∅
      · exact Or.inl hI
      · right
        refine ⟨pivot, hpivot, ?_⟩
        intro j
        rcases hmixed (j : ↥J) with hjExternal | hjPair
        · have hjE : (j : ↥J) ∈ E := (hEiff (j : ↥J)).mpr hjExternal
          exact False.elim ((Finset.mem_sdiff.mp j.property).2 hjE)
        · exact hjPair

/-- Global endpoint retaining the explicit finite external/internal row
partition alongside both preceding structural forms. -/
def PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let disp : Fin d → ZMod (2 ^ t * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          AddSubgroup.closure (Set.range disp) =
            AddSubgroup.zmultiples y ∧
          (∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J ∧
          CycleCenterSparseRetainedExternalOrCommonPivot
            g y B center P J ∧
          RetainedExternalInternalRowPartition
            g y B center P J)

/-- Attach the explicit row partition without changing any earlier data. -/
theorem pureEdgeStarLeafCycle_rowPartitionOutcome_of_retainedMixedOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleRetainedMixedOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        hsharp, hnormal⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        hsharp, hnormal,
        retainedExternalInternalRowPartition_of_mixed
          g y B center P J hnormal⟩)

/-- Global critical even-stratum endpoint with the selected rows split into
explicit finite retained-external and common-pivot classes. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRowPartitionOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (qroot : ReducedSubsetSumCollision g h)
    (hqCanonical : qroot ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((qroot, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', qroot) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        ∃ center : Fin d → Fin (m + 1),
          d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          IsMinimalFixedPointFreeCycle T a d ∧
          Function.Injective center ∧
          (∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1))) ∧
          PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedMixedOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_rowPartitionOutcome_of_retainedMixedOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
