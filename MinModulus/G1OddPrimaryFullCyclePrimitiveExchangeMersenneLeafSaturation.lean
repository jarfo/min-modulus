/-
# Exact saturation of the Mersenne leaf cycle

The lossless exact-Mersenne endpoint gives a primary union `U` equal to the
leaf range `L`, but the primary class itself is `C = insert r Sfull`.  The
original leaf incidence is full or punctured once.  Since `r` is outside the
deletion set but belongs to `L`, it is the unique missing leaf.  Every other
leaf is deleted and is parallel to `r`, so exact primary saturation puts it
in `Sfull`.  Consequently `C = L` and `Sfull = L.erase r`.

The same full-cycle argument also shows that every translated leaf, not only
their collective span, generates the whole odd kernel.  Thus every leaf
displacement has the full odd order.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLeafMode

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Every point of a fixed-point-free full doubling cycle generates the
cyclic subgroup generated collectively by the cycle. -/
theorem zmultiples_eq_of_isCycle_doubling_span
    {α : Type*} [Fintype α]
    (R : Equiv.Perm α) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (disp : α → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y)
    (i : α) :
    AddSubgroup.zmultiples (disp i) = AddSubgroup.zmultiples y := by
  apply le_antisymm
  · rw [← hspan, AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  · rw [← hspan]
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := sameCycle_doubling_eq_pow_two_nsmul
      R disp hdouble (hcycle.sameCycle (hRne i) (hRne j))
    rw [hk]
    exact (AddSubgroup.zmultiples (disp i)).nsmul_mem
      (AddSubgroup.mem_zmultiples (disp i)) (2 ^ k)

/-- Order form of full-cycle point generation in a finite ambient group. -/
theorem addOrderOf_eq_of_isCycle_doubling_span
    {α : Type*} [Fintype α] [Fintype G]
    (R : Equiv.Perm α) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (disp : α → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y)
    (i : α) :
    addOrderOf (disp i) = addOrderOf y := by
  classical
  have hgroups := zmultiples_eq_of_isCycle_doubling_span
    R hcycle hRne disp hdouble y hspan i
  have hcards :=
    congrArg (fun H : AddSubgroup G ↦ Fintype.card H) hgroups
  simpa only [Fintype.card_zmultiples] using hcards

/-- Core fixed-presentation data shared by the merged and separated exact
Mersenne leaf residuals. -/
def PrimitiveMiddleExactMersenneFixedPresentationData
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (S T Sfull : Finset (Fin n)) (k₀ w : ℤ) : Prop :=
  PrimitiveMiddleUniformLeafValueData
      g y B leaf p S T k₀ w ∧
    S ⊆ Sfull ∧
    addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g p.x - g p.z)) = 64 ∧
    16 ≤ Sfull.card ∧ Sfull ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
    (∀ b : ↥B, (b : Fin n) ∈ Sfull →
      p.weight b = 2 * k₀ ∧
      ((k₀ = -1 ∧
          g (b : Fin n) - g p.x ∈ AddSubgroup.zmultiples y ∧
          addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (b : Fin n) - g p.z)) = 64) ∨
        (k₀ = 0 ∧
          g (b : Fin n) - g p.z ∈ AddSubgroup.zmultiples y ∧
          addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (b : Fin n) - g p.x)) = 64))) ∧
    (let r := primitiveMiddleInsertedCoordinate p k₀
      ∀ b : ↥B,
        ((b : Fin n) ∈ Sfull ↔
          g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) ∧
    ((∀ b : ↥B, p.weight b ≠ -4) ∨
      ∀ b : ↥B, p.weight b ≠ 2)

/-- Refined exact-Mersenne residual.  In the merged arm the primary class is
the entire leaf cycle minus its unique missing point, and every translated
leaf has full odd order. -/
def PrimitiveMiddleExactMersenneLeafSaturationResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S T Sfull : Finset (Fin n), ∃ k₀ w : ℤ,
      PrimitiveMiddleExactMersenneFixedPresentationData
        g y B leaf p S T Sfull k₀ w ∧
      let r := primitiveMiddleInsertedCoordinate p k₀
      let C := insert r Sfull
      let L := (Finset.univ : Finset (Fin d)).image leaf
      ((∃ missing : Fin d,
          (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
          leaf missing = r ∧
          C = L ∧ Sfull = L.erase r ∧ Sfull.card + 1 = d ∧
          w = -2 ∧
          (∀ i, addOrderOf (g (leaf i) - base) = q) ∧
          2 ^ (L.card - 1) ≤ q ∧
          (∀ b ∈ L, ∀ c ∈ L,
            g b - g c ∈ AddSubgroup.zmultiples y) ∧
          L.card + 4 ≤ B.card ∧
          5 ≤ (B \ L).card ∧
          (∀ b ∈ B \ L, ∀ c ∈ L,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          PrimitiveSaturatedSecondaryResidueCapacity g y B L p k₀ ∧
          48 * L.card.choose (L.card / 2) < 2 ^ B.card) ∨
        ((∀ b ∈ L, ∀ c ∈ C,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          (∀ i j : ℕ,
            d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
          388960 * d.choose (d / 2) < 2 ^ B.card))

/-- If a complete primary owner fiber and its inserted point already exhaust
the leaf union, the inserted point is the unique missing leaf and every
other leaf is exactly one member of that fiber. -/
theorem primitiveMiddle_merged_leafSaturation_of_fixedPresentation
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (Sfull : Finset (Fin n)) (k₀ : ℤ)
    (hSsub : Sfull ⊆ B) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hcomplete :
      let r := primitiveMiddleInsertedCoordinate p k₀
      ∀ b : ↥B,
        ((b : Fin n) ∈ Sfull ↔
          g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing)
    (hunion :
      let r := primitiveMiddleInsertedCoordinate p k₀
      let C := insert r Sfull
      let L := (Finset.univ : Finset (Fin d)).image leaf
      L ∪ C = L)
    (hcoset :
      let r := primitiveMiddleInsertedCoordinate p k₀
      let C := insert r Sfull
      let L := (Finset.univ : Finset (Fin d)).image leaf
      let U := L ∪ C
      ∀ b ∈ U, ∀ c ∈ U,
        g b - g c ∈ AddSubgroup.zmultiples y) :
    let r := primitiveMiddleInsertedCoordinate p k₀
    let C := insert r Sfull
    let L := (Finset.univ : Finset (Fin d)).image leaf
    ∃ missing : Fin d,
      (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
      leaf missing = r ∧ C = L ∧ Sfull = L.erase r ∧
      Sfull.card + 1 = d := by
  classical
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r Sfull
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  let U : Finset (Fin n) := L ∪ C
  change L ∪ C = L at hunion
  change ∀ b ∈ U, ∀ c ∈ U,
    g b - g c ∈ AddSubgroup.zmultiples y at hcoset
  have hrNotB : r ∉ B := by
    rcases hmiddle with hk | hk
    · simpa only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
        using p.x_not_mem
    · have hkNe : k₀ ≠ -1 := by omega
      simpa only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
        using p.z_not_mem
  have hrNotS : r ∉ Sfull := fun hrS ↦ hrNotB (hSsub hrS)
  have hrC : r ∈ C := Finset.mem_insert_self _ _
  have hrU : r ∈ U := Finset.mem_union_right _ hrC
  have hrL : r ∈ L := by
    rw [← hunion]
    exact hrU
  obtain ⟨missing, _hmissingUniv, hmissingR⟩ :=
    Finset.mem_image.mp hrL
  have hpunctured : ∀ i, leaf i ∈ B ↔ i ≠ missing := by
    rcases hleafIncidence with hfull | ⟨missing₀, hpunctured₀⟩
    · exfalso
      apply hrNotB
      rw [← hmissingR]
      exact hfull missing
    · have hmissingEq : missing = missing₀ := by
        by_contra hneMissing
        apply hrNotB
        rw [← hmissingR]
        exact (hpunctured₀ missing).2 hneMissing
      simpa only [hmissingEq] using hpunctured₀
  have hCsubL : C ⊆ L := by
    intro b hbC
    have hbU : b ∈ U := Finset.mem_union_right _ hbC
    change b ∈ L ∪ C at hbU
    rw [hunion] at hbU
    exact hbU
  have hLsubC : L ⊆ C := by
    intro b hbL
    by_cases hbr : b = r
    · subst b
      exact hrC
    · obtain ⟨i, _hiUniv, hiLeaf⟩ := Finset.mem_image.mp hbL
      have hiMissing : i ≠ missing := by
        intro him
        apply hbr
        calc
          b = leaf i := hiLeaf.symm
          _ = leaf missing := by rw [him]
          _ = r := hmissingR
      have hbB : b ∈ B := by
        rw [← hiLeaf]
        exact (hpunctured i).2 hiMissing
      have hbU : b ∈ U := Finset.mem_union_left _ hbL
      have hparallel : g b - g r ∈ AddSubgroup.zmultiples y :=
        hcoset b hbU r hrU
      exact Finset.mem_insert_of_mem
        ((hcomplete ⟨b, hbB⟩).2 hparallel)
  have hCeq : C = L := Finset.Subset.antisymm hCsubL hLsubC
  have hSeq : Sfull = L.erase r := by
    calc
      Sfull = C.erase r := by simp [C, hrNotS]
      _ = L.erase r := by rw [hCeq]
  have hCcard : C.card = Sfull.card + 1 := by
    simp only [C, Finset.card_insert_of_notMem hrNotS]
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hcard : Sfull.card + 1 = d := by
    rw [hCeq, hLcard] at hCcard
    exact hCcard.symm
  exact ⟨missing, hpunctured, hmissingR, hCeq, hSeq, hcard⟩

/-- Refine the lossless exact-Mersenne leaf-mode endpoint.  The merged arm
now exposes the unique missing leaf, exact primary-cycle equality, and full
order of every leaf displacement; the separated capacity arm is unchanged. -/
theorem PrimitiveMiddleExactMersenneLeafModeResidual.toLeafSaturationResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (horder : addOrderOf y = q)
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing)
    (hresidual :
      PrimitiveMiddleExactMersenneLeafModeResidual g y B leaf) :
    PrimitiveMiddleExactMersenneLeafSaturationResidual
      g y B leaf base := by
  classical
  rcases hresidual with
    ⟨p, S, T, Sfull, k₀, w, hdata, hSsubset, hprimitive,
      hScard, hSsub, hmiddle, hrows, hcomplete, hwindow,
      hCcard, hcase⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r Sfull
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  let U : Finset (Fin n) := L ∪ C
  have hfixed :
      PrimitiveMiddleExactMersenneFixedPresentationData
        g y B leaf p S T Sfull k₀ w :=
    ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
      hrows, hcomplete, hwindow⟩
  refine ⟨p, S, T, Sfull, k₀, w, hfixed, ?_⟩
  change
    ((∃ missing : Fin d,
        (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
        leaf missing = r ∧
        C = L ∧ Sfull = L.erase r ∧ Sfull.card + 1 = d ∧
        w = -2 ∧
        (∀ i, addOrderOf (g (leaf i) - base) = q) ∧
        2 ^ (L.card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ L,
          g b - g c ∈ AddSubgroup.zmultiples y) ∧
        L.card + 4 ≤ B.card ∧
        5 ≤ (B \ L).card ∧
        (∀ b ∈ B \ L, ∀ c ∈ L,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        PrimitiveSaturatedSecondaryResidueCapacity g y B L p k₀ ∧
        48 * L.card.choose (L.card / 2) < 2 ^ B.card) ∨
      ((∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        (∀ i j : ℕ,
          d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
        388960 * d.choose (d / 2) < 2 ^ B.card))
  rcases hcase with hmerged | hdistinct
  · rcases hmerged with
      ⟨hUeq, hw, hUcap, hUcoset, hUgap, hfive, hseparated,
        hsecondary, hcritical⟩
    have hsaturation :=
      primitiveMiddle_merged_leafSaturation_of_fixedPresentation
        g y B leaf hleaf p Sfull k₀ hSsub hmiddle hcomplete
          hleafIncidence (by simpa only [r, C, L, U] using hUeq)
          (by simpa only [r, C, L, U] using hUcoset)
    rcases hsaturation with
      ⟨missing, hpunctured, hmissing, hCeq, hSeq, hcard⟩
    have hleafOrder : ∀ i,
        addOrderOf (g (leaf i) - base) = q := by
      intro i
      exact (addOrderOf_eq_of_isCycle_doubling_span
        R hRcycle hRne (fun j : Fin d ↦ g (leaf j) - base)
          hdouble y hspan i).trans horder
    rw [hUeq] at hUcap hUcoset hUgap hfive hseparated hsecondary hcritical
    exact Or.inl ⟨missing, hpunctured, hmissing, hCeq, hSeq, hcard,
      hw, hleafOrder, hUcap, hUcoset, hUgap, hfive, hseparated,
      hsecondary, hcritical⟩
  · exact Or.inr hdistinct

end MinModulus
