/-
# Three-residue capacity with the full primary leaf-owner union

The exhaustive deleted-owner partition initially bounds layers from the
primary owner fiber `S`, the secondary fiber `T`, and the final fiber `F`.
In the merged leaf/owner arm, however, the larger set `U` lies in the same
odd-kernel coset as `S` and contains the complete leaf range.  Exact primary
saturation proves that no coordinate of `F` can lie in `U`.  Hence the full
triple-layer injection applies to `U`, `T`, and `F`, placing leaf-cycle size
and residue-class size in one capacity inequality.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeThreeResidueCapacity

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The complete primary union can replace its deleted-owner subfiber in all
three-class layer bounds.  The final-class hypothesis is deliberately only an
exact coset equation; its canonical row data remains available in the calling
partition package but is not needed by this set-free injection. -/
theorem primaryUnion_threeResidue_fullLayerCapacity
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B U S T F : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hUnonempty : U.Nonempty)
    (hUcoset : ∀ b ∈ U, ∀ c ∈ U,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hrU : primitiveMiddleInsertedCoordinate p k₀ ∈ U)
    (hScomplete : ∀ b : ↥B,
      ((b : Fin n) ∈ S ↔
        g (b : Fin n) - g (primitiveMiddleInsertedCoordinate p k₀) ∈
          AddSubgroup.zmultiples y))
    (t : Fin n) (htT : t ∈ T)
    (hTsub : T ⊆ B \ U)
    (hTcomplete : ∀ b : ↥B,
      ((b : Fin n) ∈ T ↔
        g (b : Fin n) - g t ∈ AddSubgroup.zmultiples y))
    (hUTcap : ∀ i j : ℕ,
      U.card.choose i * T.card.choose j ≤ q)
    (hFsub : F ⊆ B \ (S ∪ T))
    (hFcase : F = ∅ ∨
      ∃ f : Fin n, f ∈ F ∧
        ∀ b : ↥B,
          ((b : Fin n) ∈ F ↔
            g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y)) :
    ∀ i j k : ℕ,
      U.card.choose i * T.card.choose j * F.card.choose k ≤ q := by
  classical
  have hTnonempty : T.Nonempty := ⟨t, htT⟩
  have hUTdisjoint : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro b hbU hbT
    exact (Finset.mem_sdiff.mp (hTsub hbT)).2 hbU
  have hUFdisjoint : Disjoint U F := by
    rw [Finset.disjoint_left]
    intro b hbU hbF
    have hbB := (Finset.mem_sdiff.mp (hFsub hbF)).1
    have hparallel := hUcoset b hbU
      (primitiveMiddleInsertedCoordinate p k₀) hrU
    have hbS := (hScomplete ⟨b, hbB⟩).2 hparallel
    exact (Finset.mem_sdiff.mp (hFsub hbF)).2
      (Finset.mem_union_left T hbS)
  have hTFdisjoint : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro b hbT hbF
    exact (Finset.mem_sdiff.mp (hFsub hbF)).2
      (Finset.mem_union_right S hbT)
  have hTcoset : ∀ b ∈ T, ∀ c ∈ T,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbT c hcT
    have hbB := (Finset.mem_sdiff.mp (hTsub hbT)).1
    have hcB := (Finset.mem_sdiff.mp (hTsub hcT)).1
    have hbParallel := (hTcomplete ⟨b, hbB⟩).1 hbT
    have hcParallel := (hTcomplete ⟨c, hcB⟩).1 hcT
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
    convert hsub using 1
    module
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  intro i j k
  rcases hFcase with hFempty | ⟨f, hfF, hFcomplete⟩
  · subst F
    cases k with
    | zero => simpa using hUTcap i j
    | succ k => simp
  · have hFnonempty : F.Nonempty := ⟨f, hfF⟩
    have hFcoset : ∀ b ∈ F, ∀ c ∈ F,
        g b - g c ∈ AddSubgroup.zmultiples y := by
      intro b hbF c hcF
      have hbB := (Finset.mem_sdiff.mp (hFsub hbF)).1
      have hcB := (Finset.mem_sdiff.mp (hFsub hcF)).1
      have hbParallel := (hFcomplete ⟨b, hbB⟩).1 hbF
      have hcParallel := (hFcomplete ⟨c, hcB⟩).1 hcF
      have hsub :=
        (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
      convert hsub using 1
      module
    have h :=
      choose_mul_choose_mul_choose_le_addOrderOf_of_three_kernelCosets
        g hg y U T F hUnonempty hTnonempty hFnonempty
          hUTdisjoint hUFdisjoint hTFdisjoint hUcoset hTcoset hFcoset
            i j k
    simpa only [horder] using h

/-- Direct quantitative endpoint extracted from the exhaustive partition:
the same secondary and final fibers partition `B`, every `U`-`T`-`F` layer
product is bounded by `q`, and exact criticality yields the central residual
with the whole leaf-owner union `U`. -/
theorem PrimitiveThreeResidueCapacityPartition.exists_primaryUnionCriticalBound
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B U S : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hUnonempty : U.Nonempty)
    (hUcoset : ∀ b ∈ U, ∀ c ∈ U,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hrU : primitiveMiddleInsertedCoordinate p k₀ ∈ U)
    (hScomplete : ∀ b : ↥B,
      ((b : Fin n) ∈ S ↔
        g (b : Fin n) - g (primitiveMiddleInsertedCoordinate p k₀) ∈
          AddSubgroup.zmultiples y))
    (hthree : PrimitiveThreeResidueCapacityPartition g y B U S p k₀) :
    ∃ T F : Finset (Fin n),
      3 ≤ T.card ∧
      B = (S ∪ T) ∪ F ∧
      F ⊆ B \ (S ∪ T) ∧
      (∀ i j k : ℕ,
        U.card.choose i * T.card.choose j * F.card.choose k ≤ q) ∧
      48 * (U.card.choose (U.card / 2) * F.card.choose (F.card / 2)) <
        2 ^ B.card := by
  classical
  rcases hthree with
    ⟨T, k₁, t, hTcard, hTsub, htT, _hk₁Mem, _hk₁Ne, _hTrows,
      hTcomplete, _hTseparated, hUTcap, hfinal⟩
  rcases hfinal with ⟨F, hpartition, hFsub, hFcase⟩
  have hFsimple : F = ∅ ∨
      ∃ f : Fin n, f ∈ F ∧
        ∀ b : ↥B,
          ((b : Fin n) ∈ F ↔
            g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y) := by
    rcases hFcase with hFempty | hFfull
    · exact Or.inl hFempty
    · rcases hFfull with
        ⟨_k₂, f, hfF, _hk₂Mem, _hk₂Ne₀, _hk₂Ne₁, _hFrows, hFcomplete⟩
      exact Or.inr ⟨f, hfF, hFcomplete⟩
  have hcap := primaryUnion_threeResidue_fullLayerCapacity
    g hg y B U S T F p k₀ hyq hfullOdd hUnonempty hUcoset hrU
      hScomplete t htT hTsub hTcomplete hUTcap hFsub hFsimple
  exact ⟨T, F, hTcard, hpartition, hFsub, hcap,
    fortyEight_mul_primaryFinalCentralChoose_lt_two_pow_transversalCard
      B U T F hretained hcritical hTcard hcap⟩

end MinModulus
