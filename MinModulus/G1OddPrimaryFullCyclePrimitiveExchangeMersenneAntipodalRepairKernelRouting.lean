/-
# Routing antipodal repair residuals through the cyclic-kernel transversal

The repair residual is displayed at a negative natural multiple of the
Mersenne leaf generator `v`, whereas the existing quotient descent is phrased
for nonzero integer multiples of the original kernel generator `y`.  Equality
of the two generated subgroups supplies the exact scalar conversion.  The
minimal transversal then forces each residual to hit a deleted pointed leaf
different from both the root and its selected owner.  This is the chargeable
family-level output needed after cancellation rigidity.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairCancellation

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A nonzero negative natural multiple of `v` is a nonzero integer multiple
of any generator `y` of the same cyclic subgroup. -/
theorem exists_yKernelScalar_of_neg_nsmul
    (y v : G) (hcyclic : AddSubgroup.zmultiples v =
      AddSubgroup.zmultiples y)
    (k : ℕ) (hne : -(k • v) ≠ 0) :
    ∃ z : ℤ, z • y = -(k • v) ∧ z • y ≠ 0 := by
  have hmem : -(k • v) ∈ AddSubgroup.zmultiples y := by
    rw [← hcyclic]
    exact AddSubgroup.neg_mem _
      (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples v) k)
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨z, hz, hz.symm ▸ hne⟩

/-- Convert a Mersenne residual witness to the exact nonzero `y`-kernel form
consumed by the transversal and quotient-descent APIs. -/
theorem mersenneResidualWitness_exists_yKernelWitness
    {n : ℕ} (g : Fin n → G) (y v : G)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (k : ℕ) (c : Fin n → ℤ)
    (hc : Witness g (-(k • v)) c) (hne : -(k • v) ≠ 0) :
    ∃ z : ℤ, z • y ≠ 0 ∧ Witness g (z • y) c := by
  obtain ⟨z, hz, hzne⟩ :=
    exists_yKernelScalar_of_neg_nsmul y v hcyclic k hne
  refine ⟨z, hzne, ?_⟩
  rw [hz]
  exact hc

/-- The cyclic-kernel support transversal hits every converted Mersenne
residual. -/
theorem CyclicKernelSupportTransversal.exists_hit_of_mersenneResidualWitness
    {n : ℕ} (g : Fin n → G) (y v : G) (B : Finset (Fin n))
    (htrans : CyclicKernelSupportTransversal g y B)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (k : ℕ) (c : Fin n → ℤ)
    (hc : Witness g (-(k • v)) c) (hne : -(k • v) ≠ 0) :
    ∃ j : Fin n, j ∈ B ∧ c j ≠ 0 := by
  obtain ⟨z, hzne, hc'⟩ :=
    mersenneResidualWitness_exists_yKernelWitness
      g y v hcyclic k c hc hne
  exact htrans z hzne c hc'

/-- If a residual is supported on a pointed leaf and vanishes at its root and
selected owner, its transversal hit is another deleted leaf position. -/
theorem CyclicKernelSupportTransversal.exists_other_pointedLeaf_of_mersenneResidualWitness
    {n d : ℕ} (g : Fin n → G) (y v : G) (B : Finset (Fin n))
    (htrans : CyclicKernelSupportTransversal g y B)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (hr : f z = r)
    (m : Fin d) (k : ℕ) (c : Fin n → ℤ)
    (hc : Witness g (-(k • v)) c) (hne : -(k • v) ≠ 0)
    (hroot : c r = 0) (howner : c (f m) = 0)
    (hoff : ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image f →
      c j = 0) :
    ∃ i : Fin d, i ≠ z ∧ i ≠ m ∧ f i ∈ B ∧ c (f i) ≠ 0 := by
  classical
  obtain ⟨j, hjB, hjne⟩ := htrans.exists_hit_of_mersenneResidualWitness
    g y v B hcyclic k c hc hne
  have hjLeaf : j ∈ (Finset.univ : Finset (Fin d)).image f := by
    by_contra hjLeaf
    exact hjne (hoff j hjLeaf)
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_image.mp hjLeaf
  have hiz : i ≠ z := by
    intro hiz
    subst i
    exact hjne (by rw [← hfi, hr, hroot])
  have him : i ≠ m := by
    intro him
    subst i
    exact hjne (by rw [← hfi, howner])
  exact ⟨i, hiz, him, hfi ▸ hjB, hfi ▸ hjne⟩

/-- Family-level routing theorem.  Either a scalar-determined singleton
cancellation occurs, or every member of `M` yields a distinct-from-root-and-
owner deleted-leaf hit after conversion to the original cyclic kernel. -/
theorem CyclicKernelSupportTransversal.singletonCancellation_or_all_other_pointedLeaf
    {n d : ℕ} (g : Fin n → G) (y v : G) (B : Finset (Fin n))
    (htrans : CyclicKernelSupportTransversal g y B)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (hd : 0 < d) (s : ℕ) (hs0 : 0 < s)
    (A M : Finset (Fin d))
    (harithmetic :
      binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) = binarySubsetValue M + s)
    (f : Fin d → Fin n) (r : Fin n) (hr : f ⟨0, hd⟩ = r)
    (Cancel : Fin d → Prop) (coeff : Fin d → Fin n → ℤ)
    (houtcome : ∀ m, m ∈ M →
      ((Cancel m ∧ A = {⟨0, hd⟩} ∧ M = {m}) ∨
        (Witness g (-((a m.val + s) • v)) (coeff m) ∧
          -((a m.val + s) • v) ≠ 0 ∧
          coeff m r = 0 ∧ coeff m (f m) = 0 ∧
          ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image f →
            coeff m j = 0))) :
    (∃ m, m ∈ M ∧ Cancel m ∧ A = {⟨0, hd⟩} ∧ M = {m} ∧
        2 ^ m.val + s = 2 ^ d ∧ s = 2 ^ d - 2 ^ m.val) ∨
      ∀ m, m ∈ M → ∃ i : Fin d,
        i ≠ ⟨0, hd⟩ ∧ i ≠ m ∧ f i ∈ B ∧ coeff m (f i) ≠ 0 := by
  let Residual : Fin d → Prop := fun m ↦
    Witness g (-((a m.val + s) • v)) (coeff m) ∧
      -((a m.val + s) • v) ≠ 0 ∧
      coeff m r = 0 ∧ coeff m (f m) = 0 ∧
      ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image f →
        coeff m j = 0
  have hfamily := singletonCancellation_or_all_residual
    hd s hs0 A M harithmetic Cancel Residual houtcome
  rcases hfamily with hcancel | hall
  · exact Or.inl hcancel
  · right
    intro m hmM
    rcases hall m hmM with ⟨hc, hne, hroot, howner, hoff⟩
    exact htrans.exists_other_pointedLeaf_of_mersenneResidualWitness
      g y v B hcyclic f ⟨0, hd⟩ r hr m (a m.val + s) (coeff m)
        hc hne hroot howner hoff

end MinModulus
