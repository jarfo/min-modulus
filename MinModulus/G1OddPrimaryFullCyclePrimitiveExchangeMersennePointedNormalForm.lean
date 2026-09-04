/-
# Pointed super-increasing normal form of the exact Mersenne cycle

A fixed-point-free full cycle can be enumerated from any chosen root by its
successive iterates.  When the cycle acts by doubling, this enumeration has
values `2^k` times the root displacement.  Subtracting the root therefore
turns the cycle into the literal super-increasing family

    2^k - 1,  0 <= k < d.

For the dimension-locked exact-Mersenne residual, choose the unique missing
leaf as root.  The entire primary leaf class is then, up to translation and
multiplication by a full-order element, exactly the canonical endpoint tuple
from `UniqueSums.lean`.  This is a structural normal form, not merely a
cardinality comparison.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneDimensionLock

namespace MinModulus

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Enumerate a fixed-point-free full cycle from any chosen root. -/
noncomputable def fullCycleOrbitEquiv
    {d : ℕ} (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (root : Fin d) : Fin d ≃ Fin d := by
  let orbit : Fin d → Fin d := fun k ↦ R^[k.val] root
  have hsupport : R.support = Finset.univ := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact hRne i
  have horder : orderOf R = d := by
    rw [hcycle.orderOf, hsupport]
    simp
  have hsurj : Function.Surjective orbit := by
    intro i
    have hsame := hcycle.sameCycle (hRne root) (hRne i)
    obtain ⟨k, hklt, hk⟩ := hsame.exists_pow_eq'
    refine ⟨⟨k, by simpa only [horder] using hklt⟩, ?_⟩
    simpa only [orbit, Equiv.Perm.iterate_eq_pow] using hk
  exact Equiv.ofBijective orbit
    ⟨(Finite.injective_iff_surjective).2 hsurj, hsurj⟩

@[simp]
theorem fullCycleOrbitEquiv_apply
    {d : ℕ} (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (root k : Fin d) :
    fullCycleOrbitEquiv R hcycle hRne root k = R^[k.val] root := by
  rfl

/-- Under a doubling recurrence, the pointed full-cycle enumeration is the
literal sequence of powers of two. -/
theorem fullCycleOrbitEquiv_doubling_eq_pow_two
    {d : ℕ} (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (root : Fin d)
    (disp : Fin d → G) (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (k : Fin d) :
    disp (fullCycleOrbitEquiv R hcycle hRne root k) =
      (2 ^ k.val) • disp root := by
  rw [fullCycleOrbitEquiv_apply]
  exact apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
    R disp hdouble k.val root

/-- Pointing a doubling cycle at one leaf turns every relative displacement
into the super-increasing coefficient `2^k-1`. -/
theorem fullCycleOrbitEquiv_sub_eq_superincreasing
    {d : ℕ} (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (root : Fin d)
    (disp : Fin d → G) (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (k : Fin d) :
    disp (fullCycleOrbitEquiv R hcycle hRne root k) - disp root =
      a k.val • disp root := by
  rw [fullCycleOrbitEquiv_doubling_eq_pow_two
    R hcycle hRne root disp hdouble]
  simp only [a]
  have hone : 1 ≤ 2 ^ k.val := Nat.one_le_two_pow
  have hsplit : (2 ^ k.val) • disp root =
      (2 ^ k.val - 1) • disp root + disp root := by
    have hcoeff := congrArg (fun z : ℕ ↦ z • disp root)
      (Nat.sub_add_cancel hone).symm
    simpa only [add_nsmul, one_nsmul] using hcoeff
  rw [hsplit]
  abel

/-- Affine leaf form: a full doubling leaf cycle, pointed at any chosen leaf,
is exactly the canonical super-increasing Mersenne tuple up to translation
and multiplication by its root displacement. -/
theorem fullCycleLeaf_eq_point_add_superincreasing
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (root : Fin d)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (k : Fin d) :
    g (leaf (fullCycleOrbitEquiv R hcycle hRne root k)) =
      g (leaf root) + a k.val • (g (leaf root) - base) := by
  have hsub := fullCycleOrbitEquiv_sub_eq_superincreasing
    R hcycle hRne root (fun i ↦ g (leaf i) - base) hdouble k
  have hrelative :
      (g (leaf (fullCycleOrbitEquiv R hcycle hRne root k)) - base) -
          (g (leaf root) - base) =
        g (leaf (fullCycleOrbitEquiv R hcycle hRne root k)) -
          g (leaf root) := by abel
  rw [hrelative] at hsub
  calc
    g (leaf (fullCycleOrbitEquiv R hcycle hRne root k)) =
        (g (leaf (fullCycleOrbitEquiv R hcycle hRne root k)) -
          g (leaf root)) + g (leaf root) :=
      (sub_add_cancel _ _).symm
    _ = a k.val • (g (leaf root) - base) + g (leaf root) := by rw [hsub]
    _ = g (leaf root) + a k.val • (g (leaf root) - base) := add_comm _ _

/-- The pointed affine normal form attached to the same canonical
presentation as the dimension-locked residual. -/
def PrimitiveMiddleExactMersennePointedNormalForm
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  ∃ hd : 0 < d, ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ k₀ : ℤ, ∃ root : Fin d, ∃ e : Fin d ≃ Fin d,
      leaf root = primitiveMiddleInsertedCoordinate p k₀ ∧
      e ⟨0, hd⟩ = root ∧
      addOrderOf (g (leaf root) - base) = q ∧
      ∀ k : Fin d,
        g (leaf (e k)) =
          g (leaf root) + a k.val • (g (leaf root) - base)

/-- Lossless enrichment of the dimension-locked survivor by its pointed
super-increasing normal form. -/
def PrimitiveMiddleExactMersennePointedResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  PrimitiveMiddleExactMersenneDimensionLockedResidual
      g y B leaf base ∧
    PrimitiveMiddleExactMersennePointedNormalForm
      g y B leaf base

/-- The unique missing leaf is a canonical root for the full cycle.  In its
orbit order the entire leaf range is the standard super-increasing
Mersenne tuple. -/
theorem PrimitiveMiddleExactMersenneDimensionLockedResidual.toPointedResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hresidual :
      PrimitiveMiddleExactMersenneDimensionLockedResidual
        g y B leaf base) :
    PrimitiveMiddleExactMersennePointedResidual
      g y B leaf base := by
  classical
  refine ⟨hresidual, ?_⟩
  rcases hresidual with
    ⟨p, S, T, Sfull, k₀, w, hfixed, missing, hpunctured,
      hmissing, hCeq, hSeq, hcard, hw, hleafOrder, hLcap,
      hLcoset, hLgap, hfive, hseparated, hsecondary,
      hcriticalBound, hn, hBcard, hexternal, hdLower, hdUpper⟩
  let e : Fin d ≃ Fin d :=
    fullCycleOrbitEquiv R hcycle hRne missing
  have hd : 0 < d := by omega
  refine ⟨hd, p, k₀, missing, e, hmissing, ?_, hleafOrder missing, ?_⟩
  · simp only [e, fullCycleOrbitEquiv_apply]
    rfl
  · intro k
    exact fullCycleLeaf_eq_point_add_superincreasing
      g leaf R hcycle hRne missing base hdouble k

end MinModulus
