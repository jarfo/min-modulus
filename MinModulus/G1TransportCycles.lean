/-
# Shift-labelled affine transport cycles

The excluded restoration face from `G1PairedRestorationTransport` is not
merely equinumerous with its target face: it is an exact translate by a
target-specific group element.  This module retains those labels under
composition.

A finite path has a sharp dichotomy.  Either its final translate contains a
value outside the starting face, or the path closes; in the latter case the
additive order of the total shift divides the face cardinality.  Restoration
faces have power-of-two cardinality, so a closed G1 transport cycle forces a
2-primary total shift.  This is the valid algebraic consequence of a cycle;
shift telescoping alone does not yet give a forbidden zero-target witness.
-/
import MinModulus.G1PairedRestorationTransport
import Mathlib.GroupTheory.GroupAction.Quotient

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translate a finite value set by a fixed additive shift. -/
def translateValueFinset (A : Finset G) (δ : G) : Finset G :=
  A.image (fun x ↦ δ + x)

@[simp]
theorem translateValueFinset_zero (A : Finset G) :
    translateValueFinset A 0 = A := by
  simp [translateValueFinset]

theorem translateValueFinset_comp (A : Finset G) (δ ε : G) :
    translateValueFinset (translateValueFinset A δ) ε =
      translateValueFinset A (δ + ε) := by
  ext x
  simp only [translateValueFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by abel⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨δ + z, ⟨z, hz, rfl⟩, by abel⟩

theorem translateValueFinset_card (A : Finset G) (δ : G) :
    (translateValueFinset A δ).card = A.card := by
  rw [translateValueFinset, Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

/-- Iteratively translate a finite value set by a list of edge labels. -/
def translateValuePath (A : Finset G) : List G → Finset G
  | [] => A
  | δ :: shifts => translateValuePath (translateValueFinset A δ) shifts

/-- A path of translations is the single translation by the sum of its
labels. -/
theorem translateValuePath_eq_translate_sum (A : Finset G) (shifts : List G) :
    translateValuePath A shifts = translateValueFinset A shifts.sum := by
  induction shifts generalizing A with
  | nil => simp [translateValuePath]
  | cons δ shifts ih =>
      simp only [translateValuePath, ih, List.sum_cons]
      exact translateValueFinset_comp A δ shifts.sum

/-- A shift-labelled equality between two finite value faces. -/
structure FinsetAffineTransport (G : Type*) [AddCommGroup G] [DecidableEq G] where
  source : Finset G
  target : Finset G
  shift : G
  transport_eq : translateValueFinset source shift = target

namespace FinsetAffineTransport

/-- The identity affine transport. -/
def refl (A : Finset G) : FinsetAffineTransport G where
  source := A
  target := A
  shift := 0
  transport_eq := translateValueFinset_zero A

/-- Compose two affine transports whose intermediate faces agree. -/
def comp (e f : FinsetAffineTransport G) (hmatch : e.target = f.source) :
    FinsetAffineTransport G where
  source := e.source
  target := f.target
  shift := e.shift + f.shift
  transport_eq := by
    rw [← translateValueFinset_comp, e.transport_eq, hmatch, f.transport_eq]

@[simp] theorem source_comp (e f : FinsetAffineTransport G)
    (hmatch : e.target = f.source) :
    (e.comp f hmatch).source = e.source := rfl

@[simp] theorem target_comp (e f : FinsetAffineTransport G)
    (hmatch : e.target = f.source) :
    (e.comp f hmatch).target = f.target := rfl

@[simp] theorem shift_comp (e f : FinsetAffineTransport G)
    (hmatch : e.target = f.source) :
    (e.comp f hmatch).shift = e.shift + f.shift := rfl

end FinsetAffineTransport

theorem translateValueFinset_neg_eq_self_of_eq_self
    (A : Finset G) (δ : G)
    (hδ : translateValueFinset A δ = A) :
    translateValueFinset A (-δ) = A := by
  calc
    translateValueFinset A (-δ) =
        translateValueFinset (translateValueFinset A δ) (-δ) := by rw [hδ]
    _ = translateValueFinset A (δ + -δ) :=
      translateValueFinset_comp A δ (-δ)
    _ = A := by simp

theorem translateValueFinset_zsmul_eq_self_of_eq_self
    (A : Finset G) (δ : G)
    (hδ : translateValueFinset A δ = A) (z : ℤ) :
    translateValueFinset A (z • δ) = A := by
  have hneg := translateValueFinset_neg_eq_self_of_eq_self A δ hδ
  refine Int.induction_on z ?_ ?_ ?_
  · simp
  · intro i hi
    calc
      translateValueFinset A (((i : ℤ) + 1) • δ) =
          translateValueFinset A ((i : ℤ) • δ + δ) := by
            congr 1
            rw [add_zsmul]
            simp
      _ = translateValueFinset (translateValueFinset A ((i : ℤ) • δ)) δ :=
        (translateValueFinset_comp A ((i : ℤ) • δ) δ).symm
      _ = translateValueFinset A δ := by rw [hi]
      _ = A := hδ
  · intro i hi
    calc
      translateValueFinset A (((-(i : ℤ) - 1)) • δ) =
          translateValueFinset A ((-(i : ℤ)) • δ + -δ) := by
            congr 1
            rw [sub_zsmul]
            simp
      _ = translateValueFinset
          (translateValueFinset A ((-(i : ℤ)) • δ)) (-δ) :=
        (translateValueFinset_comp A ((-(i : ℤ)) • δ) (-δ)).symm
      _ = translateValueFinset A (-δ) := by rw [hi]
      _ = A := hneg

theorem addOrderOf_dvd_card_of_translateValueFinset_eq_self
    [Fintype G] (A : Finset G) (δ : G)
    (hδ : translateValueFinset A δ = A) :
    addOrderOf δ ∣ A.card := by
  let H := AddSubgroup.zmultiples δ
  let X : SubAddAction H G :=
    { carrier := (A : Set G)
      vadd_mem' := by
        intro c x hx
        change (c : G) + x ∈ A
        obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp c.property
        have hxImage : z • δ + x ∈ translateValueFinset A (z • δ) := by
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        rw [translateValueFinset_zsmul_eq_self_of_eq_self A δ hδ z] at hxImage
        simpa [H, hz] using hxImage }
  letI : Fintype X := Fintype.ofFinite X
  let Q := Quotient (AddAction.orbitRel H X)
  letI : Fintype Q := Fintype.ofFinite Q
  let e : X ≃ Q × H :=
    AddAction.selfEquivOrbitsQuotientProd
      (fun b : X ↦ IsCancelVAdd.stabilizer_eq_bot b)
  have hcard := Fintype.card_congr e
  let eXA : X ≃ {x // x ∈ A} :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hXcard : Fintype.card X = A.card := by
    calc
      Fintype.card X = Fintype.card {x // x ∈ A} := Fintype.card_congr eXA
      _ = A.card := Fintype.card_coe A
  have hHcard : Fintype.card H = addOrderOf δ := by
    simpa only [H] using (Fintype.card_zmultiples (G := G) (x := δ))
  rw [hXcard] at hcard
  refine ⟨Fintype.card Q, ?_⟩
  simpa only [Fintype.card_prod, hHcard, Nat.mul_comm] using hcard

theorem card_nsmul_eq_zero_of_translateValueFinset_eq_self
    [Fintype G] (A : Finset G) (δ : G)
    (hδ : translateValueFinset A δ = A) :
    A.card • δ = 0 := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact addOrderOf_dvd_card_of_translateValueFinset_eq_self A δ hδ

namespace FinsetAffineTransport

/-- On a closed affine transport, the order of the total shift divides the
cardinality of the transported face. -/
theorem addOrderOf_shift_dvd_source_card [Fintype G]
    (e : FinsetAffineTransport G) (hcycle : e.target = e.source) :
    addOrderOf e.shift ∣ e.source.card := by
  exact addOrderOf_dvd_card_of_translateValueFinset_eq_self
    e.source e.shift (e.transport_eq.trans hcycle)

/-- Equivalently, the source-face cardinality annihilates the total shift of
a closed affine transport. -/
theorem source_card_nsmul_shift_eq_zero [Fintype G]
    (e : FinsetAffineTransport G) (hcycle : e.target = e.source) :
    e.source.card • e.shift = 0 := by
  exact card_nsmul_eq_zero_of_translateValueFinset_eq_self
    e.source e.shift (e.transport_eq.trans hcycle)

end FinsetAffineTransport

/-- A finite shift path either leaves the starting face or closes with its
total shift annihilated by the face cardinality. -/
theorem translateValuePath_exists_escape_or_card_nsmul_sum_eq_zero
    [Fintype G] (A : Finset G) (shifts : List G) :
    (∃ x, x ∈ translateValuePath A shifts ∧ x ∉ A) ∨
      A.card • shifts.sum = 0 := by
  by_cases hcycle : translateValuePath A shifts = A
  · right
    apply card_nsmul_eq_zero_of_translateValueFinset_eq_self A shifts.sum
    rw [← translateValuePath_eq_translate_sum]
    exact hcycle
  · left
    have hcard : (translateValuePath A shifts).card = A.card := by
      rw [translateValuePath_eq_translate_sum,
        translateValueFinset_card]
    have hnotSubset : ¬translateValuePath A shifts ⊆ A := by
      intro hsubset
      apply hcycle
      exact Finset.eq_of_subset_of_card_le hsubset hcard.ge
    exact Finset.not_subset.mp hnotSubset

section RestorationTransport

variable {m : ℕ}

/-- The positive collision displacement carried by a restoration edge.  The
actual excluded-to-transported face map uses its negative. -/
noncomputable def restorationFanCollisionShift
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : G :=
  h + ssum g
    (q.val.2 ∩ reducedCollisionRestorationFanSupport r q)

/-- The translated excluded value slice is precisely ordinary finset
translation by the negative restoration collision shift. -/
theorem restorationFanForcedExcludedTranslatedValueSlice_eq_translateValueFinset
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) :
    restorationFanForcedExcludedTranslatedValueSlice r q j =
      translateValueFinset
        (restorationFanForcedExcludedValueSlice r q j)
        (-restorationFanCollisionShift r q) := by
  rw [restorationFanForcedExcludedTranslatedValueSlice,
    translateValueFinset]
  apply Finset.image_congr
  intro x hx
  simp only [restorationFanCollisionShift]
  abel

/-- Package the live singleton-positive restoration theorem as one
shift-labelled affine edge from the excluded face to its intrinsic target
face. -/
noncomputable def restorationFanAffineTransport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    FinsetAffineTransport G where
  source := restorationFanForcedExcludedValueSlice r q j
  target := restorationFanExcludedTransportValueSlice q j
  shift := -restorationFanCollisionShift r q
  transport_eq := by
    rw [← restorationFanForcedExcludedTranslatedValueSlice_eq_translateValueFinset]
    exact restorationFanForcedExcludedTranslatedValueSlice_eq_transport
      r q hcard hdrop j k hAcard hB hjq hkq hAq

@[simp]
theorem restorationFanAffineTransport_shift
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    (restorationFanAffineTransport r q hcard hdrop j k hAcard hB hjq hkq hAq).shift =
      -restorationFanCollisionShift r q := rfl

/-- The excluded restoration face has an explicit power-of-two cardinality,
one exponent below the target's native padding weight. -/
theorem card_restorationFanForcedExcludedValueSlice_eq_pow
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    (restorationFanForcedExcludedValueSlice r q j).card =
      2 ^ (m - (reducedCollisionSupport q).card - 1) := by
  have htwo := two_mul_card_restorationFanForcedExcludedValueSlice
    hg r q hcard hdrop j k hAcard hB hjq hkq hAq
  have hle : (reducedCollisionSupport q).card + 1 ≤ m := by
    have hinsert := Finset.card_insert_of_notMem hjq
    have hcardUniv := Finset.card_le_univ
      (insert j (reducedCollisionSupport q))
    rw [hinsert] at hcardUniv
    simpa using hcardUniv
  have hexp : m - (reducedCollisionSupport q).card =
      (m - (reducedCollisionSupport q).card - 1) + 1 := by
    omega
  change 2 * (restorationFanForcedExcludedValueSlice r q j).card =
    2 ^ (m - (reducedCollisionSupport q).card) at htwo
  rw [hexp, pow_succ] at htwo
  omega

/-- A closed composite transport based at a live restoration face has
2-primary total shift: its additive order divides the explicit face power. -/
theorem restorationFanTransportCycle_addOrderOf_shift_dvd_pow
    [Fintype G]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty)
    (e : FinsetAffineTransport G)
    (hsource : e.source = restorationFanForcedExcludedValueSlice r q j)
    (hcycle : e.target = e.source) :
    addOrderOf e.shift ∣
      2 ^ (m - (reducedCollisionSupport q).card - 1) := by
  have horder := e.addOrderOf_shift_dvd_source_card hcycle
  rw [hsource,
    card_restorationFanForcedExcludedValueSlice_eq_pow
      hg r q hcard hdrop j k hAcard hB hjq hkq hAq] at horder
  exact horder

/-- The equivalent explicit annihilation statement for a closed composite
restoration transport. -/
theorem restorationFanTransportCycle_pow_nsmul_shift_eq_zero
    [Fintype G]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty)
    (e : FinsetAffineTransport G)
    (hsource : e.source = restorationFanForcedExcludedValueSlice r q j)
    (hcycle : e.target = e.source) :
    2 ^ (m - (reducedCollisionSupport q).card - 1) • e.shift = 0 := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact restorationFanTransportCycle_addOrderOf_shift_dvd_pow
    hg r q hcard hdrop j k hAcard hB hjq hkq hAq e hsource hcycle

end RestorationTransport

end MinModulus
