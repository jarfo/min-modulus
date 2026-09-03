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
import Mathlib.GroupTheory.Perm.Cycle.Basic
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

/-- A nonempty finite family mapped into a finite label set has a genuinely
dominant fiber: the full family is at most the number of labels times that
fiber.  Unlike a threshold pigeonhole statement, this simultaneously controls
the complement of the selected fiber. -/
theorem finiteMap_exists_dominantFiber
    {α β : Type*} [Fintype α] [DecidableEq β]
    (R : Finset β) (f : α → β)
    (hf : ∀ a : α, f a ∈ R)
    (hsource : (Finset.univ : Finset α).Nonempty) :
    ∃ y ∈ R,
      let F := Finset.univ.filter (fun a : α ↦ f a = y)
      F.Nonempty ∧ Fintype.card α ≤ R.card * F.card := by
  classical
  let fiber : β → Finset α := fun y ↦
    Finset.univ.filter (fun a : α ↦ f a = y)
  obtain ⟨a, _ha⟩ := hsource
  have hR : R.Nonempty := ⟨f a, hf a⟩
  obtain ⟨y, hyR, hyMax⟩ :=
    R.exists_max_image (fun z ↦ (fiber z).card) hR
  have haFiber : 0 < (fiber (f a)).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, by simp [fiber]⟩
  have hyFiber : (fiber y).Nonempty := by
    apply Finset.card_pos.mp
    exact haFiber.trans_le (hyMax (f a) (hf a))
  refine ⟨y, hyR, by simpa [fiber] using hyFiber, ?_⟩
  rcases finiteMap_capacity_or_largeFiber R f hf (fiber y).card with
    hcap | ⟨z, hzR, hzLarge⟩
  · simpa [fiber] using hcap
  · exact ((Nat.not_lt_of_ge (hyMax z hzR)) hzLarge).elim

/-- Dominant selection through two finite label layers.  It returns the
actual nested fibers together with both multiplicative dominance bounds. -/
theorem finiteMap_exists_twoStageDominantFibers
    {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (R : Finset β) (Q : Finset γ)
    (label : α → β) (profile : α → γ)
    (hlabel : ∀ a, label a ∈ R) (hprofile : ∀ a, profile a ∈ Q)
    (hsource : (Finset.univ : Finset α).Nonempty) :
    ∃ y ∈ R,
      let F := Finset.univ.filter (fun a : α ↦ label a = y)
      F.Nonempty ∧ Fintype.card α ≤ R.card * F.card ∧
        ∃ z ∈ Q,
          let S := Finset.univ.filter (fun f : ↥F ↦ profile (f : α) = z)
          S.Nonempty ∧ F.card ≤ Q.card * S.card := by
  classical
  obtain ⟨y, hyR, hFnonempty, hFdominant⟩ :=
    finiteMap_exists_dominantFiber R label hlabel hsource
  let F := Finset.univ.filter (fun a : α ↦ label a = y)
  have hFuniv : (Finset.univ : Finset ↥F).Nonempty := by
    obtain ⟨a, haF⟩ := hFnonempty
    exact ⟨(⟨a, haF⟩ : ↥F), Finset.mem_univ _⟩
  obtain ⟨z, hzQ, hSnonempty, hSdominant⟩ :=
    finiteMap_exists_dominantFiber Q (fun f : ↥F ↦ profile (f : α))
      (fun f ↦ hprofile (f : α)) hFuniv
  refine ⟨y, hyR, by simpa [F] using hFnonempty,
    by simpa [F] using hFdominant, z, hzQ, ?_, ?_⟩
  · simpa [F] using hSnonempty
  · change F.card ≤ Q.card *
      (Finset.univ.filter (fun f : ↥F ↦ profile (f : α) = z)).card
    simpa only [Fintype.card_coe] using hSdominant

/-- With at most six outer labels and three inner profiles, dominance bounds
charge both discarded inner layers by at most seventeen copies of the final
selected family. -/
theorem card_twoStageFiberComplements_le_seventeen_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (S : Finset ↥F)
    (hFdominant : Fintype.card α ≤ 6 * F.card)
    (hSdominant : F.card ≤ 3 * S.card) :
    (Finset.univ \ F).card + (Finset.univ \ S).card ≤ 17 * S.card := by
  have hFle : F.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ F)
  have hSle : S.card ≤ F.card := by
    simpa [Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ S)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ F),
    Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp only [Finset.card_univ, Fintype.card_coe]
  omega

/-- The components of a permutation occupied by a finite indexed family.
The family may carry additional row data; only its owner map is used. -/
noncomputable def permutationFamilyComponents
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) :
    Finset (Quotient (Equiv.Perm.SameCycle.setoid R)) := by
  classical
  exact Finset.univ.image fun i ↦
    Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i)

/-- The members of a finite family whose owners lie in one fixed permutation
component. -/
noncomputable def permutationFamilyComponentFiber
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦
    Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C

/-- The components occupied by a selected subset of the permutation carrier. -/
noncomputable def permutationSubsetComponents
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (A : Finset α) :
    Finset (Quotient (Equiv.Perm.SameCycle.setoid R)) := by
  classical
  exact A.image fun a ↦
    Quotient.mk (Equiv.Perm.SameCycle.setoid R) a

/-- Occupied components whose every vertex belongs to the selected subset. -/
noncomputable def permutationSubsetFullComponents
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (A : Finset α) :
    Finset (Quotient (Equiv.Perm.SameCycle.setoid R)) := by
  classical
  exact (permutationSubsetComponents R A).filter fun C ↦
    ∀ x : α,
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) x = C → x ∈ A

/-- Selected vertices whose successor leaves the selected subset. -/
noncomputable def permutationSubsetBoundary
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (A : Finset α) :
    Finset α := by
  classical
  exact A.filter fun x ↦ R x ∉ A

/-- Applying a permutation does not change its SameCycle quotient class. -/
theorem permutationSameCycleQuotient_apply_eq
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (x : α) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid R) (R x) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) x := by
  apply Quotient.sound
  exact ⟨-1, by simp⟩

/-- Every occupied component is either completely selected or contains a
selected vertex whose successor is unselected. -/
theorem mem_fullComponents_or_exists_mem_boundary
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (A : Finset α)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetComponents R A) :
    C ∈ permutationSubsetFullComponents R A ∨
      ∃ x ∈ permutationSubsetBoundary R A,
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) x = C := by
  classical
  obtain ⟨a, haA, haC⟩ := Finset.mem_image.mp hC
  by_cases hfull : ∀ x : α,
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) x = C → x ∈ A
  · left
    exact Finset.mem_filter.mpr ⟨hC, hfull⟩
  · right
    push Not at hfull
    obtain ⟨b, hbC, hbNotA⟩ := hfull
    have hsame : R.SameCycle a b := by
      change (Equiv.Perm.SameCycle.setoid R).r a b
      apply Quotient.exact
      exact haC.trans hbC.symm
    obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
    by_contra hboundary
    push Not at hboundary
    have hstep : ∀ x : α, x ∈ A →
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) x = C → R x ∈ A := by
      intro x hxA hxC
      by_contra hxNext
      have hxBoundary : x ∈ permutationSubsetBoundary R A :=
        Finset.mem_filter.mpr ⟨hxA, hxNext⟩
      exact (hboundary x hxBoundary) hxC
    have hiter : ∀ ell : ℕ,
        (R^[ell] a) ∈ A ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid R) (R^[ell] a) = C := by
      intro ell
      induction ell with
      | zero => simpa using And.intro haA haC
      | succ ell ih =>
          rw [Function.iterate_succ_apply']
          exact ⟨hstep _ ih.1 ih.2,
            (permutationSameCycleQuotient_apply_eq R _).trans ih.2⟩
    exact hbNotA (by rw [← hk]; exact (hiter k).1)

/-- Occupied components are paid for by full selected components plus
selected-to-unselected boundary vertices. -/
theorem card_permutationSubsetComponents_le_full_add_boundary
    {α : Type*} [Fintype α] (R : Equiv.Perm α) (A : Finset α) :
    (permutationSubsetComponents R A).card ≤
      (permutationSubsetFullComponents R A).card +
        (permutationSubsetBoundary R A).card := by
  classical
  let boundaryComponents :
      Finset (Quotient (Equiv.Perm.SameCycle.setoid R)) :=
    (permutationSubsetBoundary R A).image fun x ↦
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) x
  have hsubset : permutationSubsetComponents R A ⊆
      permutationSubsetFullComponents R A ∪ boundaryComponents := by
    intro C hC
    rcases mem_fullComponents_or_exists_mem_boundary R A C hC with
      hfull | ⟨x, hxBoundary, hxC⟩
    · exact Finset.mem_union_left _ hfull
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, hxBoundary, hxC⟩
  have hboundaryCard : boundaryComponents.card ≤
      (permutationSubsetBoundary R A).card := by
    exact Finset.card_image_le
  calc
    (permutationSubsetComponents R A).card ≤
        (permutationSubsetFullComponents R A ∪ boundaryComponents).card :=
      Finset.card_le_card hsubset
    _ ≤ (permutationSubsetFullComponents R A).card +
        boundaryComponents.card := Finset.card_union_le _ _
    _ ≤ (permutationSubsetFullComponents R A).card +
        (permutationSubsetBoundary R A).card :=
      Nat.add_le_add_left hboundaryCard _

/-- The selected owner set underlying an arbitrary finite family. -/
noncomputable def permutationFamilyOwnerSet
    {ι α : Type*} [Fintype ι] [Fintype α] (owner : ι → α) : Finset α := by
  classical
  exact Finset.univ.image owner

/-- Rows whose owner's permutation successor is not owned by the selected
family.  For an injective owner map these rows are in exact bijection with
the owner-set boundary. -/
noncomputable def permutationFamilyBoundaryRows
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦
    R (owner i) ∉ permutationFamilyOwnerSet owner

/-- The owners represented by boundary source rows. -/
noncomputable def permutationFamilyBoundaryOwnerSet
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) : Finset α := by
  classical
  exact (permutationFamilyBoundaryRows R owner).image owner

/-- Boundary owners are exactly the images of boundary source rows. -/
theorem permutationFamilyBoundaryOwnerSet_eq_boundary
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) :
    permutationFamilyBoundaryOwnerSet R owner =
      permutationSubsetBoundary R (permutationFamilyOwnerSet owner) := by
  classical
  unfold permutationFamilyBoundaryOwnerSet
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
        (Finset.mem_filter.mp hi).2⟩
  · intro hx
    obtain ⟨hxOwner, hxNext⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hxOwner
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    simpa [permutationFamilyBoundaryRows] using hxNext

/-- An injective owner map loses no multiplicity when boundary owners are
lifted back to their unique source rows. -/
theorem card_permutationFamilyBoundaryRows_eq_boundary
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner) :
    (permutationFamilyBoundaryRows R owner).card =
      (permutationSubsetBoundary R
        (permutationFamilyOwnerSet owner)).card := by
  classical
  rw [← permutationFamilyBoundaryOwnerSet_eq_boundary]
  exact (Finset.card_image_of_injective
    (permutationFamilyBoundaryRows R owner) howner).symm

/-- Each boundary owner of an injective family has one and only one
boundary source row. -/
theorem permutationFamilyBoundary_uniqueRow
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner)
    {x : α}
    (hx : x ∈ permutationSubsetBoundary R
      (permutationFamilyOwnerSet owner)) :
    ∃! i : ι, i ∈ permutationFamilyBoundaryRows R owner ∧ owner i = x := by
  classical
  have hxOwnerSet : x ∈ permutationFamilyBoundaryOwnerSet R owner := by
    rw [permutationFamilyBoundaryOwnerSet_eq_boundary]
    exact hx
  have hxImage : x ∈ (permutationFamilyBoundaryRows R owner).image owner := by
    exact hxOwnerSet
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxImage
  refine ⟨i, ⟨hi, hix⟩, ?_⟩
  intro j hj
  exact howner (hj.2.trans hix.symm)

/-- No selected row owns the successor of a boundary source row.  This is
the pointwise form consumed by nested first-failure classifications. -/
theorem permutationFamilyBoundaryRow_owner_ne_successor
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (s : ↥(permutationFamilyBoundaryRows R owner)) :
    ∀ f : ι, owner f ≠ R (owner (s : ι)) := by
  classical
  intro f hf
  have hsBoundary := (Finset.mem_filter.mp s.property).2
  apply hsBoundary
  unfold permutationFamilyOwnerSet
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ f, hf⟩

/-- A row in a full occupied component has a unique selected successor row.
The successor remains in the same permutation component. -/
theorem permutationFamilyFullComponent_uniqueSuccessorRow
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetFullComponents R
      (permutationFamilyOwnerSet owner))
    (i : ι)
    (hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C) :
    ∃! j : ι,
      owner j = R (owner i) ∧
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner j) = C := by
  classical
  have hnextC :
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) (R (owner i)) = C :=
    (permutationSameCycleQuotient_apply_eq R (owner i)).trans hiC
  have hnextOwner : R (owner i) ∈ permutationFamilyOwnerSet owner :=
    (Finset.mem_filter.mp hC).2 _ hnextC
  obtain ⟨j, _hjUniv, hjOwner⟩ := Finset.mem_image.mp hnextOwner
  refine ⟨j, ⟨hjOwner, ?_⟩, ?_⟩
  · rw [hjOwner]
    exact hnextC
  · intro k hk
    exact howner (hk.1.trans hjOwner.symm)

/-- On a full occupied component, the unique selected successor row carries
the exact centered affine doubling recurrence. -/
theorem permutationFamilyFullComponent_uniqueSuccessorRow_affine
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (x : α → G) (target : ι → G)
    (howner : Function.Injective owner)
    (hdouble : ∀ a, x (R a) = 2 • x a)
    (epsilon : ℤ) (offset : G)
    (haffine : ∀ i, target i = epsilon • x (owner i) + offset)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetFullComponents R
      (permutationFamilyOwnerSet owner))
    (i : ι)
    (hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C) :
    ∃! j : ι,
      owner j = R (owner i) ∧
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner j) = C ∧
        target j - offset = 2 • (target i - offset) := by
  obtain ⟨j, hj, hjUnique⟩ :=
    permutationFamilyFullComponent_uniqueSuccessorRow
      R owner howner C hC i hiC
  have hcentered : ∀ k, target k - offset = epsilon • x (owner k) := by
    intro k
    rw [haffine k]
    abel
  refine ⟨j, ⟨hj.1, hj.2, ?_⟩, ?_⟩
  · calc
      target j - offset = epsilon • x (owner j) := hcentered j
      _ = epsilon • x (R (owner i)) := by rw [hj.1]
      _ = epsilon • (2 • x (owner i)) := by rw [hdouble]
      _ = epsilon • x (owner i) + epsilon • x (owner i) := by
        rw [two_nsmul, smul_add]
      _ = 2 • (target i - offset) := by
        rw [hcentered i, two_nsmul]
  · intro k hk
    exact hjUnique k ⟨hk.1, hk.2.1⟩

/-- On a full occupied component, the unique selected successor rows assemble
into a permutation of the component fiber.  This packages pointwise closure
under the ambient permutation into the finite dynamical system needed for
cycle iteration. -/
theorem permutationFamilyFullComponent_exists_successorPerm
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetFullComponents R
      (permutationFamilyOwnerSet owner)) :
    ∃ Q : Equiv.Perm ↥(permutationFamilyComponentFiber R owner C),
      ∀ i, owner (Q i : ι) = R (owner (i : ι)) := by
  classical
  let fiber := permutationFamilyComponentFiber R owner C
  let next : ↥fiber → ↥fiber := fun i ↦ by
    have hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R)
        (owner (i : ι)) = C := by
      exact (Finset.mem_filter.mp i.property).2
    let hnext := permutationFamilyFullComponent_uniqueSuccessorRow
      R owner howner C hC (i : ι) hiC
    let j : ι := Classical.choose hnext
    have hj := (Classical.choose_spec hnext).1
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.2⟩⟩
  have hnextOwner : ∀ i : ↥fiber,
      owner (next i : ι) = R (owner (i : ι)) := by
    intro i
    dsimp only [next]
    exact (Classical.choose_spec
      (permutationFamilyFullComponent_uniqueSuccessorRow
        R owner howner C hC (i : ι)
          (Finset.mem_filter.mp i.property).2)).1.1
  have hnextInjective : Function.Injective next := by
    intro i k hik
    apply Subtype.ext
    apply howner
    apply R.injective
    calc
      R (owner (i : ι)) = owner (next i : ι) := (hnextOwner i).symm
      _ = owner (next k : ι) := congrArg (fun u : ↥fiber ↦ owner (u : ι)) hik
      _ = R (owner (k : ι)) := hnextOwner k
  have hnextBijective : Function.Bijective next :=
    Finite.injective_iff_bijective.mp hnextInjective
  let Q : Equiv.Perm ↥fiber := Equiv.ofBijective next hnextBijective
  refine ⟨Q, ?_⟩
  intro i
  exact hnextOwner i

/-- The successor permutation of a full component is one cycle, not a
disjoint union of smaller row cycles.  Fullness identifies its row fiber
with the entire ambient `SameCycle` class, and owner injectivity transports
ambient iterates back to rows. -/
theorem permutationFamilyFullComponent_successorPerm_isCycle
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner)
    (hRne : ∀ a, R a ≠ a)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetFullComponents R
      (permutationFamilyOwnerSet owner))
    (Q : Equiv.Perm ↥(permutationFamilyComponentFiber R owner C))
    (hQOwner : ∀ i, owner (Q i : ι) = R (owner (i : ι))) :
    Q.IsCycle := by
  classical
  let fiber := permutationFamilyComponentFiber R owner C
  have hQne : ∀ i : ↥fiber, Q i ≠ i := by
    intro i hi
    apply hRne (owner (i : ι))
    calc
      R (owner (i : ι)) = owner (Q i : ι) := (hQOwner i).symm
      _ = owner (i : ι) :=
        congrArg (fun k : ↥fiber ↦ owner (k : ι)) hi
  have hoccupied : C ∈ permutationSubsetComponents R
      (permutationFamilyOwnerSet owner) :=
    (Finset.mem_filter.mp hC).1
  obtain ⟨a, haOwner, haC⟩ := Finset.mem_image.mp hoccupied
  obtain ⟨i₀, _hi₀, hi₀Owner⟩ := Finset.mem_image.mp haOwner
  let i₀' : ↥fiber := ⟨i₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ i₀, by simpa [hi₀Owner] using haC⟩⟩
  refine ⟨i₀', hQne i₀', ?_⟩
  intro j _hj
  have hsame : R.SameCycle (owner (i₀' : ι)) (owner (j : ι)) := by
    change (Equiv.Perm.SameCycle.setoid R).r
      (owner (i₀' : ι)) (owner (j : ι))
    apply Quotient.exact
    exact (Finset.mem_filter.mp i₀'.property).2.trans
      (Finset.mem_filter.mp j.property).2.symm
  obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
  have hiterate : ∀ ell : ℕ, ∀ i : ↥fiber,
      owner (Q^[ell] i : ι) = R^[ell] (owner (i : ι)) := by
    intro ell
    induction ell with
    | zero =>
        intro i
        rfl
    | succ ell ih =>
        intro i
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hQOwner, ih]
  have hk' : R^[k] (owner (i₀' : ι)) = owner (j : ι) := by
    simpa only [Equiv.Perm.iterate_eq_pow] using hk
  have hrow : Q^[k] i₀' = j := by
    apply Subtype.ext
    apply howner
    exact (hiterate k i₀').trans hk'
  refine ⟨(k : ℤ), ?_⟩
  simpa only [zpow_natCast, Equiv.Perm.iterate_eq_pow] using hrow

/-- A fixed-point-free ambient permutation turns every full selected
component into a bounded nontrivial successor cycle.  Any quantity which
doubles along selected successors is consequently annihilated by the odd
Mersenne coefficient attached to that cycle; its length is bounded by the
ambient carrier, independently of the size of the original row family. -/
theorem permutationFamilyFullComponent_exists_bounded_oddTorsion
    {ι α A : Type*} [Fintype ι] [Fintype α] [AddCommGroup A]
    (R : Equiv.Perm α) (owner : ι → α) (value : ι → A)
    (howner : Function.Injective owner)
    (hRne : ∀ a, R a ≠ a)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (hC : C ∈ permutationSubsetFullComponents R
      (permutationFamilyOwnerSet owner))
    (hvalue : ∀ (i j : ι),
      Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C →
      owner j = R (owner i) → value j = 2 • value i) :
    ∃ Q : Equiv.Perm ↥(permutationFamilyComponentFiber R owner C),
      (∀ i, owner (Q i : ι) = R (owner (i : ι))) ∧
      (∀ i, value (Q i : ι) = 2 • value (i : ι)) ∧
      ∃ i, ∃ ell : ℕ,
        2 ≤ ell ∧ ell ≤ Fintype.card α ∧ Q^[ell] i = i ∧
          Odd (2 ^ ell - 1) ∧ (2 ^ ell - 1) • value (i : ι) = 0 := by
  classical
  let fiber := permutationFamilyComponentFiber R owner C
  obtain ⟨Q, hQOwner⟩ :=
    permutationFamilyFullComponent_exists_successorPerm
      R owner howner C hC
  have hQValue : ∀ i : ↥fiber,
      value (Q i : ι) = 2 • value (i : ι) := by
    intro i
    exact hvalue (i : ι) (Q i : ι)
      (Finset.mem_filter.mp i.property).2 (hQOwner i)
  have hQne : ∀ i : ↥fiber, Q i ≠ i := by
    intro i hi
    apply hRne (owner (i : ι))
    calc
      R (owner (i : ι)) = owner (Q i : ι) := (hQOwner i).symm
      _ = owner (i : ι) :=
        congrArg (fun k : ↥fiber ↦ owner (k : ι)) hi
  have hoccupied : C ∈ permutationSubsetComponents R
      (permutationFamilyOwnerSet owner) :=
    (Finset.mem_filter.mp hC).1
  obtain ⟨a, haOwner, haC⟩ := Finset.mem_image.mp hoccupied
  obtain ⟨i₀, _hi₀, hi₀Owner⟩ := Finset.mem_image.mp haOwner
  let i₀' : ↥fiber := ⟨i₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ i₀, by simpa [hi₀Owner] using haC⟩⟩
  obtain ⟨i, ell, hellTwo, hellFiber, hperiod⟩ :=
    exists_bounded_cycle_of_fixedPointFree Q i₀' hQne
  have hfiberCard : Fintype.card ↥fiber ≤ Fintype.card α := by
    apply Fintype.card_le_of_injective
      (fun k : ↥fiber ↦ owner (k : ι))
    intro j k hjk
    apply Subtype.ext
    exact howner hjk
  have htorsion : (2 ^ ell - 1) • value (i : ι) = 0 :=
    pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
      Q (fun k : ↥fiber ↦ value (k : ι)) hQValue hperiod
  refine ⟨Q, hQOwner, hQValue, i, ell, hellTwo,
    hellFiber.trans hfiberCard, hperiod, ?_, htorsion⟩
  exact odd_two_pow_sub_one (by omega)

/-- On one fixed-point-free finite cycle, a doubling-labelled family is
either identically zero or its multiplicity bound becomes an additive-order
charge.  In the nonzero arm the chosen value has order dividing the full
cycle's Mersenne number, and the cycle cardinality is at most `K` times the
number of its nonzero cyclic multiples. -/
theorem isCycle_doubling_zero_or_orderCharge
    {β A : Type*} [Fintype β] [Fintype A] [AddCommGroup A]
    [DecidableEq A]
    (Q : Equiv.Perm β) (value : β → A)
    (hcycle : Q.IsCycle) (hQne : ∀ i, Q i ≠ i)
    (hdouble : ∀ i, value (Q i) = 2 • value i)
    (K : ℕ)
    (hmultiplicity : ∀ z : A,
      (Finset.univ.filter (fun i : β ↦ value i = z)).card ≤ K) :
    (∀ i, value i = 0) ∨
      ∃ i, value i ≠ 0 ∧
        addOrderOf (value i) ∣ 2 ^ Fintype.card β - 1 ∧
        Fintype.card β ≤ K * (addOrderOf (value i) - 1) := by
  classical
  have hcycle' := hcycle
  obtain ⟨i₀, _hi₀, _hsame⟩ := hcycle'
  have hreach : ∀ i j : β, ∃ k : ℕ, Q^[k] i = j := by
    intro i j
    obtain ⟨k, hk⟩ := hcycle.exists_pow_eq (hQne i) (hQne j)
    exact ⟨k, by simpa only [Equiv.Perm.iterate_eq_pow] using hk⟩
  by_cases hi₀Zero : value i₀ = 0
  · left
    intro j
    obtain ⟨k, hk⟩ := hreach i₀ j
    have hiter :=
      apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
        Q value hdouble k i₀
    rw [hk, hi₀Zero] at hiter
    simpa using hiter
  · right
    have hallNonzero : ∀ j, value j ≠ 0 := by
      intro j hjZero
      obtain ⟨k, hk⟩ := hreach j i₀
      have hiter :=
        apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
          Q value hdouble k j
      rw [hk, hjZero] at hiter
      exact hi₀Zero (by simpa using hiter)
    have hsupport : Q.support = Finset.univ := by
      ext j
      simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
      exact hQne j
    have horder : orderOf Q = Fintype.card β := by
      rw [hcycle.orderOf, hsupport]
      simp
    have hperiod : Q^[Fintype.card β] i₀ = i₀ := by
      rw [Equiv.Perm.iterate_eq_pow, ← horder, pow_orderOf_eq_one]
      rfl
    have htorsion : (2 ^ Fintype.card β - 1) • value i₀ = 0 :=
      pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
        Q value hdouble hperiod
    have hdvd : addOrderOf (value i₀) ∣ 2 ^ Fintype.card β - 1 :=
      addOrderOf_dvd_of_nsmul_eq_zero htorsion
    have hvalueMem : ∀ j, value j ∈ AddSubgroup.zmultiples (value i₀) := by
      intro j
      obtain ⟨k, hk⟩ := hreach i₀ j
      have hiter :=
        apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
          Q value hdouble k i₀
      rw [hk] at hiter
      rw [hiter]
      exact (AddSubgroup.zmultiples (value i₀)).nsmul_mem
        (AddSubgroup.mem_zmultiples (value i₀)) (2 ^ k)
    let target : β → AddSubgroup.zmultiples (value i₀) := fun j ↦
      ⟨value j, hvalueMem j⟩
    let nonzero : Finset (AddSubgroup.zmultiples (value i₀)) :=
      Finset.univ.erase 0
    have hnonzeroCard : nonzero.card = addOrderOf (value i₀) - 1 := by
      dsimp only [nonzero]
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
      simp only [Finset.card_univ]
      rw [Fintype.card_zmultiples]
    have htargetMem : ∀ j, target j ∈ nonzero := by
      intro j
      have htargetNe : target j ≠ 0 := by
        intro hj
        exact hallNonzero j (congrArg Subtype.val hj)
      simpa [nonzero] using htargetNe
    rcases finiteMap_capacity_or_largeFiber
        nonzero target htargetMem K with hcap | ⟨z, _hz, hlarge⟩
    · refine ⟨i₀, hi₀Zero, hdvd, ?_⟩
      rw [hnonzeroCard] at hcap
      simpa [Nat.mul_comm] using hcap
    · have hfiberLe :
          (Finset.univ.filter (fun j : β ↦ target j = z)).card ≤ K := by
        simpa [target, Subtype.ext_iff] using hmultiplicity (z : A)
      exact (Nat.not_lt_of_ge hfiberLe hlarge).elim

/-- Restricting a finite family to one permutation component cannot increase
the multiplicity of any value.  The statement keeps the subtype bookkeeping
explicit so componentwise cycle arguments can reuse ambient target-fiber
bounds without reconstructing a row family. -/
theorem permutationFamilyComponentFiber_valueFiber_card_le
    {ι α β : Type*} [Fintype α] [DecidableEq β]
    (R : Equiv.Perm α) (owner : ι → α)
    (S : Finset ι) (value : ι → β)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R)) (K : ℕ)
    (hmultiplicity : ∀ z : β,
      (S.filter (fun i ↦ value i = z)).card ≤ K) :
    ∀ z : β,
      (Finset.univ.filter (fun i :
        ↥(permutationFamilyComponentFiber R
          (fun s : ↥S ↦ owner (s : ι)) C) ↦
            value (((i : ↥S) : ι)) = z)).card ≤ K := by
  classical
  intro z
  let fiber := permutationFamilyComponentFiber R
    (fun s : ↥S ↦ owner (s : ι)) C
  let U : Finset ↥fiber := Finset.univ.filter (fun i ↦
    value (((i : ↥S) : ι)) = z)
  let V : Finset ι := S.filter (fun i ↦ value i = z)
  let embed : ↥U → ↥V := fun u ↦ by
    refine ⟨(((u : ↥fiber) : ↥S) : ι), ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨((u : ↥fiber) : ↥S).property, ?_⟩
    exact (Finset.mem_filter.mp u.property).2
  have hembed : Function.Injective embed := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ↥V ↦ (w : ι)) huv
  have hcard : U.card ≤ V.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective embed hembed
  have hV : V.card ≤ K := by
    simpa only [V] using hmultiplicity z
  simpa only [U, fiber] using hcard.trans hV

/-- The ambient owner of a row selected through three nested finite filters. -/
def nestedSelectedOwner
    {α : Type*} {J : Finset α} {E : Finset ↥J}
    {F : Finset ↥E} (S : Finset ↥F) : ↥S → α := fun f ↦
  (((f : ↥F) : ↥E) : ↥J)

/-- Nested subtype inclusion never identifies two selected row owners. -/
theorem nestedSelectedOwner_injective
    {α : Type*} {J : Finset α} {E : Finset ↥J}
    {F : Finset ↥E} (S : Finset ↥F) :
    Function.Injective (nestedSelectedOwner S) := by
  intro f k h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Lossless first-failure classification for a successor leaving a nested
selected row family.  The successor leaves the outer index set, lands in the
other side of its partition, leaves the fixed-label fiber, or leaves only the
final profile filter. -/
theorem nestedSelectedBoundaryRow_successor_firstFailure
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F)
    (s : ↥S)
    (hboundary : ∀ f : ↥S,
      ((((f : ↥F) : ↥E) : ↥J) : α) ≠
        R ((((s : ↥F) : ↥E) : ↥J) : α)) :
    R ((((s : ↥F) : ↥E) : ↥J) : α) ∉ J ∨
      (∃ i : ↥I,
        ((i : ↥J) : α) = R ((((s : ↥F) : ↥E) : ↥J) : α)) ∨
      (∃ e : ↥E,
        ((e : ↥J) : α) = R ((((s : ↥F) : ↥E) : ↥J) : α) ∧ e ∉ F) ∨
      ∃ f : ↥F,
        (((f : ↥E) : ↥J) : α) =
            R ((((s : ↥F) : ↥E) : ↥J) : α) ∧
          f ∉ S := by
  classical
  let next : α := R ((((s : ↥F) : ↥E) : ↥J) : α)
  by_cases hnextJ : next ∈ J
  · let j : ↥J := ⟨next, hnextJ⟩
    have hjPartition : j ∈ E ∪ I := by
      rw [hpartition]
      exact Finset.mem_univ j
    rcases Finset.mem_union.mp hjPartition with hjE | hjI
    · let e : ↥E := ⟨j, hjE⟩
      by_cases heF : e ∈ F
      · let f : ↥F := ⟨e, heF⟩
        right
        right
        right
        refine ⟨f, by rfl, ?_⟩
        intro hfS
        exact hboundary (⟨f, hfS⟩ : ↥S) (by rfl)
      · right
        right
        left
        exact ⟨e, by rfl, heF⟩
    · right
      left
      exact ⟨(⟨j, hjI⟩ : ↥I), by rfl⟩
  · left
    exact hnextJ

/-- Boundary-row form of the nested first-failure classification. -/
theorem nestedSelectedBoundaryRow_successor_firstFailure_of_boundary
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F)
    (s : ↥(permutationFamilyBoundaryRows R (nestedSelectedOwner S))) :
    R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∉ J ∨
      (∃ i : ↥I, ((i : ↥J) : α) =
        R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α)) ∨
      (∃ e : ↥E, ((e : ↥J) : α) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∧ e ∉ F) ∨
      ∃ f : ↥F, (((f : ↥E) : ↥J) : α) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∧ f ∉ S := by
  apply nestedSelectedBoundaryRow_successor_firstFailure
    R J E I hpartition F S (s : ↥S)
  exact permutationFamilyBoundaryRow_owner_ne_successor
    R (nestedSelectedOwner S) s

/-- Named row-level payload for the four possible successor exits from a
nested selected family.  Keeping this proposition named prevents downstream
frontiers from repeatedly elaborating the full dependent disjunction. -/
def NestedBoundaryRowSuccessorTransition
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (F : Finset ↥E) (S : Finset ↥F)
    (owner : ↥S → α)
    (s : ↥(permutationFamilyBoundaryRows R owner)) : Prop :=
  R (owner (s : ↥S)) ∉ J ∨
    (∃ i : ↥I, ((i : ↥J) : α) = R (owner (s : ↥S))) ∨
    (∃ e : ↥E, ((e : ↥J) : α) = R (owner (s : ↥S)) ∧ e ∉ F) ∨
    ∃ f : ↥F, (((f : ↥E) : ↥J) : α) =
        R (owner (s : ↥S)) ∧ f ∉ S

/-- Every genuine boundary source row of a nested selected family carries
the named four-layer successor transition payload. -/
theorem nestedSelectedBoundaryRow_successor_transition
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F)
    (s : ↥(permutationFamilyBoundaryRows R (nestedSelectedOwner S))) :
    NestedBoundaryRowSuccessorTransition
      R J E I F S (nestedSelectedOwner S) s := by
  exact nestedSelectedBoundaryRow_successor_firstFailure_of_boundary
    R J E I hpartition F S s

/-- Ambient successor targets associated with the four nested boundary
transition layers. -/
def nestedBoundaryTransitionTargets
    {α : Type*} [Fintype α] [DecidableEq α]
    (J : Finset α) (E I : Finset ↥J)
    (F : Finset ↥E) (S : Finset ↥F) : Finset α :=
  (((Finset.univ \ J) ∪
    I.image (fun i ↦ ((i : ↥J) : α)) ∪
    (Finset.univ \ F).image (fun e ↦ (((e : ↥E) : ↥J) : α))) ∪
    (Finset.univ \ S).image (fun f ↦
      ((((f : ↥F) : ↥E) : ↥J) : α)))

/-- Every nested boundary-row successor belongs to one of the four explicit
transition target layers. -/
theorem nestedSelectedBoundaryRow_successor_mem_transitionTargets
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F)
    (s : ↥(permutationFamilyBoundaryRows R (nestedSelectedOwner S))) :
    R (nestedSelectedOwner S (s : ↥S)) ∈
      nestedBoundaryTransitionTargets J E I F S := by
  unfold nestedBoundaryTransitionTargets
  rcases nestedSelectedBoundaryRow_successor_firstFailure_of_boundary
      R J E I hpartition F S s with
    houtside | ⟨i, hi⟩ | ⟨e, he, heNotF⟩ | ⟨f, hf, hfNotS⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, houtside⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(i : ↥J), i.property, hi⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heNotF⟩, he⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨f, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfNotS⟩, hf⟩

/-- The four transition target layers cost no more than the sum of their
source-layer cardinalities. -/
theorem card_nestedBoundaryTransitionTargets_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (J : Finset α) (E I : Finset ↥J)
    (F : Finset ↥E) (S : Finset ↥F) :
    (nestedBoundaryTransitionTargets J E I F S).card ≤
      (Finset.univ \ J).card + I.card +
        (Finset.univ \ F).card + (Finset.univ \ S).card := by
  let outside : Finset α := Finset.univ \ J
  let internal : Finset α := I.image fun i ↦ ((i : ↥J) : α)
  let relabel : Finset α := (Finset.univ \ F).image fun e ↦
    (((e : ↥E) : ↥J) : α)
  let reprofile : Finset α := (Finset.univ \ S).image fun f ↦
    ((((f : ↥F) : ↥E) : ↥J) : α)
  change (((outside ∪ internal) ∪ relabel) ∪ reprofile).card ≤
    outside.card + I.card + (Finset.univ \ F).card +
      (Finset.univ \ S).card
  have hI : internal.card ≤ I.card := by
    exact Finset.card_image_le
  have hF : relabel.card ≤ (Finset.univ \ F).card := by
    exact Finset.card_image_le
  have hS : reprofile.card ≤ (Finset.univ \ S).card := by
    exact Finset.card_image_le
  calc
    (((outside ∪ internal) ∪ relabel) ∪ reprofile).card ≤
        ((outside ∪ internal) ∪ relabel).card + reprofile.card :=
      Finset.card_union_le _ _
    _ ≤ ((outside ∪ internal).card + relabel.card) + reprofile.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((outside.card + internal.card) + relabel.card) + reprofile.card :=
      Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ ((outside.card + I.card) + (Finset.univ \ F).card) +
        (Finset.univ \ S).card :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hI _) hF) hS
    _ = outside.card + I.card + (Finset.univ \ F).card +
        (Finset.univ \ S).card := by omega

/-- For an actual `E`/`I` partition, the four complement-layer budgets
 telescope to the ambient complement of the final selected family.  The
unsimplified equality remains useful because each summand has a different
geometric charge. -/
theorem nestedBoundaryTransitionLayerBudget_eq_card_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ) (hdisjoint : Disjoint E I)
    (F : Finset ↥E) (S : Finset ↥F) :
    (Finset.univ \ J).card + I.card +
        (Finset.univ \ F).card + (Finset.univ \ S).card =
      Fintype.card α - S.card := by
  have hEI : E.card + I.card = J.card := by
    calc
      E.card + I.card = (E ∪ I).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ = (Finset.univ : Finset ↥J).card := by rw [hpartition]
      _ = J.card := by simp
  have hJle : J.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ J)
  have hFle : F.card ≤ E.card := by
    simpa [Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ F)
  have hSle : S.card ≤ F.card := by
    simpa [Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ S)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ J),
    Finset.card_sdiff_of_subset (Finset.subset_univ F),
    Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp only [Finset.card_univ, Fintype.card_coe]
  omega

/-- Quantitative mixed-transition charge.  Injectivity of nested ownership
and of the permutation sends boundary source rows injectively into the four
explicit complement layers. -/
theorem card_nestedSelectedBoundaryRows_le_transitionLayers
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F) :
    (permutationFamilyBoundaryRows R (nestedSelectedOwner S)).card ≤
      (Finset.univ \ J).card + I.card +
        (Finset.univ \ F).card + (Finset.univ \ S).card := by
  let boundary := permutationFamilyBoundaryRows R (nestedSelectedOwner S)
  let targets := nestedBoundaryTransitionTargets J E I F S
  let successor : ↥boundary → ↥targets := fun s ↦
    ⟨R (nestedSelectedOwner S (s : ↥S)),
      nestedSelectedBoundaryRow_successor_mem_transitionTargets
        R J E I hpartition F S s⟩
  have hsuccessor : Function.Injective successor := by
    intro s u hsu
    apply Subtype.ext
    apply nestedSelectedOwner_injective S
    apply R.injective
    exact congrArg Subtype.val hsu
  have hcard : Fintype.card ↥boundary ≤ Fintype.card ↥targets :=
    Fintype.card_le_of_injective successor hsuccessor
  have htarget := card_nestedBoundaryTransitionTargets_le J E I F S
  have hboundaryCard : boundary.card ≤ targets.card := by
    simpa only [Fintype.card_coe] using hcard
  have htarget' : targets.card ≤
      (Finset.univ \ J).card + I.card +
        (Finset.univ \ F).card + (Finset.univ \ S).card := by
    dsimp only [targets]
    exact htarget
  exact hboundaryCard.trans htarget'

/-- After dominant selection from the six external labels and three owner
profiles, the two inner transition layers cost at most `17 * S.card`. -/
theorem card_nestedSelectedBoundaryRows_le_outer_add_internal_add_seventeen
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (F : Finset ↥E) (S : Finset ↥F)
    (hFdominant : E.card ≤ 6 * F.card)
    (hSdominant : F.card ≤ 3 * S.card) :
    (permutationFamilyBoundaryRows R (nestedSelectedOwner S)).card ≤
      (Finset.univ \ J).card + I.card + 17 * S.card := by
  have hboundary := card_nestedSelectedBoundaryRows_le_transitionLayers
    R J E I hpartition F S
  have hinner := card_twoStageFiberComplements_le_seventeen_mul F S
    (by simpa [Fintype.card_coe] using hFdominant) hSdominant
  omega

/-- A row set occupying at least `d-1` positions in `Fin d` misses at most
one ambient position. -/
theorem card_fin_compl_le_one_of_sub_one_le_card
    {d : ℕ} (J : Finset (Fin d)) (hJ : d - 1 ≤ J.card) :
    (Finset.univ \ J).card ≤ 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ J)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- In the non-dense-internal arm, the two dominant finite-label selections
pay for both the internal rows and the original total-row lower bound. -/
theorem twoStageDominance_internalSparse_bounds
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : ℕ) (E I : Finset α) (F : Finset ↥E) (S : Finset ↥F)
    (hlarge : d - 1 ≤ E.card + I.card)
    (hFdominant : E.card ≤ 6 * F.card)
    (hSdominant : F.card ≤ 3 * S.card)
    (hIsparse : 2 * I.card < d - 1) :
    I.card < 18 * S.card ∧ d - 1 < 36 * S.card := by
  have hE : E.card ≤ 18 * S.card := by
    omega
  omega

/-- Once the outer defect and the non-dense internal arm are routed, every
selected boundary row is paid for by thirty-five copies of the same dominant
affine family.  The decomposed constant-seventeen bound remains available
separately for later geometric refinements. -/
theorem card_nestedSelectedBoundaryRows_le_thirty_five_mul
    {d : ℕ} (R : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (E I : Finset ↥J)
    (hJ : d - 1 ≤ J.card)
    (hpartition : E ∪ I = Finset.univ)
    (hlarge : d - 1 ≤ E.card + I.card)
    (F : Finset ↥E) (S : Finset ↥F)
    (hFdominant : E.card ≤ 6 * F.card)
    (hSdominant : F.card ≤ 3 * S.card)
    (hIsparse : 2 * I.card < d - 1) :
    (permutationFamilyBoundaryRows R (nestedSelectedOwner S)).card ≤
      35 * S.card := by
  have hboundary :=
    card_nestedSelectedBoundaryRows_le_outer_add_internal_add_seventeen
      R J E I hpartition F S hFdominant hSdominant
  have houter := card_fin_compl_le_one_of_sub_one_le_card J hJ
  have hI := (twoStageDominance_internalSparse_bounds
    d E I F S hlarge hFdominant hSdominant hIsparse).1
  omega

/-- Telescoped ambient form of the quantitative mixed-transition charge. -/
theorem card_nestedSelectedBoundaryRows_le_card_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ) (hdisjoint : Disjoint E I)
    (F : Finset ↥E) (S : Finset ↥F) :
    (permutationFamilyBoundaryRows R (nestedSelectedOwner S)).card ≤
      Fintype.card α - S.card := by
  calc
    (permutationFamilyBoundaryRows R (nestedSelectedOwner S)).card ≤
        (Finset.univ \ J).card + I.card +
          (Finset.univ \ F).card + (Finset.univ \ S).card :=
      card_nestedSelectedBoundaryRows_le_transitionLayers
        R J E I hpartition F S
    _ = Fintype.card α - S.card :=
      nestedBoundaryTransitionLayerBudget_eq_card_sub
        J E I hpartition hdisjoint F S

/-- Semantic form of the nested boundary split when the last two selection
layers are fibers of explicit label maps.  Exiting those layers is exactly a
change of the corresponding label, so later counting may charge the finite
label alphabets directly. -/
theorem nestedFilteredBoundaryRow_successor_transition
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ]
    (R : Equiv.Perm α)
    (J : Finset α) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (label : ↥E → β) (fixedLabel : β)
    (F : Finset ↥E)
    (hF : F = Finset.univ.filter (fun e ↦ label e = fixedLabel))
    (profile : ↥F → γ) (fixedProfile : γ)
    (S : Finset ↥F)
    (hS : S = Finset.univ.filter (fun f ↦ profile f = fixedProfile))
    (s : ↥(permutationFamilyBoundaryRows R (nestedSelectedOwner S))) :
    R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∉ J ∨
      (∃ i : ↥I, ((i : ↥J) : α) =
        R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α)) ∨
      (∃ e : ↥E, ((e : ↥J) : α) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∧
            label e ≠ fixedLabel) ∨
      ∃ f : ↥F, (((f : ↥E) : ↥J) : α) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : α) ∧
            profile f ≠ fixedProfile := by
  rcases nestedSelectedBoundaryRow_successor_firstFailure_of_boundary
      R J E I hpartition F S s with
    houtside | hinternal | hlabel | hprofile
  · exact Or.inl houtside
  · exact Or.inr (Or.inl hinternal)
  · right
    right
    left
    obtain ⟨e, heOwner, heNotF⟩ := hlabel
    refine ⟨e, heOwner, ?_⟩
    intro heLabel
    apply heNotF
    rw [hF]
    simp [heLabel]
  · right
    right
    right
    obtain ⟨f, hfOwner, hfNotS⟩ := hprofile
    refine ⟨f, hfOwner, ?_⟩
    intro hfProfile
    apply hfNotS
    rw [hS]
    simp [hfProfile]

/-- Family and owner-set definitions give the same occupied components. -/
theorem permutationFamilyComponents_eq_subsetComponents
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) :
    permutationFamilyComponents R owner =
      permutationSubsetComponents R (permutationFamilyOwnerSet owner) := by
  classical
  simp [permutationFamilyComponents, permutationSubsetComponents,
    permutationFamilyOwnerSet, Finset.image_image, Function.comp_def]

/-- The occupied components of a finite family are controlled by full owner
components and owner-set boundary vertices. -/
theorem card_permutationFamilyComponents_le_full_add_boundary
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) :
    (permutationFamilyComponents R owner).card ≤
      (permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner)).card +
      (permutationSubsetBoundary R
        (permutationFamilyOwnerSet owner)).card := by
  rw [permutationFamilyComponents_eq_subsetComponents]
  exact card_permutationSubsetComponents_le_full_add_boundary R
    (permutationFamilyOwnerSet owner)

/-- Exact occupied-component frontier for a finite family: either `K` slots
per occupied component suffice, or one component contains more than `K`
members. -/
theorem permutationFamily_capacity_or_largeComponent
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) (K : ℕ) :
    Fintype.card ι ≤ (permutationFamilyComponents R owner).card * K ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        K < (permutationFamilyComponentFiber R owner C).card := by
  classical
  let component : ι → Quotient (Equiv.Perm.SameCycle.setoid R) := fun i ↦
    Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i)
  have hcomponent : ∀ i : ι,
      component i ∈ permutationFamilyComponents R owner := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rcases finiteMap_capacity_or_largeFiber
      (permutationFamilyComponents R owner) component hcomponent K with
    hcap | ⟨C, hC, hlarge⟩
  · exact Or.inl hcap
  · exact Or.inr ⟨C, hC, by
      simpa [component, permutationFamilyComponentFiber] using hlarge⟩

/-- If every full selected component has capacity `K`, then either all rows
fit in `K` slots per full-or-boundary component, or an oversized occupied
component is provably nonfull and comes with an explicit selected boundary
vertex in that same ambient cycle. -/
theorem permutationFamily_fullCapacity_or_largeBoundaryComponent
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α) (K : ℕ)
    (hfullBound : ∀ C,
      C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner) →
      (permutationFamilyComponentFiber R owner C).card ≤ K) :
    Fintype.card ι ≤
        ((permutationSubsetFullComponents R
            (permutationFamilyOwnerSet owner)).card +
          (permutationSubsetBoundary R
            (permutationFamilyOwnerSet owner)).card) * K ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        K < (permutationFamilyComponentFiber R owner C).card ∧
        C ∉ permutationSubsetFullComponents R
          (permutationFamilyOwnerSet owner) ∧
        ∃ x ∈ permutationSubsetBoundary R
            (permutationFamilyOwnerSet owner),
          Quotient.mk (Equiv.Perm.SameCycle.setoid R) x = C := by
  classical
  rcases permutationFamily_capacity_or_largeComponent R owner K with
    hcap | ⟨C, hC, hlarge⟩
  · left
    exact hcap.trans (Nat.mul_le_mul_right K
      (card_permutationFamilyComponents_le_full_add_boundary R owner))
  · right
    have hnotFull : C ∉ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner) := by
      intro hfull
      exact (Nat.not_lt_of_ge (hfullBound C hfull)) hlarge
    have hC' : C ∈ permutationSubsetComponents R
        (permutationFamilyOwnerSet owner) := by
      rw [← permutationFamilyComponents_eq_subsetComponents]
      exact hC
    rcases mem_fullComponents_or_exists_mem_boundary
        R (permutationFamilyOwnerSet owner) C hC' with
      hfull | ⟨x, hx, hxC⟩
    · exact (hnotFull hfull).elim
    · exact ⟨C, hC, hlarge, hnotFull, x, hx, hxC⟩

/-- Injective owners lift the boundary vertex of an oversized nonfull
component to a genuine selected boundary source row in the same component.
This is the row-level form needed by successor first-failure arguments. -/
theorem permutationFamily_fullCapacity_or_largeBoundaryRow
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (howner : Function.Injective owner) (K : ℕ)
    (hfullBound : ∀ C,
      C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner) →
      (permutationFamilyComponentFiber R owner C).card ≤ K) :
    Fintype.card ι ≤
        ((permutationSubsetFullComponents R
            (permutationFamilyOwnerSet owner)).card +
          (permutationSubsetBoundary R
            (permutationFamilyOwnerSet owner)).card) * K ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        K < (permutationFamilyComponentFiber R owner C).card ∧
        C ∉ permutationSubsetFullComponents R
          (permutationFamilyOwnerSet owner) ∧
        ∃ s : ↥(permutationFamilyBoundaryRows R owner),
          Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner (s : ι)) = C := by
  classical
  rcases permutationFamily_fullCapacity_or_largeBoundaryComponent
      R owner K hfullBound with
    hcap | ⟨C, hC, hlarge, hnotFull, a, haBoundary, haC⟩
  · exact Or.inl hcap
  · right
    obtain ⟨s, ⟨hsBoundary, hsOwner⟩, _hsUnique⟩ :=
      permutationFamilyBoundary_uniqueRow R owner howner haBoundary
    refine ⟨C, hC, hlarge, hnotFull, ⟨s, hsBoundary⟩, ?_⟩
    simpa [hsOwner] using haC

/-- Two members of one component fiber have owners in the same cycle. -/
theorem permutationFamilyComponentFiber_sameCycle
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (u v : ↥(permutationFamilyComponentFiber R owner C)) :
    R.SameCycle (owner (u : ι)) (owner (v : ι)) := by
  classical
  change (Equiv.Perm.SameCycle.setoid R).r
    (owner (u : ι)) (owner (v : ι))
  apply Quotient.exact
  have hu : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner (u : ι)) = C :=
    (Finset.mem_filter.mp u.property).2
  have hv : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner (v : ι)) = C :=
    (Finset.mem_filter.mp v.property).2
  exact hu.trans hv.symm

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

/-- Pairwise Mersenne comparison inside one occupied component of an affine
family.  Unlike `sameCycle_affineTargets_sub_eq_mersenne_nsmul`, the target
is indexed by the family rather than by every point of the permutation. -/
theorem permutationFamilyComponent_affineTargets_sub_eq_mersenne_nsmul
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (x : α → G) (target : ι → G)
    (hdouble : ∀ a, x (R a) = 2 • x a)
    (epsilon : ℤ) (offset : G)
    (haffine : ∀ i, target i = epsilon • x (owner i) + offset)
    (C : Quotient (Equiv.Perm.SameCycle.setoid R))
    (u v : ↥(permutationFamilyComponentFiber R owner C)) :
    ∃ k : ℕ, target (v : ι) - target (u : ι) =
      epsilon • ((2 ^ k - 1) • x (owner (u : ι))) := by
  have hsame := permutationFamilyComponentFiber_sameCycle R owner C u v
  obtain ⟨k, hk⟩ :=
    sameCycle_doubling_eq_pow_two_nsmul R x hdouble hsame
  refine ⟨k, ?_⟩
  rw [haffine (v : ι), haffine (u : ι), hk]
  have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hsplit : (2 ^ k) • x (owner (u : ι)) =
      (2 ^ k - 1) • x (owner (u : ι)) + x (owner (u : ι)) := by
    have hcoeff := congrArg (fun a : ℕ ↦ a • x (owner (u : ι)))
      (Nat.sub_add_cancel hone).symm
    simpa [add_nsmul, one_nsmul] using hcoeff
  rw [hsplit, smul_add]
  abel

/-- Occupied-component frontier with the affine recurrence retained in the
large-component arm.  This is the direct finite-family interface used by the
row partition: the capacity arm counts only occupied components. -/
theorem permutationFamily_affineComponentFrontier
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (x : α → G) (target : ι → G)
    (hdouble : ∀ a, x (R a) = 2 • x a)
    (epsilon : ℤ) (offset : G)
    (haffine : ∀ i, target i = epsilon • x (owner i) + offset)
    (K : ℕ) :
    Fintype.card ι ≤ (permutationFamilyComponents R owner).card * K ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        K < (permutationFamilyComponentFiber R owner C).card ∧
        ∀ u v : ↥(permutationFamilyComponentFiber R owner C),
          ∃ k : ℕ, target (v : ι) - target (u : ι) =
            epsilon • ((2 ^ k - 1) • x (owner (u : ι))) := by
  rcases permutationFamily_capacity_or_largeComponent R owner K with
    hcap | ⟨C, hC, hlarge⟩
  · exact Or.inl hcap
  · exact Or.inr ⟨C, hC, hlarge, fun u v ↦
      permutationFamilyComponent_affineTargets_sub_eq_mersenne_nsmul
        R owner x target hdouble epsilon offset haffine C u v⟩

/-- Threshold form of the affine component frontier.  A family larger than
`L` either forces its occupied-component budget above `L`, or has more than
`K` members in one component with all pairwise Mersenne comparisons. -/
theorem permutationFamily_large_affineComponentFrontier
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (x : α → G) (target : ι → G)
    (hdouble : ∀ a, x (R a) = 2 • x a)
    (epsilon : ℤ) (offset : G)
    (haffine : ∀ i, target i = epsilon • x (owner i) + offset)
    (L K : ℕ) (hlarge : L < Fintype.card ι) :
    L < (permutationFamilyComponents R owner).card * K ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        K < (permutationFamilyComponentFiber R owner C).card ∧
        ∀ u v : ↥(permutationFamilyComponentFiber R owner C),
          ∃ k : ℕ, target (v : ι) - target (u : ι) =
            epsilon • ((2 ^ k - 1) • x (owner (u : ι))) := by
  rcases permutationFamily_affineComponentFrontier
      R owner x target hdouble epsilon offset haffine K with
    hcap | hcomponent
  · exact Or.inl (hlarge.trans_le hcap)
  · exact Or.inr hcomponent

/-- Adaptive full-component/boundary form.  If the proposed full-component
and boundary budgets would fit below `L`, a family larger than `L` forces
one of those two budgets to overflow or yields a large affine component. -/
theorem permutationFamily_affine_fullComponent_or_boundary_or_largeComponent
    {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Equiv.Perm α) (owner : ι → α)
    (x : α → G) (target : ι → G)
    (hdouble : ∀ a, x (R a) = 2 • x a)
    (epsilon : ℤ) (offset : G)
    (haffine : ∀ i, target i = epsilon • x (owner i) + offset)
    (L fullThreshold boundaryThreshold componentThreshold : ℕ)
    (hbudget :
      (fullThreshold + boundaryThreshold) * componentThreshold ≤ L)
    (hlarge : L < Fintype.card ι) :
    fullThreshold <
        (permutationSubsetFullComponents R
          (permutationFamilyOwnerSet owner)).card ∨
      boundaryThreshold <
        (permutationSubsetBoundary R
          (permutationFamilyOwnerSet owner)).card ∨
      ∃ C ∈ permutationFamilyComponents R owner,
        componentThreshold <
            (permutationFamilyComponentFiber R owner C).card ∧
        ∀ u v : ↥(permutationFamilyComponentFiber R owner C),
          ∃ k : ℕ, target (v : ι) - target (u : ι) =
            epsilon • ((2 ^ k - 1) • x (owner (u : ι))) := by
  rcases permutationFamily_large_affineComponentFrontier
      R owner x target hdouble epsilon offset haffine
        L componentThreshold hlarge with
    hcomponents | hcomponent
  · by_cases hfull : fullThreshold <
        (permutationSubsetFullComponents R
          (permutationFamilyOwnerSet owner)).card
    · exact Or.inl hfull
    · right
      by_cases hboundary : boundaryThreshold <
          (permutationSubsetBoundary R
            (permutationFamilyOwnerSet owner)).card
      · exact Or.inl hboundary
      · exfalso
        have hcard := card_permutationFamilyComponents_le_full_add_boundary
          R owner
        have hsum :
            (permutationSubsetFullComponents R
                (permutationFamilyOwnerSet owner)).card +
              (permutationSubsetBoundary R
                (permutationFamilyOwnerSet owner)).card ≤
            fullThreshold + boundaryThreshold :=
          Nat.add_le_add (Nat.le_of_not_gt hfull)
            (Nat.le_of_not_gt hboundary)
        have hmul := Nat.mul_le_mul_right componentThreshold
          (hcard.trans hsum)
        exact (Nat.not_lt_of_ge (hmul.trans hbudget)) hcomponents
  · exact Or.inr (Or.inr hcomponent)

/-- The two-permutation affine relation gives the doubling recurrence on
leaf displacements when the center permutation is the same `P`. -/
theorem alignedCenterSuccessor_relativeDoubling
    (g : Fin n → G) (base : G) {d : ℕ}
    (leaf center : Fin d → Fin n) (P S : Equiv.Perm (Fin d))
    (hcenter : ∀ j, center j = leaf (P j))
    (hrel : ∀ j, (2 : ℤ) • g (leaf (P j)) =
      base + g (leaf (S j))) :
    ∀ j,
      g (center (P.symm ((P.symm.trans S) j))) - base =
        2 • (g (center (P.symm j)) - base) := by
  intro j
  rw [hcenter (P.symm ((P.symm.trans S) j)), P.apply_symm_apply,
    hcenter (P.symm j), P.apply_symm_apply]
  change g (leaf (S (P.symm j))) - base =
    2 • (g (leaf j) - base)
  have hj := hrel (P.symm j)
  rw [P.apply_symm_apply, two_zsmul] at hj
  rw [two_nsmul]
  calc
    g (leaf (S (P.symm j))) - base =
        (base + g (leaf (S (P.symm j)))) - (base + base) := by abel
    _ = (g (leaf j) + g (leaf j)) - (base + base) := by rw [← hj]
    _ = (g (leaf j) - base) + (g (leaf j) - base) := by abel

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

/-- An injective family of nonzero integer multiples of one element fits in
the nonzero part of its cyclic subgroup.  This is the global capacity form of
the cyclic-kernel charge; no decomposition into permutation components is
needed. -/
theorem card_le_addOrderOf_sub_one_of_injective_nonzero_zsmul
    [Fintype G] {ι : Type*} [Fintype ι]
    (y : G) (scalar : ι → ℤ)
    (hnonzero : ∀ i, scalar i • y ≠ 0)
    (hinjective : Function.Injective (fun i ↦ scalar i • y)) :
    Fintype.card ι ≤ addOrderOf y - 1 := by
  classical
  let embed : ι → ↥(nonzeroZMultiples y) := fun i ↦ by
    refine ⟨⟨scalar i • y, ?_⟩, ?_⟩
    · exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
    · simp only [nonzeroZMultiples, Finset.mem_erase, Finset.mem_univ,
        and_true]
      intro hzero
      exact hnonzero i (congrArg Subtype.val hzero)
  have hembed : Function.Injective embed := by
    intro i j hij
    apply hinjective
    exact congrArg
      (fun u : ↥(nonzeroZMultiples y) ↦
        ((u : AddSubgroup.zmultiples y) : G)) hij
  have hcard := Fintype.card_le_of_injective embed hembed
  simpa only [Fintype.card_coe, card_nonzeroZMultiples] using hcard

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

/-- At a deleted coordinate, positivity can occur in at most one row of a
private external fiber: privacy forces that coordinate to be the row's owner,
and the owner map is injective. -/
theorem fixedExternalFiberPositiveRowsAt_card_le_one_of_mem_deleted
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) {E : Finset ↥J}
    (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (S : Finset ↥F) (w : Fin n) (hwB : w ∈ B) :
    (fixedExternalFiberPositiveRowsAt coeff S w).card ≤ 1 := by
  classical
  rcases hfiber with
    ⟨_hxRange, _hxB, _hlambda, hownerInj, _hcoeffInj,
      _hrowData, hprivacy, _hoffdiag⟩
  rw [Finset.card_le_one]
  intro f hf k hk
  have hfPositive := (Finset.mem_filter.mp hf).2
  have hkPositive := (Finset.mem_filter.mp hk).2
  have hfOwner : w =
      center (P.symm (((f : ↥E) : ↥J) : Fin d)) := by
    by_contra hwOwner
    have hzero := hprivacy f w hwB hwOwner
    omega
  have hkOwner : w =
      center (P.symm (((k : ↥E) : ↥J) : Fin d)) := by
    by_contra hwOwner
    have hzero := hprivacy k w hwB hwOwner
    omega
  apply hownerInj
  exact hfOwner.symm.trans hkOwner

/-- With exactly two retained coordinates, a coordinate positive in two
selected private rows must be one of the fixed external column and the unique
companion retained column.  Thus high positive-row incidence cannot wander
over the ambient coordinate set. -/
theorem fixedExternalFiberPositiveRowsAt_large_eq_fixed_or_companion
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) {E : Finset ↥J}
    (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hretained : n - B.card = 2)
    (z : Fin n) (hzB : z ∉ B) (hzx : z ≠ x)
    (S : Finset ↥F) (w : Fin n)
    (hpositive : 1 < (fixedExternalFiberPositiveRowsAt coeff S w).card) :
    w = x ∨ w = z := by
  classical
  have hwB : w ∉ B := by
    intro hwB
    have hle := fixedExternalFiberPositiveRowsAt_card_le_one_of_mem_deleted
      B center P coeff F x lambda hfiber S w hwB
    omega
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfiber.2.1⟩
  have hzC : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem hCcard hxC hzC hzx.symm
  have hwC : w ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwB⟩
  rw [hCeq] at hwC
  simpa using hwC

/-- If one coordinate coefficient is constant on a selected family, its
positive-row set is exactly the whole family or the empty set according to
the sign of that constant. -/
theorem fixedExternalFiberPositiveRowsAt_eq_self_or_empty_of_constant
    {d : ℕ} {J : Finset (Fin d)} (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} {F : Finset ↥E} (S : Finset ↥F)
    (w : Fin n) (a : ℤ)
    (hconstant : ∀ f : ↥F, f ∈ S → coeff ((f : ↥E) : ↥J) w = a) :
    fixedExternalFiberPositiveRowsAt coeff S w =
      if 1 ≤ a then S else ∅ := by
  classical
  ext f
  by_cases hf : f ∈ S
  · have hvalue := hconstant f hf
    by_cases ha : 1 ≤ a
    · simp [fixedExternalFiberPositiveRowsAt, hf, hvalue, ha]
    · simp [fixedExternalFiberPositiveRowsAt, hf, hvalue, ha]
  · by_cases ha : 1 ≤ a
    · simp [fixedExternalFiberPositiveRowsAt, hf, ha]
    · simp [fixedExternalFiberPositiveRowsAt, hf, ha]

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

/-- Once the private-owner coefficient is fixed across a selected subfamily,
the target map is injective in the two-retained no-common-touch regime.  If
the fixed owner coefficient is at least two, an equal-target pair is a
forbidden heavy/heavy pair; otherwise it is the already impossible
light/light pair. -/
theorem fixedExternalCoefficientPrivateFiber_fixedOwnerCoefficient_target_injective
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : G) (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda mu : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (S : Finset ↥F)
    (hownerCoefficient : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
    (hretained : n - B.card ≤ 2) :
    Function.Injective (fun f : ↥S ↦
      scalar ((((f : ↥F) : ↥E) : ↥J)) • y) := by
  intro f k htarget
  by_contra hfk
  have hfkF : (f : ↥F) ≠ (k : ↥F) := by
    intro h
    exact hfk (Subtype.ext h)
  by_cases hmuHeavy : 2 ≤ mu
  · have hfHeavy : 2 ≤ coeff (((f : ↥S) : ↥F) : ↥E)
        (center (P.symm (((((f : ↥S) : ↥F) : ↥E) : ↥J) : Fin d))) := by
      rw [hownerCoefficient (f : ↥F) f.property]
      exact hmuHeavy
    have hkHeavy : 2 ≤ coeff (((k : ↥S) : ↥F) : ↥E)
        (center (P.symm (((((k : ↥S) : ↥F) : ↥E) : ↥J) : Fin d))) := by
      rw [hownerCoefficient (k : ↥F) k.property]
      exact hmuHeavy
    apply hno
    exact
      fixedExternalCoefficientPrivateFiber_equalTarget_twoHeavy_twoRetained_commonTouched
        g hg hh hne hunique y B center P scalar coeff F x lambda hfiber
          (fun j ↦ (hrows j).2) f k hfkF htarget hfHeavy hkHeavy hretained
  · have hfLight : ¬ 2 ≤ coeff (((f : ↥S) : ↥F) : ↥E)
        (center (P.symm (((((f : ↥S) : ↥F) : ↥E) : ↥J) : Fin d))) := by
      rw [hownerCoefficient (f : ↥F) f.property]
      exact hmuHeavy
    have hkLight : ¬ 2 ≤ coeff (((k : ↥S) : ↥F) : ↥E)
        (center (P.symm (((((k : ↥S) : ↥F) : ↥E) : ↥J) : Fin d))) := by
      rw [hownerCoefficient (k : ↥F) k.property]
      exact hmuHeavy
    exact
      fixedExternalCoefficientPrivateFiber_equalTarget_twoLight_twoRetained_false
        g hg y B center P scalar coeff F x lambda hfiber hrows
          f k hfkF htarget hfLight hkLight hretained

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

/-- On a fixed owner-coefficient profile in the exact-two regime, the
companion retained coefficient is the single integer `-(mu+lambda)` on every
selected row.  This is the zero coefficient-sum identity after the owner and
the two retained columns have been fixed. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_companionCoefficient
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2)
    (z : Fin n) (hzB : z ∉ B) (hzx : z ≠ x)
    (mu : ℤ) (S : Finset ↥F)
    (hS : S = Finset.univ.filter (fun f : ↥F ↦
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)) :
    ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) z = -(mu + lambda) := by
  classical
  intro f hfS
  have hmu : coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu := by
    rw [hS] at hfS
    exact (Finset.mem_filter.mp hfS).2
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_rowProfile
      g y B center P scalar coeff F x lambda hfiber hrows f hretained with
    ⟨zf, hzfB, hzfX, _hzero, hprofile⟩
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfiber.2.1⟩
  have hzC : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem hCcard hxC hzC hzx.symm
  have hzfC : zf ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzfB⟩
  have hzfPair : zf = x ∨ zf = z := by
    have : zf ∈ ({x, z} : Finset (Fin n)) := by
      rw [← hCeq]
      exact hzfC
    simpa using this
  have hzfEq : zf = z := hzfPair.resolve_left hzfX
  subst zf
  rcases hprofile with
      ⟨hlambda, ⟨howner, hz⟩ | ⟨howner, hz⟩ | ⟨howner, hz⟩⟩ |
      ⟨hlambda, howner, hz⟩ | ⟨hlambda, howner, hz⟩
  all_goals omega

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

/-- Selecting one owner coefficient turns the rowwise exact-two geometry into
one of five fully labelled signed/pure-edge profiles.  The companion
coordinate is supplied globally, so no row may choose a different retained
column. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_selectedRowGeometry
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2)
    (z : Fin n) (hzB : z ∉ B) (hzx : z ≠ x)
    (mu : ℤ) (f : ↥F)
    (hmu : coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) :
    (lambda = -1 ∧ mu = -1 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs z
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = -1 ∧ mu = 1 ∧
        ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
          (coeff ((f : ↥E) : ↥J))
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = -1 ∧ mu = 2 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z) ∨
      (lambda = 1 ∧ mu = -1 ∧
        ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
          (coeff ((f : ↥E) : ↥J))
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = 2 ∧ mu = -1 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs x
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) z) := by
  classical
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_signedPair_or_pureEdge
      g y B center P scalar coeff F x lambda hfiber hrows f hretained with
    ⟨zf, hzfB, hzfX, hgeometry⟩
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hxC : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfiber.2.1⟩
  have hzC : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem hCcard hxC hzC hzx.symm
  have hzfC : zf ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzfB⟩
  have hzfPair : zf = x ∨ zf = z := by
    have : zf ∈ ({x, z} : Finset (Fin n)) := by
      rw [← hCeq]
      exact hzfC
    simpa using this
  have hzfEq : zf = z := hzfPair.resolve_left hzfX
  subst zf
  let owner : Fin n := center (P.symm (((f : ↥E) : ↥J) : Fin d))
  have hownerB : owner ∈ B := by
    simpa [owner] using (hfiber.2.2.2.2.2.1 f).1
  have hownerX : owner ≠ x := by
    intro h
    subst x
    exact hfiber.2.1 hownerB
  have hownerZ : owner ≠ z := by
    intro h
    subst z
    exact hzB hownerB
  have hx : coeff ((f : ↥E) : ↥J) x = lambda :=
    (hfiber.2.2.2.2.2.1 f).2.1
  rcases hgeometry with
      ⟨hlambda, hleft | hsigned | hright⟩ |
      ⟨hlambda, hsigned⟩ | ⟨hlambda, hcenter⟩
  · left
    refine ⟨hlambda, ?_, hleft⟩
    have hownerValue : coeff ((f : ↥E) : ↥J) owner = -1 := by
      rw [hleft]
      simp [owner, pureEdgeCoeffs, hownerZ, hownerX]
    have hmu' : coeff ((f : ↥E) : ↥J) owner = mu := by
      simpa [owner] using hmu
    omega
  · right
    left
    rcases hsigned.2.1 with hforward | hreverse
    · exact ⟨hlambda, by omega, hsigned⟩
    · exfalso
      omega
  · right
    right
    left
    refine ⟨hlambda, ?_, hright⟩
    have hownerValue : coeff ((f : ↥E) : ↥J) owner = 2 := by
      rw [hright]
      simp [owner, pureEdgeCoeffs, hownerX, hownerZ]
    have hmu' : coeff ((f : ↥E) : ↥J) owner = mu := by
      simpa [owner] using hmu
    omega
  · right
    right
    right
    left
    rcases hsigned.2.1 with hforward | hreverse
    · exfalso
      omega
    · exact ⟨hlambda, by omega, hsigned⟩
  · right
    right
    right
    right
    refine ⟨hlambda, ?_, hcenter⟩
    have hownerValue : coeff ((f : ↥E) : ↥J) owner = -1 := by
      rw [hcenter]
      simp [owner, pureEdgeCoeffs, hownerX, hownerZ]
    have hmu' : coeff ((f : ↥E) : ↥J) owner = mu := by
      simpa [owner] using hmu
    omega

/-- Every row in one selected owner-coefficient fiber has one of the same
five labelled exact geometries.  The labels `lambda` and `mu`, and the
retained companion `z`, are fixed across the entire selected family. -/
def FixedExternalTwoRetainedSelectedGeometry
    (g : Fin n → G) (y : G)
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (S : Finset ↥F)
    (x z : Fin n) (lambda mu : ℤ) : Prop :=
  ∀ f : ↥F, f ∈ S →
    (lambda = -1 ∧ mu = -1 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs z
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = -1 ∧ mu = 1 ∧
        ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
          (coeff ((f : ↥E) : ↥J))
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = -1 ∧ mu = 2 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z) ∨
      (lambda = 1 ∧ mu = -1 ∧
        ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
          (coeff ((f : ↥E) : ↥J))
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
      (lambda = 2 ∧ mu = -1 ∧
        coeff ((f : ↥E) : ↥J) =
          pureEdgeCoeffs x
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) z)

/-- Lift the rowwise exact geometry to an arbitrary selected subfamily on
which the private-owner coefficient is constantly `mu`. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_selectedGeometry
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (S : Finset ↥F)
    (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2)
    (z : Fin n) (hzB : z ∉ B) (hzx : z ≠ x)
    (mu : ℤ)
    (hmu : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) :
    FixedExternalTwoRetainedSelectedGeometry
      g y center P scalar coeff F S x z lambda mu := by
  intro f hf
  exact fixedExternalCoefficientPrivateFiber_twoRetained_selectedRowGeometry
    g y B center P scalar coeff F x lambda hfiber hrows hretained
      z hzB hzx mu f (hmu f hf)

/-- The fixed labels make the rowwise five-way alternative uniform: a
nonempty selected family occupies one exact signed/pure-edge class globally,
not a row-dependent mixture of the five classes. -/
def FixedExternalTwoRetainedUniformGeometry
    (g : Fin n → G) (y : G)
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (S : Finset ↥F)
    (x z : Fin n) (lambda mu : ℤ) : Prop :=
  (lambda = -1 ∧ mu = -1 ∧ ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) =
        pureEdgeCoeffs z
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
    (lambda = -1 ∧ mu = 1 ∧ ∀ f : ↥F, f ∈ S →
      ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
        (coeff ((f : ↥E) : ↥J))
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
    (lambda = -1 ∧ mu = 2 ∧ ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) =
        pureEdgeCoeffs
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x z) ∨
    (lambda = 1 ∧ mu = -1 ∧ ∀ f : ↥F, f ∈ S →
      ExactSignedPairWitness g (scalar ((f : ↥E) : ↥J) • y)
        (coeff ((f : ↥E) : ↥J))
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) x) ∨
    (lambda = 2 ∧ mu = -1 ∧ ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) =
        pureEdgeCoeffs x
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) z)

/-- Collapse a rowwise selected geometry to one global case using any row of
the nonempty selected family to determine the two fixed labels. -/
theorem FixedExternalTwoRetainedSelectedGeometry.uniform
    (g : Fin n → G) (y : G)
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    {J : Finset (Fin d)} (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (S : Finset ↥F)
    (x z : Fin n) (lambda mu : ℤ)
    (hgeometry : FixedExternalTwoRetainedSelectedGeometry
      g y center P scalar coeff F S x z lambda mu)
    (hS : S.Nonempty) :
    FixedExternalTwoRetainedUniformGeometry
      g y center P scalar coeff F S x z lambda mu := by
  classical
  unfold FixedExternalTwoRetainedSelectedGeometry at hgeometry
  unfold FixedExternalTwoRetainedUniformGeometry
  obtain ⟨f₀, hf₀⟩ := hS
  rcases hgeometry f₀ hf₀ with hfirst | hsecond | hthird | hfourth | hfifth
  · left
    refine ⟨hfirst.1, hfirst.2.1, ?_⟩
    intro f hf
    rcases hgeometry f hf with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · exact hfirst'.2.2
    all_goals omega
  · right
    left
    refine ⟨hsecond.1, hsecond.2.1, ?_⟩
    intro f hf
    rcases hgeometry f hf with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · exact hsecond'.2.2
    all_goals omega
  · right
    right
    left
    refine ⟨hthird.1, hthird.2.1, ?_⟩
    intro f hf
    rcases hgeometry f hf with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · omega
    · exact hthird'.2.2
    all_goals omega
  · right
    right
    right
    left
    refine ⟨hfourth.1, hfourth.2.1, ?_⟩
    intro f hf
    rcases hgeometry f hf with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · omega
    · omega
    · exact hfourth'.2.2
    · omega
  · right
    right
    right
    right
    refine ⟨hfifth.1, hfifth.2.1, ?_⟩
    intro f hf
    rcases hgeometry f hf with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    all_goals try omega
    exact hfifth'.2.2

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

/-- Exact sign conditions inside the three-level exact-two alphabet. -/
theorem twoRetainedExternalCoefficientLevels_positive_cases
    {lambda mu : ℤ}
    (hlambda : lambda ∈ twoRetainedExternalCoefficientLevels)
    (hmu : mu ∈ twoRetainedExternalCoefficientLevels) :
    (1 ≤ lambda ↔ lambda = 1 ∨ lambda = 2) ∧
      (1 ≤ -(mu + lambda) ↔ mu = -1 ∧ lambda = -1) := by
  simp [twoRetainedExternalCoefficientLevels] at hlambda hmu
  omega

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

/-- A nonempty fixed external fiber has a dominant private-owner coefficient
profile.  The three-level alphabet gives `F.card ≤ 3 * S.card`, not merely a
profile above a preset threshold. -/
theorem fixedExternalCoefficientPrivateFiber_exists_dominantOwnerProfile
    (g : Fin n → G) (y : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2) (hF : F.Nonempty) :
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      let S := Finset.univ.filter (fun f : ↥F ↦
        coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
      S.Nonempty ∧ F.card ≤ 3 * S.card := by
  classical
  let ownerCoeff : ↥F → ℤ := fun f ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d)))
  have hownerMem : ∀ f : ↥F,
      ownerCoeff f ∈ twoRetainedExternalCoefficientLevels := by
    intro f
    exact fixedExternalCoefficientPrivateFiber_ownerCoefficient_mem_twoRetainedLevels
      g y B center P scalar coeff F x lambda hfiber hrows f hretained
  have hsource : (Finset.univ : Finset ↥F).Nonempty := by
    obtain ⟨f, hfF⟩ := hF
    exact ⟨(⟨f, hfF⟩ : ↥F), Finset.mem_univ _⟩
  obtain ⟨mu, hmu, hSnonempty, hSdominant⟩ :=
    finiteMap_exists_dominantFiber twoRetainedExternalCoefficientLevels
      ownerCoeff hownerMem hsource
  refine ⟨mu, hmu, by simpa [ownerCoeff] using hSnonempty, ?_⟩
  rw [card_twoRetainedExternalCoefficientLevels] at hSdominant
  simpa [ownerCoeff, Fintype.card_coe] using hSdominant

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

/-- Translation-normalized form of a dense affine external profile.  The
same selected rows have one global slope and offset as functions of the
translated private-owner coordinates. -/
def FixedExternalTwoRetainedRelativeAffineProfileAbove
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n)
    (K : ℕ) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      ∃ epsilon ∈ twoRetainedExternalCoefficientLevels, ∃ offset : G,
        K < (Finset.univ.filter (fun f : ↥F ↦
          coeff ((f : ↥E) : ↥J)
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)).card ∧
        ∀ f : ↥(Finset.univ.filter (fun f : ↥F ↦
            coeff ((f : ↥E) : ↥J)
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)),
          let o := center (P.symm (((((f : ↥F) : ↥E) : ↥J)) : Fin d))
          scalar (((f : ↥F) : ↥E) : ↥J) • y =
            epsilon • (g o - base) + offset

/-- Exact slope and translation offset attached to each of the five uniform
two-retained coefficient profiles.  In particular the affine slope is the
private-owner coefficient `mu`, not a separately chosen unit. -/
def FixedExternalTwoRetainedRelativeAffineParameters
    (g : Fin n → G) (base : G) (x z : Fin n)
    (lambda mu epsilon : ℤ) (offset : G) : Prop :=
  (lambda = -1 ∧ mu = -1 ∧ epsilon = mu ∧
      offset = 2 • g z - g x - base) ∨
    (lambda = -1 ∧ mu = 1 ∧ epsilon = mu ∧
      offset = base - g x) ∨
    (lambda = -1 ∧ mu = 2 ∧ epsilon = mu ∧
      offset = 2 • base - g x - g z) ∨
    (lambda = 1 ∧ mu = -1 ∧ epsilon = mu ∧
      offset = g x - base) ∨
    (lambda = 2 ∧ mu = -1 ∧ epsilon = mu ∧
      offset = 2 • g x - g z - base)

/-- The homogeneous affine slope in every exact parameter profile is the
selected private-owner coefficient. -/
theorem FixedExternalTwoRetainedRelativeAffineParameters.slope_eq
    (g : Fin n → G) (base : G) (x z : Fin n)
    (lambda mu epsilon : ℤ) (offset : G)
    (hparameters : FixedExternalTwoRetainedRelativeAffineParameters
      g base x z lambda mu epsilon offset) :
    epsilon = mu := by
  rcases hparameters with hfirst | hsecond | hthird | hfourth | hfifth
  · exact hfirst.2.2.1
  · exact hsecond.2.2.1
  · exact hthird.2.2.1
  · exact hfourth.2.2.1
  · exact hfifth.2.2.1

/-- If an affine target and its homogeneous displacement both lie in the
cyclic subgroup generated by `y`, then so does the affine offset. -/
theorem affineOffset_mem_zmultiples
    (y offset : G) {α : Type*} (displacement : α → G)
    (mu scalar : ℤ) (i : α)
    (hdisplacement : displacement i ∈ AddSubgroup.zmultiples y)
    (haffine : scalar • y = mu • displacement i + offset) :
    offset ∈ AddSubgroup.zmultiples y := by
  have htarget : scalar • y ∈ AddSubgroup.zmultiples y :=
    (AddSubgroup.zmultiples y).zsmul_mem
      (AddSubgroup.mem_zmultiples y) scalar
  have hhomogeneous : mu • displacement i ∈ AddSubgroup.zmultiples y :=
    (AddSubgroup.zmultiples y).zsmul_mem hdisplacement mu
  have hsub := (AddSubgroup.zmultiples y).sub_mem htarget hhomogeneous
  have heq : scalar • y - mu • displacement i = offset := by
    rw [haffine]
    abel
  rwa [heq] at hsub

/-- Dominant translation-normalized affine profile.  It retains the same
homogeneous owner law as `FixedExternalTwoRetainedRelativeAffineProfileAbove`
and additionally controls the whole fixed external fiber by three copies of
the selected owner-coefficient profile. -/
def FixedExternalTwoRetainedDominantRelativeAffineProfile
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      ∃ epsilon ∈ twoRetainedExternalCoefficientLevels, ∃ offset : G,
        FixedExternalTwoRetainedRelativeAffineParameters
            g base x z lambda mu epsilon offset ∧
        let S := Finset.univ.filter (fun f : ↥F ↦
          coeff ((f : ↥E) : ↥J)
            (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
        S.Nonempty ∧ F.card ≤ 3 * S.card ∧
          ∀ f : ↥S,
            let o := center (P.symm (((((f : ↥F) : ↥E) : ↥J)) : Fin d))
            scalar (((f : ↥F) : ↥E) : ↥J) • y =
              epsilon • (g o - base) + offset

/-- Each of the five exact affine profiles has one fixed slope and offset
after translating owner values by an arbitrary base.  The slope still lies
in `{-1,1,2}`, so it is invertible in every odd-primary projection. -/
theorem FixedExternalTwoRetainedAffineProfileAbove.relative
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (K : ℕ)
    (hprofile : FixedExternalTwoRetainedAffineProfileAbove
      g y B center P scalar coeff F x lambda K) :
    FixedExternalTwoRetainedRelativeAffineProfileAbove
      g y base B center P scalar coeff F x K := by
  classical
  rcases hprofile with
    ⟨z, hzB, hzx, mu, hmuLevel, hlarge, haffine⟩
  let S : Finset ↥F := Finset.univ.filter (fun f : ↥F ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
  have hSnonempty : S.Nonempty := by
    apply Finset.card_pos.mp
    simpa [S] using lt_of_le_of_lt (Nat.zero_le K) hlarge
  obtain ⟨f₀, hf₀S⟩ := hSnonempty
  let f₀' : ↥S := ⟨f₀, hf₀S⟩
  have hf₀ := haffine f₀'
  rcases hf₀ with hfirst | hsecond | hthird | hfourth | hfifth
  · refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • g z - g x - base, by simpa [S] using hlarge, ?_⟩
    intro f
    rcases haffine f with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · rw [hfirst'.2.2]
      simp
      abel
    · omega
    · omega
    · omega
    · omega
  · refine ⟨z, hzB, hzx, mu, hmuLevel, 1,
      by simp [twoRetainedExternalCoefficientLevels],
      base - g x, by simpa [S] using hlarge, ?_⟩
    intro f
    rcases haffine f with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · rw [hsecond'.2.2]
      simp
    · omega
    · omega
    · omega
  · refine ⟨z, hzB, hzx, mu, hmuLevel, 2,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • base - g x - g z, by simpa [S] using hlarge, ?_⟩
    intro f
    rcases haffine f with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · omega
    · rw [hthird'.2.2]
      simp [two_zsmul, two_nsmul]
      abel
    · omega
    · omega
  · refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      g x - base, by simpa [S] using hlarge, ?_⟩
    intro f
    rcases haffine f with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · omega
    · omega
    · rw [hfourth'.2.2]
      simp
    · omega
  · refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • g x - g z - base, by simpa [S] using hlarge, ?_⟩
    intro f
    rcases haffine f with hfirst' | hsecond' | hthird' | hfourth' | hfifth'
    · omega
    · omega
    · omega
    · omega
    · rw [hfifth'.2.2]
      simp
      abel

/-- Dominant owner-profile extraction preserves the exact translated affine
law.  The selected profile pays for the whole fixed external fiber with the
constant-three bound. -/
theorem fixedExternalCoefficientPrivateFiber_twoRetained_dominantRelativeProfile
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n) (lambda : ℤ)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hrows : ∀ j, Witness g (scalar j • y) (coeff j))
    (hretained : n - B.card = 2) (hF : F.Nonempty) :
    FixedExternalTwoRetainedDominantRelativeAffineProfile
      g y base B center P scalar coeff F x lambda := by
  classical
  unfold FixedExternalTwoRetainedDominantRelativeAffineProfile
  rcases fixedExternalCoefficientPrivateFiber_twoRetained_familyAffineTargets
      g y B center P scalar coeff F x lambda hfiber hrows hretained with
    ⟨z, hzB, hzx, haffine⟩
  rcases fixedExternalCoefficientPrivateFiber_exists_dominantOwnerProfile
      g y B center P scalar coeff F x lambda hfiber hrows hretained hF with
    ⟨mu, hmuLevel, hSnonempty, hSdominant⟩
  let ownerCoeff : ↥F → ℤ := fun f ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d)))
  let S : Finset ↥F := Finset.univ.filter fun f ↦ ownerCoeff f = mu
  have hSnonempty' : S.Nonempty := by
    simpa [S, ownerCoeff] using hSnonempty
  have hSdominant' : F.card ≤ 3 * S.card := by
    simpa [S, ownerCoeff] using hSdominant
  have hSnonemptyOut : S.Nonempty := hSnonempty'
  obtain ⟨f₀, hf₀S⟩ := hSnonempty'
  let f₀' : ↥S := ⟨f₀, hf₀S⟩
  have hmu₀ : ownerCoeff (f₀' : ↥F) = mu :=
    (Finset.mem_filter.mp f₀'.property).2
  rcases haffine (f₀' : ↥F) with
      ⟨hlambda, ⟨howner, htarget⟩ |
        ⟨howner, htarget⟩ | ⟨howner, htarget⟩⟩ |
      ⟨hlambda, howner, htarget⟩ |
      ⟨hlambda, howner, htarget⟩
  · have hmuValue : mu = -1 := by
      simpa [ownerCoeff] using hmu₀.symm.trans howner
    refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • g z - g x - base,
      Or.inl ⟨hlambda, hmuValue, hmuValue.symm, rfl⟩,
      by simpa [S, ownerCoeff] using hSnonemptyOut,
      by simpa [S, ownerCoeff] using hSdominant', ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    dsimp only [ownerCoeff] at hmu
    rcases haffine (f : ↥F) with
        ⟨hlambda', ⟨howner', htarget'⟩ |
          ⟨howner', htarget'⟩ | ⟨howner', htarget'⟩⟩ |
        ⟨hlambda', howner', htarget'⟩ |
        ⟨hlambda', howner', htarget'⟩
    · rw [htarget']
      simp
      abel
    all_goals omega
  · have hmuValue : mu = 1 := by
      simpa [ownerCoeff] using hmu₀.symm.trans howner
    refine ⟨z, hzB, hzx, mu, hmuLevel, 1,
      by simp [twoRetainedExternalCoefficientLevels],
      base - g x,
      Or.inr (Or.inl ⟨hlambda, hmuValue, hmuValue.symm, rfl⟩),
      by simpa [S, ownerCoeff] using hSnonemptyOut,
      by simpa [S, ownerCoeff] using hSdominant', ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    dsimp only [ownerCoeff] at hmu
    rcases haffine (f : ↥F) with
        ⟨hlambda', ⟨howner', htarget'⟩ |
          ⟨howner', htarget'⟩ | ⟨howner', htarget'⟩⟩ |
        ⟨hlambda', howner', htarget'⟩ |
        ⟨hlambda', howner', htarget'⟩
    · omega
    · rw [htarget']
      simp
    all_goals omega
  · have hmuValue : mu = 2 := by
      simpa [ownerCoeff] using hmu₀.symm.trans howner
    refine ⟨z, hzB, hzx, mu, hmuLevel, 2,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • base - g x - g z,
      Or.inr (Or.inr (Or.inl
        ⟨hlambda, hmuValue, hmuValue.symm, rfl⟩)),
      by simpa [S, ownerCoeff] using hSnonemptyOut,
      by simpa [S, ownerCoeff] using hSdominant', ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    dsimp only [ownerCoeff] at hmu
    rcases haffine (f : ↥F) with
        ⟨hlambda', ⟨howner', htarget'⟩ |
          ⟨howner', htarget'⟩ | ⟨howner', htarget'⟩⟩ |
        ⟨hlambda', howner', htarget'⟩ |
        ⟨hlambda', howner', htarget'⟩
    · omega
    · omega
    · rw [htarget']
      simp [two_zsmul, two_nsmul]
      abel
    all_goals omega
  · have hmuValue : mu = -1 := by
      simpa [ownerCoeff] using hmu₀.symm.trans howner
    refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      g x - base,
      Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hlambda, hmuValue, hmuValue.symm, rfl⟩))),
      by simpa [S, ownerCoeff] using hSnonemptyOut,
      by simpa [S, ownerCoeff] using hSdominant', ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    dsimp only [ownerCoeff] at hmu
    rcases haffine (f : ↥F) with
        ⟨hlambda', ⟨howner', htarget'⟩ |
          ⟨howner', htarget'⟩ | ⟨howner', htarget'⟩⟩ |
        ⟨hlambda', howner', htarget'⟩ |
        ⟨hlambda', howner', htarget'⟩
    all_goals try omega
    rw [htarget']
    simp
  · have hmuValue : mu = -1 := by
      simpa [ownerCoeff] using hmu₀.symm.trans howner
    refine ⟨z, hzB, hzx, mu, hmuLevel, -1,
      by simp [twoRetainedExternalCoefficientLevels],
      2 • g x - g z - base,
      Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hlambda, hmuValue, hmuValue.symm, rfl⟩))),
      by simpa [S, ownerCoeff] using hSnonemptyOut,
      by simpa [S, ownerCoeff] using hSdominant', ?_⟩
    intro f
    have hmu : ownerCoeff (f : ↥F) = mu :=
      (Finset.mem_filter.mp f.property).2
    dsimp only [ownerCoeff] at hmu
    rcases haffine (f : ↥F) with
        ⟨hlambda', ⟨howner', htarget'⟩ |
          ⟨howner', htarget'⟩ | ⟨howner', htarget'⟩⟩ |
        ⟨hlambda', howner', htarget'⟩ |
        ⟨hlambda', howner', htarget'⟩
    all_goals try omega
    rw [htarget']
    simp
    abel

/-- The owner map of every selected fixed-external row family is injective.
This is structural: all successive row types are subtypes of the original
cycle-index set, so lifting boundary owners and successors loses no rows. -/
theorem fixedExternalSelectedOwner_injective
    {d : ℕ} {J : Finset (Fin d)} {E : Finset ↥J}
    {F : Finset ↥E} (S : Finset ↥F) :
    Function.Injective (fun f : ↥S ↦
      (((f : ↥F) : ↥E) : ↥J) : ↥S → Fin d) := by
  intro f k h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Concrete first-failure split for the selected fixed-external affine rows.
A boundary successor either leaves the retained row set, enters the internal
class, changes its external coordinate/coefficient label, or keeps that label
and changes the private-owner coefficient profile. -/
theorem fixedExternalBoundaryRow_successor_transition
    {n d : ℕ} (R : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (E I : Finset ↥J)
    (hpartition : E ∪ I = Finset.univ)
    (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (supportCoord : ↥E → Fin n) (coeff : ↥J → Fin n → ℤ)
    (fixedLabel : Fin n × ℤ)
    (F : Finset ↥E)
    (hF : F = Finset.univ.filter (fun e ↦
      (supportCoord e, coeff (e : ↥J) (supportCoord e)) = fixedLabel))
    (mu : ℤ) (S : Finset ↥F)
    (hS : S = Finset.univ.filter (fun f : ↥F ↦
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu))
    (s : ↥(permutationFamilyBoundaryRows R (nestedSelectedOwner S))) :
    R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : Fin d) ∉ J ∨
      (∃ i : ↥I, ((i : ↥J) : Fin d) =
        R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : Fin d)) ∨
      (∃ e : ↥E, ((e : ↥J) : Fin d) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : Fin d) ∧
        (supportCoord e, coeff (e : ↥J) (supportCoord e)) ≠ fixedLabel) ∨
      ∃ f : ↥F, (((f : ↥E) : ↥J) : Fin d) =
          R (((((s : ↥S) : ↥F) : ↥E) : ↥J) : Fin d) ∧
        coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) ≠ mu := by
  exact nestedFilteredBoundaryRow_successor_transition
    R J E I hpartition
      (fun e ↦ (supportCoord e, coeff (e : ↥J) (supportCoord e)))
      fixedLabel F hF
      (fun f ↦ coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))))
      mu S hS s

/-- Named payload for the occupied relative-cycle frontier of a dense
external affine profile. -/
def FixedExternalTwoRetainedRelativeAffineCycleComponentFrontierAbove
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P R : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n)
    (profileThreshold componentThreshold : ℕ) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      ∃ epsilon ∈ twoRetainedExternalCoefficientLevels, ∃ offset : G,
        ∃ S : Finset ↥F,
          S = Finset.univ.filter (fun f : ↥F ↦
            coeff ((f : ↥E) : ↥J)
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) ∧
          profileThreshold < S.card ∧
          let owner : ↥S → Fin d := fun f ↦
            (((f : ↥F) : ↥E) : ↥J)
          let displacement : Fin d → G := fun j ↦
            g (center (P.symm j)) - base
          let target : ↥S → G := fun f ↦
            scalar (((f : ↥F) : ↥E) : ↥J) • y
          Function.Injective owner ∧
            (∀ f, target f = epsilon • displacement (owner f) + offset) ∧
            ((profileThreshold <
                  (permutationFamilyComponents R owner).card * componentThreshold ∧
                profileThreshold <
                  ((permutationSubsetFullComponents R
                      (permutationFamilyOwnerSet owner)).card +
                    (permutationSubsetBoundary R
                      (permutationFamilyOwnerSet owner)).card) *
                    componentThreshold) ∨
              ∃ C ∈ permutationFamilyComponents R owner,
                componentThreshold <
                    (permutationFamilyComponentFiber R owner C).card ∧
                ∀ u v : ↥(permutationFamilyComponentFiber R owner C),
                  ∃ k : ℕ, target (v : ↥S) - target (u : ↥S) =
                    epsilon • ((2 ^ k - 1) •
                      displacement (owner (u : ↥S))))

/-- A translation-normalized external profile satisfies the exact occupied
relative-cycle frontier.  In the large-component arm every two retained rows
carry the componentwise Mersenne target comparison, while all profile data
and the original dense selected set are preserved. -/
theorem FixedExternalTwoRetainedRelativeAffineProfileAbove.cycleComponentFrontier
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (F : Finset ↥E) (x : Fin n)
    (profileThreshold componentThreshold : ℕ)
    (hprofile : FixedExternalTwoRetainedRelativeAffineProfileAbove
      g y base B center P scalar coeff F x profileThreshold)
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j,
      g (center (P.symm (R j))) - base =
        2 • (g (center (P.symm j)) - base)) :
    FixedExternalTwoRetainedRelativeAffineCycleComponentFrontierAbove
      g y base B center P R scalar coeff F x
        profileThreshold componentThreshold := by
  classical
  unfold FixedExternalTwoRetainedRelativeAffineCycleComponentFrontierAbove
  rcases hprofile with
    ⟨z, hzB, hzx, mu, hmuLevel, epsilon, hepsilonLevel, offset,
      hlarge, haffine⟩
  let S : Finset ↥F := Finset.univ.filter (fun f : ↥F ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
  let owner : ↥S → Fin d := fun f ↦ (((f : ↥F) : ↥E) : ↥J)
  let displacement : Fin d → G := fun j ↦
    g (center (P.symm j)) - base
  let target : ↥S → G := fun f ↦
    scalar (((f : ↥F) : ↥E) : ↥J) • y
  have hlarge' : profileThreshold < S.card := by
    simpa [S] using hlarge
  have hdouble' : ∀ j, displacement (R j) = 2 • displacement j := by
    simpa [displacement] using hdouble
  have haffine' : ∀ f, target f =
      epsilon • displacement (owner f) + offset := by
    intro f
    simpa [S, owner, displacement, target] using haffine f
  have hfrontier := permutationFamily_large_affineComponentFrontier
    R owner displacement target hdouble' epsilon offset haffine'
      profileThreshold componentThreshold (by
        simpa [Fintype.card_coe] using hlarge')
  refine ⟨z, hzB, hzx, mu, hmuLevel, epsilon, hepsilonLevel, offset,
    S, rfl, hlarge', ?_⟩
  refine ⟨by simpa [owner] using fixedExternalSelectedOwner_injective S,
    haffine', ?_⟩
  rcases hfrontier with hcomponents | hcomponent
  · left
    refine ⟨by simpa [owner] using hcomponents, ?_⟩
    have hcard := card_permutationFamilyComponents_le_full_add_boundary
      R owner
    have hbound := hcomponents.trans_le
      (Nat.mul_le_mul_right componentThreshold hcard)
    simpa [owner] using hbound
  · right
    simpa [owner, displacement, target] using hcomponent

/-- Dominant-profile version of the relative cycle frontier.  Besides the
exact affine and Mersenne laws, it retains the two global dominance bounds as
one quantitative boundary charge and records the exact successor recurrence
on every full selected component. -/
def FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier
    (g : Fin n → G) (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P R : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (I : Finset ↥J) (F : Finset ↥E) (x : Fin n)
    (lambda : ℤ) (componentThreshold : ℕ) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ x ∧
    lambda ∈ twoRetainedExternalCoefficientLevels ∧
    ∃ mu ∈ twoRetainedExternalCoefficientLevels,
      ∃ epsilon ∈ twoRetainedExternalCoefficientLevels, ∃ offset : G,
        FixedExternalTwoRetainedRelativeAffineParameters
            g base x z lambda mu epsilon offset ∧
        ∃ rho : ℤ, rho • y = offset ∧
        ∃ S : Finset ↥F,
          S = Finset.univ.filter (fun f : ↥F ↦
            coeff ((f : ↥E) : ↥J)
              (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) ∧
          S.Nonempty ∧ F.card ≤ 3 * S.card ∧
          let owner : ↥S → Fin d := fun f ↦
            (((f : ↥F) : ↥E) : ↥J)
          let displacement : Fin d → G := fun j ↦
            g (center (P.symm j)) - base
          let target : ↥S → G := fun f ↦
            scalar (((f : ↥F) : ↥E) : ↥J) • y
          Function.Injective owner ∧
            (∀ f, target f = mu • displacement (owner f) + offset) ∧
            S.card ≤ addOrderOf y - 1 ∧
            d - 1 < 36 * (addOrderOf y - 1) ∧
            (permutationFamilyBoundaryRows R owner).card ≤
              (Finset.univ \ J).card + I.card + 17 * S.card ∧
            (permutationFamilyBoundaryRows R owner).card ≤ 35 * S.card ∧
            d - 1 < 36 * S.card ∧
            (∀ w : Fin n,
              1 < (fixedExternalFiberPositiveRowsAt coeff S w).card →
                w = x ∨ w = z) ∧
            (∀ f : ↥F, f ∈ S →
              coeff ((f : ↥E) : ↥J) x = lambda ∧
              coeff ((f : ↥E) : ↥J) z = -(mu + lambda)) ∧
            fixedExternalFiberPositiveRowsAt coeff S x =
              (if 1 ≤ lambda then S else ∅) ∧
            fixedExternalFiberPositiveRowsAt coeff S z =
              (if 1 ≤ -(mu + lambda) then S else ∅) ∧
            FixedExternalTwoRetainedUniformGeometry
              g y center P scalar coeff F S x z lambda mu ∧
            (∀ (C : Quotient (Equiv.Perm.SameCycle.setoid R))
                (_hC : C ∈ permutationSubsetFullComponents R
                  (permutationFamilyOwnerSet owner))
                (i : ↥S)
                (_hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R)
                  (owner i) = C),
              ∃! j : ↥S, owner j = R (owner i) ∧
                Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner j) = C ∧
                target j - offset = 2 • (target i - offset) ∧
                (scalar (((j : ↥F) : ↥E) : ↥J) - rho) • y =
                  2 • ((scalar (((i : ↥F) : ↥E) : ↥J) - rho) • y)) ∧
            (∀ (C : Quotient (Equiv.Perm.SameCycle.setoid R))
                (_hC : C ∈ permutationSubsetFullComponents R
                  (permutationFamilyOwnerSet owner)),
              ∃ Q : Equiv.Perm
                  ↥(permutationFamilyComponentFiber R owner C),
                (∀ i, owner (Q i : ↥S) = R (owner (i : ↥S))) ∧
                (∀ i,
                  (scalar ((((Q i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y =
                    2 • ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y)) ∧
                Q.IsCycle ∧
                (∃ i : ↥(permutationFamilyComponentFiber R owner C),
                  (scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y ≠ 0 ∧
                  addOrderOf
                      ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) ∣
                    2 ^ (permutationFamilyComponentFiber R owner C).card - 1 ∧
                  addOrderOf
                      ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) ∣
                    addOrderOf y ∧
                  (permutationFamilyComponentFiber R owner C).card ≤
                    addOrderOf
                      ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) - 1 ∧
                  (permutationFamilyComponentFiber R owner C).card ≤
                    addOrderOf y - 1) ∧
                ∃ i, ∃ ell : ℕ,
                  2 ≤ ell ∧ ell ≤ d ∧ Q^[ell] i = i ∧
                    Odd (2 ^ ell - 1) ∧
                    (2 ^ ell - 1) •
                      ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) = 0) ∧
            (S.card ≤
                  ((permutationSubsetFullComponents R
                      (permutationFamilyOwnerSet owner)).card +
                    (permutationSubsetBoundary R
                      (permutationFamilyOwnerSet owner)).card) *
                    (addOrderOf y - 1) ∨
              ∃ C ∈ permutationFamilyComponents R owner,
                addOrderOf y - 1 <
                    (permutationFamilyComponentFiber R owner C).card ∧
                C ∉ permutationSubsetFullComponents R
                  (permutationFamilyOwnerSet owner) ∧
                ∃ s : ↥(permutationFamilyBoundaryRows R owner),
                  Quotient.mk (Equiv.Perm.SameCycle.setoid R)
                      (owner (s : ↥S)) = C ∧
                    NestedBoundaryRowSuccessorTransition
                      R J E I F S owner s) ∧
            ((S.card ≤
                  (permutationFamilyComponents R owner).card *
                    componentThreshold ∧
                S.card ≤
                  ((permutationSubsetFullComponents R
                      (permutationFamilyOwnerSet owner)).card +
                    (permutationSubsetBoundary R
                      (permutationFamilyOwnerSet owner)).card) *
                    componentThreshold) ∨
              ∃ C ∈ permutationFamilyComponents R owner,
                componentThreshold <
                    (permutationFamilyComponentFiber R owner C).card ∧
                ∀ u v : ↥(permutationFamilyComponentFiber R owner C),
                  ∃ k : ℕ, target (v : ↥S) - target (u : ↥S) =
                    mu • ((2 ^ k - 1) •
                      displacement (owner (u : ↥S))))

set_option maxHeartbeats 500000 in
/-- A dominant translated affine profile, together with the global outer
label dominance, satisfies the quantitative boundary/full-component cycle
frontier for the very same selected set. -/
theorem FixedExternalTwoRetainedDominantRelativeAffineProfile.cycleComponentFrontier
    [Fintype G] [DecidableEq G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y base : G)
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    {E : Finset ↥J} (I : Finset ↥J) (F : Finset ↥E) (x : Fin n)
    (lambda : ℤ)
    (hlambdaLevel : lambda ∈ twoRetainedExternalCoefficientLevels)
    (hfiber : FixedExternalCoefficientPrivateFiber
      B center P coeff F x lambda)
    (hretained : n - B.card = 2)
    (hrows : ∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j))
    (hJcard : d - 1 ≤ J.card)
    (hpartition : E ∪ I = Finset.univ)
    (hlarge : d - 1 ≤ E.card + I.card)
    (hFdominant : E.card ≤ 6 * F.card)
    (hIsparse : 2 * I.card < d - 1)
    (hprofile : FixedExternalTwoRetainedDominantRelativeAffineProfile
      g y base B center P scalar coeff F x lambda)
    (R : Equiv.Perm (Fin d))
    (hRne : ∀ j, R j ≠ j)
    (hdouble : ∀ j,
      g (center (P.symm (R j))) - base =
        2 • (g (center (P.symm j)) - base))
    (hdisplacement : ∀ j,
      g (center (P.symm j)) - base ∈ AddSubgroup.zmultiples y)
    (componentThreshold : ℕ) :
    FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier
      g y base B center P R scalar coeff I F x lambda
        componentThreshold := by
  classical
  unfold FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier
  rcases hprofile with
    ⟨z, hzB, hzx, mu, hmuLevel, epsilon, hepsilonLevel, offset, hparameters,
      hSnonempty, hSdominant, haffine⟩
  let S : Finset ↥F := Finset.univ.filter (fun f : ↥F ↦
    coeff ((f : ↥E) : ↥J)
      (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu)
  let owner : ↥S → Fin d := fun f ↦ (((f : ↥F) : ↥E) : ↥J)
  let displacement : Fin d → G := fun j ↦
    g (center (P.symm j)) - base
  let target : ↥S → G := fun f ↦
    scalar (((f : ↥F) : ↥E) : ↥J) • y
  have hSnonempty' : S.Nonempty := by
    simpa [S] using hSnonempty
  have hSdominant' : F.card ≤ 3 * S.card := by
    simpa [S] using hSdominant
  have howner : Function.Injective owner := by
    simpa [owner] using fixedExternalSelectedOwner_injective S
  have hdouble' : ∀ j, displacement (R j) = 2 • displacement j := by
    simpa [displacement] using hdouble
  have hdisplacement' : ∀ j,
      displacement j ∈ AddSubgroup.zmultiples y := by
    simpa [displacement] using hdisplacement
  have haffine' : ∀ f, target f =
      epsilon • displacement (owner f) + offset := by
    intro f
    simpa [S, owner, displacement, target] using haffine f
  have hepsilonMu : epsilon = mu :=
    hparameters.slope_eq g base x z lambda mu epsilon offset
  have haffineMu : ∀ f, target f =
      mu • displacement (owner f) + offset := by
    intro f
    rw [← hepsilonMu]
    exact haffine' f
  have hSnonemptyOut : S.Nonempty := hSnonempty'
  obtain ⟨f₀, hf₀⟩ := hSnonempty'
  let f₀' : ↥S := ⟨f₀, hf₀⟩
  have hoffset : offset ∈ AddSubgroup.zmultiples y :=
    affineOffset_mem_zmultiples y offset displacement mu
      (scalar (((f₀' : ↥F) : ↥E) : ↥J)) (owner f₀')
      (hdisplacement' (owner f₀')) (by
        simpa [target] using haffineMu f₀')
  obtain ⟨rho, hrho⟩ := AddSubgroup.mem_zmultiples_iff.mp hoffset
  have hboundary : (permutationFamilyBoundaryRows R owner).card ≤
      (Finset.univ \ J).card + I.card + 17 * S.card := by
    have hownerEq : owner = nestedSelectedOwner S := by
      rfl
    rw [hownerEq]
    exact card_nestedSelectedBoundaryRows_le_outer_add_internal_add_seventeen
      R J E I hpartition F S hFdominant hSdominant'
  have hboundaryRouted : (permutationFamilyBoundaryRows R owner).card ≤
      35 * S.card := by
    have hownerEq : owner = nestedSelectedOwner S := by
      rfl
    rw [hownerEq]
    exact card_nestedSelectedBoundaryRows_le_thirty_five_mul
      R J E I hJcard hpartition hlarge F S hFdominant hSdominant'
        hIsparse
  have hdense : d - 1 < 36 * S.card :=
    (twoStageDominance_internalSparse_bounds
      d E I F S hlarge hFdominant hSdominant' hIsparse).2
  have hpositive : ∀ w : Fin n,
      1 < (fixedExternalFiberPositiveRowsAt coeff S w).card →
        w = x ∨ w = z := by
    intro w hw
    exact fixedExternalFiberPositiveRowsAt_large_eq_fixed_or_companion
      B center P coeff F x lambda hfiber hretained z hzB hzx S w hw
  have hcompanion : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) z = -(mu + lambda) :=
    fixedExternalCoefficientPrivateFiber_twoRetained_companionCoefficient
      g y B center P scalar coeff F x lambda hfiber
        (fun j ↦ (hrows j).2) hretained
        z hzB hzx mu S rfl
  have hxconstant : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) x = lambda := by
    intro f _hf
    exact (hfiber.2.2.2.2.2.1 f).2.1
  have hcolumns : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J) x = lambda ∧
      coeff ((f : ↥E) : ↥J) z = -(mu + lambda) := by
    intro f hf
    exact ⟨hxconstant f hf, hcompanion f hf⟩
  have hxPositive : fixedExternalFiberPositiveRowsAt coeff S x =
      if 1 ≤ lambda then S else ∅ :=
    fixedExternalFiberPositiveRowsAt_eq_self_or_empty_of_constant
      coeff S x lambda hxconstant
  have hzPositive : fixedExternalFiberPositiveRowsAt coeff S z =
      if 1 ≤ -(mu + lambda) then S else ∅ :=
    fixedExternalFiberPositiveRowsAt_eq_self_or_empty_of_constant
      coeff S z (-(mu + lambda)) hcompanion
  have hgeometry : FixedExternalTwoRetainedSelectedGeometry
      g y center P scalar coeff F S x z lambda mu :=
    fixedExternalCoefficientPrivateFiber_twoRetained_selectedGeometry
      g y B center P scalar coeff F S x lambda hfiber
        (fun j ↦ (hrows j).2) hretained
        z hzB hzx mu (by
          intro f hf
          have hf' : f ∈ Finset.univ.filter (fun f : ↥F ↦
              coeff ((f : ↥E) : ↥J)
                (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) := by
            simpa [S] using hf
          exact (Finset.mem_filter.mp hf').2)
  have huniform : FixedExternalTwoRetainedUniformGeometry
      g y center P scalar coeff F S x z lambda mu :=
    hgeometry.uniform g y center P scalar coeff F S x z lambda mu
      hSnonemptyOut
  have hfullTarget : ∀ (C : Quotient (Equiv.Perm.SameCycle.setoid R))
      (hC : C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner))
      (i : ↥S)
      (hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C),
      ∃! j : ↥S, owner j = R (owner i) ∧
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner j) = C ∧
        target j - offset = 2 • (target i - offset) := by
    intro C hC i hiC
    exact permutationFamilyFullComponent_uniqueSuccessorRow_affine
      R owner displacement target howner hdouble' mu offset haffineMu
        C hC i hiC
  have hfull : ∀ (C : Quotient (Equiv.Perm.SameCycle.setoid R))
      (hC : C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner))
      (i : ↥S)
      (hiC : Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C),
      ∃! j : ↥S, owner j = R (owner i) ∧
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner j) = C ∧
        target j - offset = 2 • (target i - offset) ∧
        (scalar (((j : ↥F) : ↥E) : ↥J) - rho) • y =
          2 • ((scalar (((i : ↥F) : ↥E) : ↥J) - rho) • y) := by
    intro C hC i hiC
    rcases hfullTarget C hC i hiC with ⟨j, hj, hjUnique⟩
    refine ⟨j, ⟨hj.1, hj.2.1, hj.2.2, ?_⟩, ?_⟩
    · have hrecurrence := hj.2.2
      dsimp [target] at hrecurrence
      rw [← hrho] at hrecurrence
      simpa only [sub_smul] using hrecurrence
    · intro k hk
      exact hjUnique k ⟨hk.1, hk.2.1, hk.2.2.1⟩
  let centered : ↥F → G := fun f ↦
    (scalar ((f : ↥E) : ↥J) - rho) • y
  have hownerCoefficient : ∀ f : ↥F, f ∈ S →
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu := by
    intro f hf
    have hf' : f ∈ Finset.univ.filter (fun f : ↥F ↦
        coeff ((f : ↥E) : ↥J)
          (center (P.symm (((f : ↥E) : ↥J) : Fin d))) = mu) := by
      simpa [S] using hf
    exact (Finset.mem_filter.mp hf').2
  have htargetInjective : Function.Injective (fun f : ↥S ↦
      scalar ((((f : ↥F) : ↥E) : ↥J)) • y) :=
    fixedExternalCoefficientPrivateFiber_fixedOwnerCoefficient_target_injective
      g hg hh hne hunique hno y B center P scalar coeff F x lambda mu
        hfiber hrows S hownerCoefficient (by omega)
  have hselectedOrderBound : S.card ≤ addOrderOf y - 1 := by
    have hcard :=
      card_le_addOrderOf_sub_one_of_injective_nonzero_zsmul y
        (fun f : ↥S ↦ scalar ((((f : ↥F) : ↥E) : ↥J)))
        (fun f ↦ hrows ((((f : ↥F) : ↥E) : ↥J)) |>.1)
        htargetInjective
    simpa only [Fintype.card_coe] using hcard
  have hdimensionOrderBound : d - 1 < 36 * (addOrderOf y - 1) :=
    hdense.trans_le (Nat.mul_le_mul_left 36 hselectedOrderBound)
  have hcenteredInjective : Function.Injective (fun f : ↥S ↦
      centered (f : ↥F)) := by
    intro f k hcentered
    apply htargetInjective
    have heq := congrArg (fun u : G ↦ u + rho • y) hcentered
    simpa only [centered, sub_smul, sub_add_cancel] using heq
  have hcenteredMultiplicity : ∀ v : G,
      (S.filter (fun f ↦ centered f = v)).card ≤ 1 := by
    intro v
    rw [Finset.card_le_one]
    intro f hf k hk
    let f' : ↥S := ⟨f, (Finset.mem_filter.mp hf).1⟩
    let k' : ↥S := ⟨k, (Finset.mem_filter.mp hk).1⟩
    have hfk : f' = k' := hcenteredInjective (by
      exact (Finset.mem_filter.mp hf).2.trans
        (Finset.mem_filter.mp hk).2.symm)
    exact congrArg Subtype.val hfk
  have hfullCycle : ∀
      (C : Quotient (Equiv.Perm.SameCycle.setoid R))
      (hC : C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner)),
      ∃ Q : Equiv.Perm
          ↥(permutationFamilyComponentFiber R owner C),
        (∀ i, owner (Q i : ↥S) = R (owner (i : ↥S))) ∧
        (∀ i,
          (scalar ((((Q i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y =
            2 • ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y)) ∧
        Q.IsCycle ∧
        (∃ i : ↥(permutationFamilyComponentFiber R owner C),
          (scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y ≠ 0 ∧
          addOrderOf
              ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) ∣
            2 ^ (permutationFamilyComponentFiber R owner C).card - 1 ∧
          addOrderOf
              ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) ∣
            addOrderOf y ∧
          (permutationFamilyComponentFiber R owner C).card ≤
            addOrderOf
              ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) - 1 ∧
          (permutationFamilyComponentFiber R owner C).card ≤
            addOrderOf y - 1) ∧
        ∃ i, ∃ ell : ℕ,
          2 ≤ ell ∧ ell ≤ d ∧ Q^[ell] i = i ∧
            Odd (2 ^ ell - 1) ∧
            (2 ^ ell - 1) •
              ((scalar ((((i : ↥S) : ↥F) : ↥E) : ↥J) - rho) • y) = 0 := by
    intro C hC
    let value : ↥S → G := fun f ↦
      (scalar (((f : ↥F) : ↥E) : ↥J) - rho) • y
    have hvalue : ∀ (i j : ↥S),
        Quotient.mk (Equiv.Perm.SameCycle.setoid R) (owner i) = C →
        owner j = R (owner i) → value j = 2 • value i := by
      intro i j hiC hjOwner
      rcases hfull C hC i hiC with ⟨k, hk, _hkUnique⟩
      have hjk : j = k := howner (hjOwner.trans hk.1.symm)
      subst j
      exact hk.2.2.2
    obtain ⟨Q, hQOwner⟩ :=
      permutationFamilyFullComponent_exists_successorPerm
        R owner howner C hC
    have hQValue : ∀ i, value (Q i : ↥S) = 2 • value (i : ↥S) := by
      intro i
      exact hvalue (i : ↥S) (Q i : ↥S)
        (Finset.mem_filter.mp i.property).2 (hQOwner i)
    have hQne : ∀ i, Q i ≠ i := by
      intro i hi
      apply hRne (owner (i : ↥S))
      calc
        R (owner (i : ↥S)) = owner (Q i : ↥S) := (hQOwner i).symm
        _ = owner (i : ↥S) :=
          congrArg (fun k :
            ↥(permutationFamilyComponentFiber R owner C) ↦
              owner (k : ↥S)) hi
    have hQCycle : Q.IsCycle :=
      permutationFamilyFullComponent_successorPerm_isCycle
        R owner howner hRne C hC Q hQOwner
    have hcomponentMultiplicity : ∀ v : G,
        (Finset.univ.filter (fun i :
          ↥(permutationFamilyComponentFiber R owner C) ↦
            value (i : ↥S) = v)).card ≤ 1 := by
      have hrestrict := permutationFamilyComponentFiber_valueFiber_card_le
        R (fun f : ↥F ↦ (((f : ↥E) : ↥J) : Fin d))
          S centered C 1 hcenteredMultiplicity
      simpa only [owner, value, centered] using hrestrict
    have hvalueInjective : Function.Injective (fun i :
        ↥(permutationFamilyComponentFiber R owner C) ↦
          value (i : ↥S)) := by
      intro i j hij
      apply Subtype.ext
      apply hcenteredInjective
      simpa only [value, centered] using hij
    have horderCharge := isCycle_doubling_zero_or_orderCharge
      Q (fun i ↦ value (i : ↥S)) hQCycle hQne hQValue 1
        hcomponentMultiplicity
    have hQCycle' := hQCycle
    obtain ⟨i₀, _hi₀, _hsame⟩ := hQCycle'
    have horderCharge' : ∃ i :
        ↥(permutationFamilyComponentFiber R owner C),
        value (i : ↥S) ≠ 0 ∧
        addOrderOf (value (i : ↥S)) ∣
          2 ^ Fintype.card
            ↥(permutationFamilyComponentFiber R owner C) - 1 ∧
        Fintype.card ↥(permutationFamilyComponentFiber R owner C) ≤
          addOrderOf (value (i : ↥S)) - 1 := by
      rcases horderCharge with hzero | hcharge
      · exfalso
        apply hQne i₀
        apply hvalueInjective
        exact (hzero (Q i₀)).trans (hzero i₀).symm
      · simpa using hcharge
    have horderChargeGlobal : ∃ i :
        ↥(permutationFamilyComponentFiber R owner C),
        value (i : ↥S) ≠ 0 ∧
        addOrderOf (value (i : ↥S)) ∣
          2 ^ Fintype.card
            ↥(permutationFamilyComponentFiber R owner C) - 1 ∧
        addOrderOf (value (i : ↥S)) ∣ addOrderOf y ∧
        Fintype.card ↥(permutationFamilyComponentFiber R owner C) ≤
          addOrderOf (value (i : ↥S)) - 1 ∧
        Fintype.card ↥(permutationFamilyComponentFiber R owner C) ≤
          addOrderOf y - 1 := by
      obtain ⟨i, hiNonzero, hiMersenne, hiCard⟩ := horderCharge'
      have hiMem : value (i : ↥S) ∈ AddSubgroup.zmultiples y := by
        dsimp only [value]
        exact (AddSubgroup.zmultiples y).zsmul_mem
          (AddSubgroup.mem_zmultiples y)
            (scalar (((i : ↥S) : ↥F) : ↥E) - rho)
      have hiOrder : addOrderOf (value (i : ↥S)) ∣ addOrderOf y :=
        addOrderOf_dvd_of_mem_zmultiples hiMem
      have hiOrderLe : addOrderOf (value (i : ↥S)) ≤ addOrderOf y :=
        Nat.le_of_dvd (addOrderOf_pos y) hiOrder
      exact ⟨i, hiNonzero, hiMersenne, hiOrder, hiCard,
        hiCard.trans (Nat.sub_le_sub_right hiOrderLe 1)⟩
    obtain ⟨i, ell, hellTwo, hellFiber, hperiod⟩ :=
      exists_bounded_cycle_of_fixedPointFree Q i₀ hQne
    have hfiberCard :
        Fintype.card ↥(permutationFamilyComponentFiber R owner C) ≤ d := by
      have hcard := Fintype.card_le_of_injective
        (fun k : ↥(permutationFamilyComponentFiber R owner C) ↦
          owner (k : ↥S)) (by
            intro j k hjk
            apply Subtype.ext
            exact howner hjk)
      simpa only [Fintype.card_fin] using hcard
    have htorsion : (2 ^ ell - 1) • value (i : ↥S) = 0 :=
      pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
        Q (fun k ↦ value (k : ↥S)) hQValue hperiod
    refine ⟨Q, hQOwner, hQValue, hQCycle, ?_, i, ell, hellTwo,
      hellFiber.trans hfiberCard, hperiod, odd_two_pow_sub_one (by omega),
      htorsion⟩
    simpa only [value, Fintype.card_coe] using horderChargeGlobal
  have hfullOrderBound : ∀ C,
      C ∈ permutationSubsetFullComponents R
        (permutationFamilyOwnerSet owner) →
      (permutationFamilyComponentFiber R owner C).card ≤
        addOrderOf y - 1 := by
    intro C hC
    obtain ⟨_Q, _hQOwner, _hQValue, _hQCycle, hcharge, _hbounded⟩ :=
      hfullCycle C hC
    obtain ⟨_i, _hiNonzero, _hiMersenne, _hiOrder,
      _hiCard, hiGlobalCard⟩ := hcharge
    exact hiGlobalCard
  have hcomponentAggregate :=
    permutationFamily_fullCapacity_or_largeBoundaryRow
      R owner howner (addOrderOf y - 1) hfullOrderBound
  have hcomponentAggregate' :
      S.card ≤
          ((permutationSubsetFullComponents R
              (permutationFamilyOwnerSet owner)).card +
            (permutationSubsetBoundary R
              (permutationFamilyOwnerSet owner)).card) *
            (addOrderOf y - 1) ∨
        ∃ C ∈ permutationFamilyComponents R owner,
          addOrderOf y - 1 <
              (permutationFamilyComponentFiber R owner C).card ∧
          C ∉ permutationSubsetFullComponents R
            (permutationFamilyOwnerSet owner) ∧
          ∃ s : ↥(permutationFamilyBoundaryRows R owner),
            Quotient.mk (Equiv.Perm.SameCycle.setoid R)
                (owner (s : ↥S)) = C ∧
              NestedBoundaryRowSuccessorTransition
                R J E I F S owner s := by
    rcases hcomponentAggregate with
      hcap | ⟨C, hC, hlargeC, hnotFull, s, hsC⟩
    · left
      simpa only [Fintype.card_coe] using hcap
    · right
      refine ⟨C, hC, hlargeC, hnotFull, s, hsC, ?_⟩
      exact nestedSelectedBoundaryRow_successor_transition
        R J E I hpartition F S s
  have hfrontier := permutationFamily_affineComponentFrontier
    R owner displacement target hdouble' mu offset haffineMu
      componentThreshold
  refine ⟨z, hzB, hzx, hlambdaLevel, mu, hmuLevel, epsilon,
    hepsilonLevel, offset, hparameters, rho, hrho,
    S, rfl, hSnonemptyOut, hSdominant', howner, haffineMu,
    hselectedOrderBound, hdimensionOrderBound, hboundary,
    hboundaryRouted, hdense, hpositive, hcolumns, hxPositive, hzPositive,
    huniform, hfull, hfullCycle, hcomponentAggregate', ?_⟩
  rcases hfrontier with hcomponents | hcomponent
  · left
    have hcomponents' : S.card ≤
        (permutationFamilyComponents R owner).card * componentThreshold := by
      simpa [Fintype.card_coe] using hcomponents
    refine ⟨hcomponents', ?_⟩
    have hcard := card_permutationFamilyComponents_le_full_add_boundary
      R owner
    exact hcomponents'.trans
      (Nat.mul_le_mul_right componentThreshold hcard)
  · right
    exact hcomponent

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

/-- The private-owner coefficient obeys the same three-level restriction.
Indeed, privacy confines every other nonzero entry to the two retained
coordinates, whose lower bounds force the owner coefficient to be at most
two. -/
theorem privateWitness_ownerCoefficient_mem_twoRetainedLevels
    (g : Fin n → G) {target : G} {c : Fin n → ℤ}
    (hc : Witness g target c) (B : Finset (Fin n))
    (owner : Fin n) (hownerB : owner ∈ B) (howner : c owner ≠ 0)
    (hprivate : ∀ i, i ∈ B → i ≠ owner → c i = 0)
    (hretained : n - B.card = 2) :
    c owner ∈ twoRetainedExternalCoefficientLevels := by
  classical
  have hCcard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hCone : 1 < (Finset.univ \ B).card := by omega
  obtain ⟨x, hxC, z, hzC, hxz⟩ := Finset.one_lt_card.mp hCone
  have hCeq : Finset.univ \ B = {x, z} :=
    finset_eq_pair_of_card_eq_two_of_mem hCcard hxC hzC hxz
  have hxB : x ∉ B := (Finset.mem_sdiff.mp hxC).2
  have hzB : z ∉ B := (Finset.mem_sdiff.mp hzC).2
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
        rw [hCeq] at hiC
        simpa using hiC
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
    simpa only [Finset.mem_singleton] using hxz
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
  have hlevel : c owner = -1 ∨ c owner = 1 ∨ c owner = 2 := by omega
  rcases hlevel with hlevel | hlevel | hlevel
  · simp [twoRetainedExternalCoefficientLevels, hlevel]
  · simp [twoRetainedExternalCoefficientLevels, hlevel]
  · simp [twoRetainedExternalCoefficientLevels, hlevel]

/-- Once the two retained coordinates are named, a private witness has exact
three-coordinate support.  Its zero coefficient sum determines the companion
coefficient and its witness equation becomes the corresponding affine target
formula. -/
theorem privateWitness_twoRetained_exactShape
    (g : Fin n → G) {target : G} {c : Fin n → ℤ}
    (hc : Witness g target c) (B : Finset (Fin n))
    (owner : Fin n) (hownerB : owner ∈ B)
    (hprivate : ∀ i, i ∈ B → i ≠ owner → c i = 0)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    c z = -(c owner + c x) ∧
      (∀ i : Fin n, i ≠ owner → i ≠ x → i ≠ z → c i = 0) ∧
      target = c owner • g owner + c x • g x + c z • g z := by
  classical
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
        rw [hcomplement] at hiC
        simpa using hiC
      exact hiPair.elim hix hiz
    exact hprivate i hiB hiOwner
  have hownerNotPair : owner ∉ ({x, z} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hownerX, hownerZ⟩
  have hxNotZ : x ∉ ({z} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hxz
  have hsumRestrict :
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
  have hsum : c owner + c x + c z = 0 := by
    calc
      c owner + c x + c z =
          ∑ i ∈ ({owner, x, z} : Finset (Fin n)), c i := by
        rw [Finset.sum_insert hownerNotPair, Finset.sum_insert hxNotZ]
        simp [add_assoc]
      _ = ∑ i, c i := hsumRestrict
      _ = 0 := hc.2.2.1
  have hvalueRestrict :
      ∑ i ∈ ({owner, x, z} : Finset (Fin n)), c i • g i =
        ∑ i, c i • g i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      rw [hzeroOutside i (by
        intro hiOwner
        exact hi (by simp [hiOwner])) (by
        intro hix
        exact hi (by simp [hix])) (by
        intro hiz
        exact hi (by simp [hiz])), zero_zsmul])
  have hvalue :
      c owner • g owner + c x • g x + c z • g z = target := by
    calc
      c owner • g owner + c x • g x + c z • g z =
          ∑ i ∈ ({owner, x, z} : Finset (Fin n)), c i • g i := by
        rw [Finset.sum_insert hownerNotPair, Finset.sum_insert hxNotZ]
        simp [add_assoc]
      _ = ∑ i, c i • g i := hvalueRestrict
      _ = target := hc.2.2.2
  exact ⟨by omega, hzeroOutside, hvalue.symm⟩

/-- Uniform exact geometry of one owner-profile inside the complete
minimal-transversal private family. -/
def TwoRetainedMinimalCyclicKernelPrivateProfileGeometry
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (scalar : ↥B → ℤ) (coeff : ↥B → Fin n → ℤ)
    (label : Fin n × ℤ) (F : Finset ↥B)
    (mu : ℤ) (S : Finset ↥F) : Prop :=
  ∃ z : Fin n, z ∉ B ∧ z ≠ label.1 ∧
    Finset.univ \ B = {label.1, z} ∧
    ∀ f : ↥S,
      let b : ↥B := (f : ↥F)
      coeff b (b : Fin n) = mu ∧
        coeff b label.1 = label.2 ∧
        coeff b z = -(mu + label.2) ∧
        (∀ i : Fin n, i ≠ (b : Fin n) →
          i ≠ label.1 → i ≠ z → coeff b i = 0) ∧
        scalar b • y =
          mu • g (b : Fin n) + label.2 • g label.1 +
            (-(mu + label.2)) • g z

/-- Canonical private witnesses indexed by every point of a minimal cyclic-
kernel transversal when exactly two coordinates survive.  Each row uses its
own deleted coordinate and a chosen retained coordinate; the retained
coefficient belongs to the uniform three-level alphabet. -/
def TwoRetainedMinimalCyclicKernelPrivateRows
    (g : Fin n → G) (y : G) (B : Finset (Fin n)) : Prop :=
  n - B.card = 2 ∧
    ∃ scalar : ↥B → ℤ, ∃ coeff : ↥B → Fin n → ℤ,
      ∃ supportCoord : ↥B → Fin n,
        Function.Injective coeff ∧
        (∀ b : ↥B,
            scalar b • y ≠ 0 ∧
            Witness g (scalar b • y) (coeff b) ∧
            coeff b (b : Fin n) ≠ 0 ∧
            coeff b (b : Fin n) ∈
              twoRetainedExternalCoefficientLevels ∧
            (∀ a ∈ B, a ≠ (b : Fin n) → coeff b a = 0) ∧
            supportCoord b ∉ B ∧
            coeff b (supportCoord b) ≠ 0 ∧
            coeff b (supportCoord b) ∈
              twoRetainedExternalCoefficientLevels) ∧
        (B = ∅ ∨
          ∃ label ∈ (Finset.univ \ B).product
              twoRetainedExternalCoefficientLevels,
            let F : Finset ↥B := Finset.univ.filter (fun b : ↥B ↦
              (supportCoord b, coeff b (supportCoord b)) = label)
            F.Nonempty ∧ B.card ≤ 6 * F.card ∧
              ∃ mu ∈ twoRetainedExternalCoefficientLevels,
                let S : Finset ↥F := Finset.univ.filter (fun f : ↥F ↦
                  coeff (f : ↥B) ((f : ↥B) : Fin n) = mu)
                S.Nonempty ∧ F.card ≤ 3 * S.card ∧
                  B.card ≤ 18 * S.card ∧
                  TwoRetainedMinimalCyclicKernelPrivateProfileGeometry
                    g y B scalar coeff label F mu S)

/-- Minimality supplies the full exact-two private-row family canonically;
unlike the cycle-owned subfamily, this retains every deleted coordinate. -/
theorem twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
    (g : Fin n → G) (y : G) {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2) :
    TwoRetainedMinimalCyclicKernelPrivateRows g y B := by
  classical
  let data : ∀ b : ↥B, CyclicKernelPrivateWitnessData g y b :=
    fun b ↦ minimalCyclicKernelPrivateWitnessData g y hmin b
  have hsupport : ∀ b : ↥B, ∃ x : Fin n,
      x ∉ B ∧ (data b).coeff x ≠ 0 := by
    intro b
    obtain ⟨x, hxOwner, hxNonzero⟩ :=
      exists_other_nonzero_of_sum_eq_zero (data b).coeff
        (data b).owner_ne_zero (data b).isWitness.2.2.1
    refine ⟨x, ?_, hxNonzero⟩
    intro hxB
    exact hxNonzero ((data b).zero_other x hxB hxOwner)
  let supportCoord : ↥B → Fin n := fun b ↦ Classical.choose (hsupport b)
  have hsupportCoord : ∀ b : ↥B,
      supportCoord b ∉ B ∧ (data b).coeff (supportCoord b) ≠ 0 := by
    intro b
    exact Classical.choose_spec (hsupport b)
  have hrowData : ∀ b : ↥B,
      (data b).scalar • y ≠ 0 ∧
      Witness g ((data b).scalar • y) (data b).coeff ∧
      (data b).coeff (b : Fin n) ≠ 0 ∧
      (data b).coeff (b : Fin n) ∈
        twoRetainedExternalCoefficientLevels ∧
      (∀ a ∈ B, a ≠ (b : Fin n) → (data b).coeff a = 0) ∧
      supportCoord b ∉ B ∧
      (data b).coeff (supportCoord b) ≠ 0 ∧
      (data b).coeff (supportCoord b) ∈
        twoRetainedExternalCoefficientLevels := by
    intro b
    refine ⟨(data b).target_ne_zero, (data b).isWitness,
      (data b).owner_ne_zero, ?_, (data b).zero_other,
      (hsupportCoord b).1, (hsupportCoord b).2, ?_⟩
    · exact privateWitness_ownerCoefficient_mem_twoRetainedLevels
        g (data b).isWitness B (b : Fin n) b.property
          (data b).owner_ne_zero (data b).zero_other hretained
    exact privateWitness_externalCoefficient_mem_twoRetainedLevels
      g (data b).isWitness B (b : Fin n) (supportCoord b)
        b.property (data b).owner_ne_zero (data b).zero_other
        (hsupportCoord b).1 (hsupportCoord b).2 hretained
  refine ⟨hretained, (fun b ↦ (data b).scalar),
    (fun b ↦ (data b).coeff), supportCoord,
    minimalCyclicKernelPrivateWitness_coeff_injective g y hmin,
    hrowData, ?_⟩
  by_cases hB : B = ∅
  · exact Or.inl hB
  · right
    let label : ↥B → Fin n × ℤ := fun b ↦
      (supportCoord b, (data b).coeff (supportCoord b))
    let labels : Finset (Fin n × ℤ) :=
      (Finset.univ \ B).product twoRetainedExternalCoefficientLevels
    have hlabelMem : ∀ b : ↥B, label b ∈ labels := by
      intro b
      rcases hrowData b with
        ⟨_htarget, _hwitness, _howner, _hownerLevel, _hprivate,
          hsupportB, _hsupportNonzero, hlevel⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsupportB⟩, hlevel⟩
    have hsource : (Finset.univ : Finset ↥B).Nonempty := by
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hB
      exact ⟨(⟨b, hb⟩ : ↥B), Finset.mem_univ _⟩
    obtain ⟨z, hz, hFnonempty, hdominant⟩ :=
      finiteMap_exists_dominantFiber labels label hlabelMem hsource
    have hcomplementCard : (Finset.univ \ B).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
      simpa using hretained
    have hlabelsCard : labels.card = 6 := by
      calc
        labels.card = (Finset.univ \ B).card *
            twoRetainedExternalCoefficientLevels.card :=
          Finset.card_product _ _
        _ = 2 * 3 := by rw [hcomplementCard,
          card_twoRetainedExternalCoefficientLevels]
        _ = 6 := by omega
    let F : Finset ↥B := Finset.univ.filter (fun b : ↥B ↦ label b = z)
    have hFnonempty' : F.Nonempty := by
      simpa [F, label] using hFnonempty
    have hBdominant : B.card ≤ 6 * F.card := by
      rw [hlabelsCard] at hdominant
      simpa only [Fintype.card_coe, F] using hdominant
    let ownerLevel : ↥F → ℤ := fun f ↦
      (data (f : ↥B)).coeff ((f : ↥B) : Fin n)
    have hownerLevelMem : ∀ f : ↥F,
        ownerLevel f ∈ twoRetainedExternalCoefficientLevels := by
      intro f
      rcases hrowData (f : ↥B) with
        ⟨_htarget, _hwitness, _howner, hlevel, _hprivate,
          _hsupportB, _hsupportNonzero, _hsupportLevel⟩
      exact hlevel
    have hFsource : (Finset.univ : Finset ↥F).Nonempty := by
      obtain ⟨f, hf⟩ := hFnonempty'
      exact ⟨(⟨f, hf⟩ : ↥F), Finset.mem_univ _⟩
    obtain ⟨mu, hmu, hSnonempty, hprofileDominant⟩ :=
      finiteMap_exists_dominantFiber twoRetainedExternalCoefficientLevels
        ownerLevel hownerLevelMem hFsource
    let S : Finset ↥F := Finset.univ.filter (fun f : ↥F ↦
      ownerLevel f = mu)
    have hSnonempty' : S.Nonempty := by
      simpa [S, ownerLevel] using hSnonempty
    have hFprofile : F.card ≤ 3 * S.card := by
      rw [card_twoRetainedExternalCoefficientLevels] at hprofileDominant
      simpa only [Fintype.card_coe, S] using hprofileDominant
    have hBprofile : B.card ≤ 18 * S.card := by
      calc
        B.card ≤ 6 * F.card := hBdominant
        _ ≤ 6 * (3 * S.card) := Nat.mul_le_mul_left 6 hFprofile
        _ = 18 * S.card := by omega
    have hxC : z.1 ∈ Finset.univ \ B :=
      (Finset.mem_product.mp hz).1
    have hxB : z.1 ∉ B := (Finset.mem_sdiff.mp hxC).2
    have hCone : 1 < (Finset.univ \ B).card := by omega
    obtain ⟨u, huC, v, hvC, huv⟩ := Finset.one_lt_card.mp hCone
    obtain ⟨w, hwC, hwNeX⟩ :
        ∃ w ∈ Finset.univ \ B, w ≠ z.1 := by
      by_cases hux : u = z.1
      · refine ⟨v, hvC, ?_⟩
        intro hvx
        exact huv (hux.trans hvx.symm)
      · exact ⟨u, huC, hux⟩
    have hwB : w ∉ B := (Finset.mem_sdiff.mp hwC).2
    have hcomplement : Finset.univ \ B = {z.1, w} :=
      finset_eq_pair_of_card_eq_two_of_mem
        hcomplementCard hxC hwC hwNeX.symm
    have hgeometry :
        TwoRetainedMinimalCyclicKernelPrivateProfileGeometry
          g y B (fun b ↦ (data b).scalar) (fun b ↦ (data b).coeff)
            z F mu S := by
      refine ⟨w, hwB, hwNeX, hcomplement, ?_⟩
      intro f
      let b : ↥B := (f : ↥F)
      have hownerValue : (data b).coeff (b : Fin n) = mu := by
        have hf := (Finset.mem_filter.mp f.property).2
        simpa only [ownerLevel, b] using hf
      have hlabelValue : label b = z := by
        have hf := (Finset.mem_filter.mp (f : ↥F).property).2
        simpa only [F, b] using hf
      have hsupportValue : supportCoord b = z.1 :=
        congrArg Prod.fst hlabelValue
      have hlambdaValue : (data b).coeff z.1 = z.2 := by
        have hvalue := congrArg Prod.snd hlabelValue
        simpa only [label, hsupportValue] using hvalue
      rcases hrowData b with
        ⟨_htarget, hwitness, _howner, _hownerLevel, hprivate,
          _hsupportB, _hsupportNonzero, _hsupportLevel⟩
      have hshape := privateWitness_twoRetained_exactShape
        g hwitness B (b : Fin n) b.property hprivate z.1 w hxB hwB
          hwNeX.symm hcomplement
      refine ⟨hownerValue, hlambdaValue, ?_, hshape.2.1, ?_⟩
      · change (data b).coeff w = -(mu + z.2)
        rw [hshape.1, hownerValue, hlambdaValue]
      · change (data b).scalar • y =
          mu • g (b : Fin n) + z.2 • g z.1 + (-(mu + z.2)) • g w
        simpa only [hownerValue, hlambdaValue, hshape.1] using hshape.2.2
    refine ⟨z, hz, ?_⟩
    dsimp only
    refine ⟨hFnonempty', hBdominant, mu, hmu, ?_, ?_, ?_, ?_⟩
    · simpa only [S, ownerLevel]
    · simpa only [S, ownerLevel] using hFprofile
    · simpa only [S, ownerLevel] using hBprofile
    · simpa only [F, label, S, ownerLevel] using hgeometry

/-- Any realized exact-two external label fiber has the full private
diagonal-plus-common-column structure.  This factors the geometric part from
the choice of threshold or dominant label. -/
theorem fixedExternalCoefficientPrivateFiber_of_twoRetainedExternalLabel
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) (E : Finset ↥J)
    (supportCoord : ↥E → Fin n)
    (hprivate : ∀ (j : ↥J) i, i ∈ B →
      i ≠ center (P.symm (j : Fin d)) → coeff j i = 0)
    (hcenterInj : Function.Injective center)
    (hownerMem : ∀ j : ↥J, center (P.symm (j : Fin d)) ∈ B)
    (howner : ∀ j : ↥J,
      coeff j (center (P.symm (j : Fin d))) ≠ 0)
    (hcoeffInj : Function.Injective coeff)
    (z : Fin n × ℤ)
    (hz : z ∈ (((Finset.univ \ B) \
          (Finset.univ.image center : Finset (Fin n))).product
        twoRetainedExternalCoefficientLevels)) :
    FixedExternalCoefficientPrivateFiber B center P coeff
      (Finset.univ.filter (fun e : ↥E ↦
        (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z))
      z.1 z.2 := by
  classical
  let level : ↥E → (Fin n × ℤ) := fun e ↦
    (supportCoord e, coeff (e : ↥J) (supportCoord e))
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

/-- Dominant-label version of the exact-two external-row frontier.  For a
nonempty external family it selects one realized coordinate/coefficient label
whose fiber pays for all external rows with the sharp constant-six budget,
while retaining the full private-fiber geometry. -/
theorem twoRetainedExternalRows_exists_dominantPrivateFiber
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
    (hretained : n - B.card = 2) (hE : E.Nonempty) :
    ∃ z ∈ (((Finset.univ \ B) \
          (Finset.univ.image center : Finset (Fin n))).product
        twoRetainedExternalCoefficientLevels),
      let F := Finset.univ.filter (fun e : ↥E ↦
        (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z)
      F.Nonempty ∧ E.card ≤ 6 * F.card ∧
        FixedExternalCoefficientPrivateFiber B center P coeff F z.1 z.2 := by
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
  have hsource : (Finset.univ : Finset ↥E).Nonempty := by
    obtain ⟨e, heE⟩ := hE
    exact ⟨(⟨e, heE⟩ : ↥E), Finset.mem_univ _⟩
  obtain ⟨z, hz, hFnonempty, hFdominant⟩ :=
    finiteMap_exists_dominantFiber
      (R.product twoRetainedExternalCoefficientLevels)
      level hlevelMem hsource
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
  refine ⟨z, by simpa [R] using hz, by simpa [level] using hFnonempty,
    ?_, ?_⟩
  · have hdominant : E.card ≤
        (R.product twoRetainedExternalCoefficientLevels).card *
          (Finset.univ.filter (fun e : ↥E ↦ level e = z)).card := by
      simpa [Fintype.card_coe] using hFdominant
    have hdominant' := hdominant.trans
      (Nat.mul_le_mul_right
        (Finset.univ.filter (fun e : ↥E ↦ level e = z)).card
        hproductCard)
    simpa [level] using hdominant'
  · exact fixedExternalCoefficientPrivateFiber_of_twoRetainedExternalLabel
      B center P coeff E supportCoord hprivate hcenterInj hownerMem howner
        hcoeffInj z (by simpa [R] using hz)

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

/-- Named exact-two row dichotomy whose external branch already carries its
occupied relative-cycle decomposition. -/
def TwoRetainedExternalInternalCycleComponentFrontier
    (g : Fin n → G) (y base : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (componentThreshold : ℕ) : Prop :=
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
            FixedExternalTwoRetainedRelativeAffineCycleComponentFrontierAbove
              g y base B center P R scalar coeff F label.1
                ((d - 1) / 36) componentThreshold)

/-- The exact-two dense dichotomy with its external arm carried all the way
through translation and occupied relative-cycle decomposition. -/
theorem twoRetainedExternalInternalRowFrontier_largeInternal_or_cycleComponentExternal
    (g : Fin n → G) (y base : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hfrontier : TwoRetainedExternalInternalRowFrontier
      g y B center P J)
    (hretained : n - B.card = 2)
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j,
      g (center (P.symm (R j))) - base =
        2 • (g (center (P.symm j)) - base))
    (componentThreshold : ℕ) :
    TwoRetainedExternalInternalCycleComponentFrontier
      g y base B center P J R componentThreshold := by
  classical
  unfold TwoRetainedExternalInternalCycleComponentFrontier
  rcases twoRetainedExternalInternalRowFrontier_largeInternal_or_largeAffineExternal
      g y B center P J hfrontier hretained with
    ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, hinternal | hexternal⟩
  · exact ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, Or.inl hinternal⟩
  · refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hrows, hsupport, Or.inr ?_⟩
    rcases hexternal with ⟨label, hlabel, hfiber, hprofile⟩
    refine ⟨label, hlabel, hfiber, ?_⟩
    have hrelative := FixedExternalTwoRetainedAffineProfileAbove.relative
      g y base B center P scalar coeff
        (Finset.univ.filter (fun e : ↥E ↦
          (supportCoord e, coeff (e : ↥J) (supportCoord e)) = label))
        label.1 label.2 ((d - 1) / 36) hprofile
    exact hrelative.cycleComponentFrontier
      g y base B center P scalar coeff
        (Finset.univ.filter (fun e : ↥E ↦
          (supportCoord e, coeff (e : ↥J) (supportCoord e)) = label))
        label.1 ((d - 1) / 36) componentThreshold R hdouble

/-- Dominant exact-two row dichotomy.  The external branch selects its label
and affine profile once across the entire external family, then carries the
resulting quantitative boundary/full-component frontier on that same set. -/
def TwoRetainedExternalInternalDominantCycleComponentFrontier
    (g : Fin n → G) (y base : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (componentThreshold : ℕ) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ E I : Finset ↥J, ∃ supportCoord : ↥E → Fin n,
      E ∪ I = Finset.univ ∧ Disjoint E I ∧
      E.card + I.card = J.card ∧ d - 1 ≤ E.card + I.card ∧
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
        (2 * I.card < d - 1 ∧
        ∃ label ∈ (((Finset.univ \ B) \
              (Finset.univ.image center : Finset (Fin n))).product
            twoRetainedExternalCoefficientLevels),
          let F : Finset ↥E := Finset.univ.filter (fun e : ↥E ↦
            (supportCoord e,
              coeff (e : ↥J) (supportCoord e)) = label)
          F.Nonempty ∧ E.card ≤ 6 * F.card ∧
            FixedExternalCoefficientPrivateFiber
              B center P coeff F label.1 label.2 ∧
            FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier
              g y base B center P R scalar coeff I F label.1 label.2
                componentThreshold))

/-- Construct the dominant exact-two cycle frontier directly from the
retained row partition.  The internal alternative is unchanged; otherwise
the external set is nonempty and the global maximum fibers supply both
constant dominance estimates before cycle decomposition. -/
theorem retainedExternalInternalRowPartition_largeInternal_or_dominantCycleComponentExternal
    [Fintype G] [DecidableEq G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y base : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hpart : RetainedExternalInternalRowPartition g y B center P J)
    (hretained : n - B.card = 2)
    (R : Equiv.Perm (Fin d))
    (hRne : ∀ j, R j ≠ j)
    (hdouble : ∀ j,
      g (center (P.symm (R j))) - base =
        2 • (g (center (P.symm j)) - base))
    (hdisplacement : ∀ j,
      g (center (P.symm j)) - base ∈ AddSubgroup.zmultiples y)
    (componentThreshold : ℕ) :
    TwoRetainedExternalInternalDominantCycleComponentFrontier
      g y base B center P J R componentThreshold := by
  classical
  unfold TwoRetainedExternalInternalDominantCycleComponentFrontier
  rcases hpart with
    ⟨scalar, coeff, E, I, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner, hunion, hdisjoint, hcard, hlarge,
      _hEiff, supportCoord, hsupport, _hcoordFrontier,
      _hgenericLevelFrontier, hinternal⟩
  refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
    hlarge, hrows, hsupport, ?_⟩
  by_cases hIlarge : d - 1 ≤ 2 * I.card
  · exact Or.inl ⟨hIlarge, hinternal⟩
  · right
    have hIsparse : 2 * I.card < d - 1 := Nat.lt_of_not_ge hIlarge
    have hE : E.Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨label, hlabel, hFnonempty, hFdominant, hfiber⟩ :=
      twoRetainedExternalRows_exists_dominantPrivateFiber
        g y B center P scalar coeff E supportCoord hsupport
          (fun j ↦ (hrows j).2) hprivate hcenterInj hownerMem howner
          hcoeffInj hretained hE
    let F : Finset ↥E := Finset.univ.filter (fun e : ↥E ↦
      (supportCoord e, coeff (e : ↥J) (supportCoord e)) = label)
    have hprofile :=
      fixedExternalCoefficientPrivateFiber_twoRetained_dominantRelativeProfile
        g y base B center P scalar coeff F label.1 label.2
          (by simpa [F] using hfiber) (fun j ↦ (hrows j).2)
          hretained (by simpa [F] using hFnonempty)
    have hcycle := hprofile.cycleComponentFrontier
      g hg hh hne hunique hno y base B center P scalar coeff I F
        label.1 label.2
        (Finset.mem_product.mp hlabel).2 (by simpa [F] using hfiber)
          hretained hrows hJcard hunion hlarge
            (by simpa [F] using hFdominant) hIsparse R hRne hdouble
              hdisplacement componentThreshold
    refine ⟨hIsparse, label, hlabel, ?_, ?_, ?_, ?_⟩
    · simpa [F] using hFnonempty
    · simpa [F] using hFdominant
    · simpa [F] using hfiber
    · simpa [F] using hcycle

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

/-- The row-partition endpoint with the successor permutation aligned to the
same explicit center permutation `P`.  Its relative permutation therefore
acts by doubling on the translated leaf coordinates used by the rows. -/
def PureEdgeStarLeafOddPrimaryFullCycleAlignedRowPartitionOutcome
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
            g y B center P J ∧
          ∃ S : Equiv.Perm (Fin d),
            (∀ j : Fin d,
              P j ≠ j ∧ P j ≠ S j ∧
              center j = leaf (P j) ∧
              (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
              (2 : ℤ) • g (leaf (P j)) =
                h + g r + g (leaf (S j))) ∧
            ∀ j : Fin d,
              disp ((P.symm.trans S) j) = 2 • disp j)

/-- Reopen the retained cycle-layer algebra and use injectivity of the
minimal leaf cycle to identify its center permutation with the explicit row
permutation.  Earlier nested capacity branches are propagated outward. -/
theorem pureEdgeStarLeafCycle_alignedRowPartitionOutcome_of_rowPartitionOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleAlignedRowPartitionOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        hsharp, hnormal, hrows⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · have hcharge' := hcharge
    rcases hcharge' with hcap | hmixed |
        ⟨hrelative, _hlayer, _i, _ell, _p, _B, _hellTwo, _hellD,
          _hodd, _htorsion, _hlayers, _hcert, _hordD, _hlog⟩
    · exact Or.inl hcap
    · exact Or.inr (Or.inl hmixed)
    · right
      right
      let leaf : Fin d → Fin (m + 1) :=
        fun j ↦ (T^[j.val] a : Fin (m + 1))
      let disp : Fin d → ZMod (2 ^ t * q) :=
        fun j ↦ g (leaf j) - (h + g r)
      have hleaf : Function.Injective leaf := by
        intro j k hjk
        apply minimalFixedPointFreeCycle_iterates_injective T hcycle
        exact Subtype.ext hjk
      have hrelative' := hrelative
      rcases hrelative' with
        ⟨P', S, hlocal, _hsum, _htorsionRelative⟩
      have hsparse' := hsparse
      rcases hsparse' with
        ⟨_scalar, _coeff, _hJcard, _hJiff, _htarget, _hwitness,
          _howner, _hzero, _hprivate, _hcoeffInj, hcenter,
          _hcenterOutside, _hrowSupport⟩
      have hP' : P' = P := by
        apply Equiv.ext
        intro j
        apply hleaf
        calc
          leaf (P' j) = center j := (hlocal j).2.2.1.symm
          _ = leaf (P j) := hcenter j
      subst P'
      have hdouble : ∀ j : Fin d,
          disp ((P.symm.trans S) j) = 2 • disp j := by
        simpa [disp, leaf, hcenter] using
          alignedCenterSuccessor_relativeDoubling
            g (h + g r) leaf center P S hcenter
              (fun j ↦ (hlocal j).2.2.2.2)
      refine ⟨hcharge, y, B, P, J, ?_, ?_, ?_, ?_, hsharp,
        hnormal, hrows, S, ?_, hdouble⟩
      · simpa [disp, leaf] using hspan
      · simpa [disp, leaf] using hmem
      · simpa [leaf] using hretained
      · simpa [leaf] using hsparse
      · simpa [leaf] using hlocal

/-- Global critical endpoint with the row family and its actual relative
doubling permutation retained in one aligned package. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleAlignedRowPartitionOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleAlignedRowPartitionOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRowPartitionOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_alignedRowPartitionOutcome_of_rowPartitionOutcome
      g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

/-- Global row endpoint split by the retained quotient dimension.  The
exact-two arm is fully decomposed into the dense internal pivot alternative
or the occupied-component/Mersenne external frontier. -/
def PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
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
            g y B center P J ∧
          ∃ S : Equiv.Perm (Fin d),
            (∀ j : Fin d,
              P j ≠ j ∧ P j ≠ S j ∧
              center j = leaf (P j) ∧
              (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
              (2 : ℤ) • g (leaf (P j)) =
                h + g r + g (leaf (S j))) ∧
            (∀ j : Fin d,
              disp ((P.symm.trans S) j) = 2 • disp j) ∧
            (2 < m + 1 - B.card ∨
              (TwoRetainedMinimalCyclicKernelPrivateRows g y B ∧
                TwoRetainedExternalInternalDominantCycleComponentFrontier
                  g y (h + g r) B center P J (P.symm.trans S)
                    componentThreshold)))

/-- Refine the aligned global endpoint.  At least two quotient coordinates
are retained; equality invokes the exact-two row/component theorem, while a
strictly larger quotient is kept as its own explicit branch. -/
theorem pureEdgeStarLeafCycle_componentRowOutcome_of_alignedRowPartitionOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleAlignedRowPartitionOutcome
      g h r T a d center) (componentThreshold : ℕ) :
    PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome
      g h r T a d center componentThreshold := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretainedCharge, hsparse,
        hsharp, hnormal, hrowPartition, S, hlocal, hdouble⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    let disp : Fin d → ZMod (2 ^ t * q) :=
      fun j ↦ g (leaf j) - (h + g r)
    have htwo : 2 ≤ m + 1 - B.card :=
      hretainedCharge.1.1.two_le_retained
    refine ⟨hcharge, y, B, P, J, ?_, ?_, ?_, ?_, hsharp,
      hnormal, hrowPartition, S, ?_, ?_, ?_⟩
    · simpa [disp, leaf] using hspan
    · simpa [disp, leaf] using hmem
    · simpa [leaf] using hretainedCharge
    · simpa [leaf] using hsparse
    · simpa [leaf] using hlocal
    · simpa [disp, leaf] using hdouble
    · by_cases hexact : m + 1 - B.card = 2
      · right
        refine ⟨
          twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
            g y hretainedCharge.1.1.1 hexact, ?_⟩
        have hcenter : ∀ j : Fin d, center j = leaf (P j) :=
          fun j ↦ (hlocal j).2.2.1
        have hdoubleCenter : ∀ j,
            g (center (P.symm ((P.symm.trans S) j))) - (h + g r) =
              2 • (g (center (P.symm j)) - (h + g r)) := by
          simpa [disp, leaf, hcenter] using hdouble
        have hdisplacementCenter : ∀ j,
            g (center (P.symm j)) - (h + g r) ∈
              AddSubgroup.zmultiples y := by
          simpa [disp, leaf, hcenter] using hmem
        have hRne : ∀ j, (P.symm.trans S) j ≠ j :=
          perm_symm_trans_fixedPointFree_of_apply_ne P S
            (fun j ↦ (hlocal j).2.1)
        exact
          retainedExternalInternalRowPartition_largeInternal_or_dominantCycleComponentExternal
            g hg hh hne hunique hno y (h + g r) B center P J
              hrowPartition hexact
              (P.symm.trans S) hRne hdoubleCenter hdisplacementCenter
                componentThreshold
      · left
        omega

/-- Global critical endpoint with the exact-two quotient branch already
reduced to internal density or affine cycle-component occupancy. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleComponentRowOutcome
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
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty)
    (componentThreshold : ℕ) :
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
          PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleAlignedRowPartitionOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hN : 2 ^ t * q = 2 * (2 ^ (t - 1) * q) := by
    have htDecomp : t = (t - 1) + 1 := by omega
    calc
      2 ^ t * q = 2 ^ ((t - 1) + 1) * q := by rw [← htDecomp]
      _ = 2 * (2 ^ (t - 1) * q) := by rw [pow_succ]; ring
  have hhCanonical : h = ((2 ^ (t - 1) * q : ℕ) : ZMod (2 ^ t * q)) := by
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN h hh with
      hzero | hhalf
    · exact (hne hzero).elim
    · exact hhalf
  have hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h := by
    intro u hu
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu with
      hzero | hhalf
    · exact Or.inl hzero
    · exact Or.inr (hhalf.trans hhCanonical.symm)
  have hout' :=
    pureEdgeStarLeafCycle_componentRowOutcome_of_alignedRowPartitionOutcome
      g hg hh hne hunique hno r T center hout componentThreshold
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
