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

/-- Rescale each possible exact-two owner coefficient to the common value
`2`.  This is the normalization that lets all owner profiles participate in
one balanced subset-sum argument. -/
def twoRetainedOwnerNormalization (mu : ℤ) : ℤ :=
  if mu = -1 then -2 else if mu = 1 then 2 else 1

theorem twoRetainedOwnerNormalization_mul
    {mu : ℤ} (hmu : mu ∈ twoRetainedExternalCoefficientLevels) :
    twoRetainedOwnerNormalization mu * mu = 2 := by
  simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
    Finset.mem_singleton] at hmu
  rcases hmu with hminus | hone | htwo
  · subst mu
    norm_num [twoRetainedOwnerNormalization]
  · subst mu
    norm_num [twoRetainedOwnerNormalization]
  · subst mu
    norm_num [twoRetainedOwnerNormalization]

/-- After naming the two retained coordinates, all normalized private-row
offsets are controlled by one coefficient in this five-element alphabet. -/
def twoRetainedNormalizedWeightLevels : Finset ℤ := {-4, -2, -1, 0, 2}

theorem card_twoRetainedNormalizedWeightLevels :
    twoRetainedNormalizedWeightLevels.card = 5 := by
  norm_num [twoRetainedNormalizedWeightLevels]

/-- The complete label space for a private row records its retained support
coordinate, retained coefficient, and owner coefficient. -/
def twoRetainedPrivateProfileLabels (B : Finset (Fin n)) :
    Finset ((Fin n × ℤ) × ℤ) :=
  ((Finset.univ \ B).product twoRetainedExternalCoefficientLevels).product
    twoRetainedExternalCoefficientLevels

theorem card_twoRetainedPrivateProfileLabels
    (B : Finset (Fin n)) (hretained : n - B.card = 2) :
    (twoRetainedPrivateProfileLabels B).card = 18 := by
  have hcomplementCard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  calc
    (twoRetainedPrivateProfileLabels B).card =
        (((Finset.univ \ B).product
          twoRetainedExternalCoefficientLevels).card *
            twoRetainedExternalCoefficientLevels.card) :=
      Finset.card_product _ _
    _ = (((Finset.univ \ B).card *
          twoRetainedExternalCoefficientLevels.card) *
            twoRetainedExternalCoefficientLevels.card) :=
      congrArg (fun q ↦ q * twoRetainedExternalCoefficientLevels.card)
        (Finset.card_product _ _)
    _ = 18 := by
      rw [hcomplementCard, card_twoRetainedExternalCoefficientLevels]

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

/-- After the three owner levels are normalized, every exact-two private row
has the same owner slope `2`.  The two retained terms form an offset depending
only on the row's finite profile label. -/
theorem privateWitness_twoRetained_normalizedAffine
    (g : Fin n → G) (y : G) (scalar : ℤ) {c : Fin n → ℤ}
    (hc : Witness g (scalar • y) c) (B : Finset (Fin n))
    (owner : Fin n) (hownerB : owner ∈ B)
    (hprivate : ∀ i, i ∈ B → i ≠ owner → c i = 0)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (hownerLevel : c owner ∈ twoRetainedExternalCoefficientLevels) :
    twoRetainedOwnerNormalization (c owner) • (scalar • y) =
      (2 : ℤ) • g owner +
        twoRetainedOwnerNormalization (c owner) •
          (c x • g x + (-(c owner + c x)) • g z) := by
  have hshape := privateWitness_twoRetained_exactShape
    g hc B owner hownerB hprivate x z hxB hzB hxz hcomplement
  rw [hshape.2.2, hshape.1, zsmul_add, zsmul_add]
  rw [← mul_zsmul,
    twoRetainedOwnerNormalization_mul hownerLevel]
  rw [zsmul_add]
  exact add_assoc _ _ _

/-- Naming the retained pair globally collapses the normalized affine
offset to one weight times their difference, plus the uniform translate
`-2 • g z`.  Witness positivity leaves only five possible weights. -/
theorem privateWitness_twoRetained_fiveWeightAffine
    (g : Fin n → G) (y : G) (scalar : ℤ) {c : Fin n → ℤ}
    (hc : Witness g (scalar • y) c) (B : Finset (Fin n))
    (owner : Fin n) (hownerB : owner ∈ B)
    (hprivate : ∀ i, i ∈ B → i ≠ owner → c i = 0)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (hownerLevel : c owner ∈ twoRetainedExternalCoefficientLevels) :
    let weight := twoRetainedOwnerNormalization (c owner) * c x
    weight ∈ twoRetainedNormalizedWeightLevels ∧
      (weight = -1 ↔ c owner = 2) ∧
      twoRetainedOwnerNormalization (c owner) • (scalar • y) =
        (2 : ℤ) • g owner + weight • (g x - g z) - (2 : ℤ) • g z := by
  dsimp only
  have hshape := privateWitness_twoRetained_exactShape
    g hc B owner hownerB hprivate x z hxB hzB hxz hcomplement
  have hxFloor := hc.2.1 x
  have hzFloor := hc.2.1 z
  have hweight :
      twoRetainedOwnerNormalization (c owner) * c x ∈
        twoRetainedNormalizedWeightLevels := by
    simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
      Finset.mem_singleton] at hownerLevel
    simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
      Finset.mem_singleton]
    rcases hownerLevel with hminus | hone | htwo
    · rw [hminus]
      simp only [twoRetainedOwnerNormalization, if_pos, neg_mul]
      omega
    · rw [hone]
      norm_num [twoRetainedOwnerNormalization]
      omega
    · rw [htwo]
      norm_num [twoRetainedOwnerNormalization]
      omega
  have hheavy :
      twoRetainedOwnerNormalization (c owner) * c x = -1 ↔
        c owner = 2 := by
    constructor
    · intro hweightEq
      have hlevels := hownerLevel
      simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
        Finset.mem_singleton] at hlevels
      rcases hlevels with hminus | hone | htwo
      · rw [hminus] at hweightEq
        norm_num [twoRetainedOwnerNormalization] at hweightEq
        omega
      · rw [hone] at hweightEq
        norm_num [twoRetainedOwnerNormalization] at hweightEq
        omega
      · exact htwo
    · intro htwo
      have hxValue : c x = -1 := by
        rw [hshape.1, htwo] at hzFloor
        omega
      rw [htwo, hxValue]
      norm_num [twoRetainedOwnerNormalization]
  refine ⟨hweight, hheavy, ?_⟩
  have hnormalized := privateWitness_twoRetained_normalizedAffine
    g y scalar hc B owner hownerB hprivate x z hxB hzB hxz hcomplement
      hownerLevel
  have hnormalization := twoRetainedOwnerNormalization_mul hownerLevel
  have hcoeff :
      twoRetainedOwnerNormalization (c owner) * (-(c owner + c x)) =
        -(twoRetainedOwnerNormalization (c owner) * c x) - 2 := by
    nlinarith
  rw [hnormalized]
  rw [zsmul_add, ← mul_zsmul, ← mul_zsmul, hcoeff,
    sub_zsmul, neg_zsmul, zsmul_sub]
  abel

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

/-- Under the global no-common-touch assumptions, the exact full-transversal
profile has injective kernel targets.  Equal targets cancel the common
retained offset; unit owner coefficients contradict validity, while owner
coefficient two forces common touch through the unique involution. -/
theorem TwoRetainedMinimalCyclicKernelPrivateProfileGeometry.target_injective
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : G) (B : Finset (Fin n))
    (scalar : ↥B → ℤ) (coeff : ↥B → Fin n → ℤ)
    (label : Fin n × ℤ) (F : Finset ↥B)
    (mu : ℤ) (S : Finset ↥F)
    (hmu : mu ∈ twoRetainedExternalCoefficientLevels)
    (hgeometry : TwoRetainedMinimalCyclicKernelPrivateProfileGeometry
      g y B scalar coeff label F mu S) :
    Function.Injective (fun f : ↥S ↦
      scalar ((f : ↥F) : ↥B) • y) := by
  rcases hgeometry with ⟨z, _hzB, _hzx, _hcomplement, hrow⟩
  intro f k htarget
  by_contra hfk
  let bf : ↥B := (f : ↥F)
  let bk : ↥B := (k : ↥F)
  have hownerNe : (bf : Fin n) ≠ (bk : Fin n) := by
    intro howner
    apply hfk
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact howner
  have hfRow := hrow f
  have hkRow := hrow k
  dsimp only at hfRow hkRow
  rcases hfRow with
    ⟨_hfOwner, _hfLabel, _hfCompanion, _hfZero, hfTarget⟩
  rcases hkRow with
    ⟨_hkOwner, _hkLabel, _hkCompanion, _hkZero, hkTarget⟩
  let common : G :=
    label.2 • g label.1 + (-(mu + label.2)) • g z
  have htarget' : scalar bf • y = scalar bk • y := by
    simpa only [bf, bk] using htarget
  have hscaled : mu • g (bf : Fin n) = mu • g (bk : Fin n) := by
    calc
      mu • g (bf : Fin n) = scalar bf • y - common := by
        rw [hfTarget]
        dsimp only [common]
        abel
      _ = scalar bk • y - common := by
        rw [htarget']
      _ = mu • g (bk : Fin n) := by
        rw [hkTarget]
        dsimp only [common]
        abel
  simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
    Finset.mem_singleton] at hmu
  rcases hmu with hminus | hone | htwo
  · have hneg : -g (bf : Fin n) = -g (bk : Fin n) := by
      simpa [hminus] using hscaled
    apply hownerNe
    exact (validTuple_injective g hg) (neg_injective hneg)
  · have heq : g (bf : Fin n) = g (bk : Fin n) := by
      simpa [hone] using hscaled
    exact hownerNe ((validTuple_injective g hg) heq)
  · have hdouble : (2 : ℤ) • g (bf : Fin n) =
        (2 : ℤ) • g (bk : Fin n) := by
      simpa [htwo] using hscaled
    exact hno (common_touched_of_two_smul_eq
      g hg hh hne hunique hownerNe hdouble)

/-- Uniform affine targets with owner coefficient `±1` amplify pointwise
distinctness to every equal-cardinality subset layer.  The common offset
cancels at fixed cardinality, leaving an ordinary tuple subset-sum equality;
all target sums remain in the cyclic subgroup generated by `y`. -/
theorem choose_le_addOrderOf_of_uniform_unit_affine_targets
    [Fintype G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → G) (hg : ValidTuple g)
    (owner : ι ↪ Fin n) (y offset : G) (target : ι → G)
    (mu : ℤ) (hmu : mu = -1 ∨ mu = 1)
    (haffine : ∀ i, target i = mu • g (owner i) + offset)
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (k : ℕ) :
    (Fintype.card ι).choose k ≤ addOrderOf y := by
  classical
  let L := (Finset.univ : Finset ι).powersetCard k
  let encode : ↥L → AddSubgroup.zmultiples y := fun S ↦
    ⟨∑ i ∈ S.1, target i,
      AddSubgroup.sum_mem _ fun i _ ↦ hmem i⟩
  have hencode : Function.Injective encode := by
    intro S T hST
    apply Subtype.ext
    apply validTuple_subsetSum_eq_of_card_eq g hg owner
    · have hScard := (Finset.mem_powersetCard.mp S.property).2
      have hTcard := (Finset.mem_powersetCard.mp T.property).2
      omega
    · have hval := congrArg Subtype.val hST
      dsimp only [encode] at hval
      simp_rw [haffine] at hval
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_zsmul, Finset.sum_zsmul] at hval
      simp only [Finset.sum_const] at hval
      have hScard := (Finset.mem_powersetCard.mp S.property).2
      have hTcard := (Finset.mem_powersetCard.mp T.property).2
      rw [hScard, hTcard] at hval
      have hscaled :
          mu • (∑ i ∈ S.1, g (owner i)) =
            mu • (∑ i ∈ T.1, g (owner i)) :=
        add_right_cancel hval
      rcases hmu with hminus | hone
      · have hneg : -(∑ i ∈ S.1, g (owner i)) =
            -(∑ i ∈ T.1, g (owner i)) := by
          simpa [hminus] using hscaled
        exact neg_injective hneg
      · simpa [hone] using hscaled
  have hcard := Fintype.card_le_of_injective encode hencode
  rw [Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_zmultiples] at hcard
  exact hcard

/-- Uniform affine targets with owner coefficient `2` still give a binomial
layer bound with only a factor-two loss when the ambient group has a unique
nonzero involution.  In one target-sum fiber, distinct owner-subset sums
differ by that involution; hence a third distinct subset would force two
owner-subset sums to coincide. -/
theorem choose_le_two_mul_addOrderOf_of_uniform_two_affine_targets
    [Fintype G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (owner : ι ↪ Fin n) (y offset : G) (target : ι → G)
    (haffine : ∀ i, target i = (2 : ℤ) • g (owner i) + offset)
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (k : ℕ) :
    (Fintype.card ι).choose k ≤ 2 * addOrderOf y := by
  classical
  let L := (Finset.univ : Finset ι).powersetCard k
  let encode : ↥L → AddSubgroup.zmultiples y := fun S ↦
    ⟨∑ i ∈ S.1, target i,
      AddSubgroup.sum_mem _ fun i _ ↦ hmem i⟩
  let ownerSum : ↥L → G := fun S ↦
    ∑ i ∈ S.1, g (owner i)
  have hownerSumInjective : Function.Injective ownerSum := by
    intro S T hST
    apply Subtype.ext
    apply validTuple_subsetSum_eq_of_card_eq g hg owner
    · have hScard := (Finset.mem_powersetCard.mp S.property).2
      have hTcard := (Finset.mem_powersetCard.mp T.property).2
      omega
    · simpa only [ownerSum] using hST
  have hdouble_of_encode_eq : ∀ {S T : ↥L}, encode S = encode T →
      (2 : ℤ) • ownerSum S = (2 : ℤ) • ownerSum T := by
    intro S T hST
    have hval := congrArg Subtype.val hST
    dsimp only [encode] at hval
    simp_rw [haffine] at hval
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_zsmul, Finset.sum_zsmul] at hval
    simp only [Finset.sum_const] at hval
    have hScard := (Finset.mem_powersetCard.mp S.property).2
    have hTcard := (Finset.mem_powersetCard.mp T.property).2
    rw [hScard, hTcard] at hval
    dsimp only [ownerSum]
    exact add_right_cancel hval
  have hsub_eq_involution_of_ne : ∀ {S T : ↥L},
      encode S = encode T → S ≠ T → ownerSum S - ownerSum T = h := by
    intro S T hencode hne
    have hdouble := hdouble_of_encode_eq hencode
    have htwoTorsion :
        (ownerSum S - ownerSum T) + (ownerSum S - ownerSum T) = 0 := by
      have hzsmul : (2 : ℤ) • (ownerSum S - ownerSum T) = 0 := by
        rw [zsmul_sub, hdouble, sub_self]
      simpa only [two_zsmul] using hzsmul
    rcases hunique (ownerSum S - ownerSum T) htwoTorsion with
      hzero | hinvolution
    · exact (hne (hownerSumInjective (sub_eq_zero.mp hzero))).elim
    · exact hinvolution
  rcases finiteMap_capacity_or_largeFiber
      (Finset.univ : Finset (AddSubgroup.zmultiples y))
        encode (fun _ ↦ Finset.mem_univ _) 2 with
    hcap | ⟨value, _hvalue, hlarge⟩
  · simpa only [L, Fintype.card_coe, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_zmultiples, Nat.mul_comm] using hcap
  · let fiber : Finset ↥L :=
      Finset.univ.filter (fun S : ↥L ↦ encode S = value)
    have hlarge' : 2 < fiber.card := by
      simpa only [fiber] using hlarge
    obtain ⟨S, T, U, hS, hT, hU, hST, hSU, hTU⟩ :=
      Finset.two_lt_card_iff.mp hlarge'
    have hencodeST : encode S = encode T :=
      (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hT).2.symm
    have hencodeSU : encode S = encode U :=
      (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hU).2.symm
    have hsubST := hsub_eq_involution_of_ne hencodeST hST
    have hsubSU := hsub_eq_involution_of_ne hencodeSU hSU
    have hsumTU : ownerSum T = ownerSum U :=
      sub_right_inj.mp (hsubST.trans hsubSU.symm)
    exact (hTU (hownerSumInjective hsumTU)).elim

/-- Joint balanced-layer capacity for a finite affine profile partition.
Choose a prescribed number of owners independently in every profile cell.
All cell offsets then cancel, while the normalized owner slope `2` leaves
fibers of size at most two by uniqueness of the involution. -/
theorem prod_profile_choose_le_two_mul_addOrderOf_of_uniform_two_affine_targets
    [Fintype G]
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (owner : ι ↪ Fin n) (profile : ι → β)
    (y : G) (offset : β → G) (target : ι → G)
    (haffine : ∀ i, target i =
      (2 : ℤ) • g (owner i) + offset (profile i))
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (k : β → ℕ) :
    (∏ q : β,
      ((Finset.univ.filter (fun i : ι ↦ profile i = q)).card.choose
        (k q))) ≤ 2 * addOrderOf y := by
  classical
  let cell : β → Finset ι := fun q ↦
    Finset.univ.filter (fun i : ι ↦ profile i = q)
  let cellChoices : β → Finset (Finset ι) := fun q ↦
    (cell q).powersetCard (k q)
  let choices : Finset (β → Finset ι) := Fintype.piFinset cellChoices
  have hchoiceCell : ∀ (A : ↥choices) (q : β), A.1 q ⊆ cell q := by
    intro A q
    exact (Finset.mem_powersetCard.mp
      (Fintype.mem_piFinset.mp A.property q)).1
  have hchoiceCard : ∀ (A : ↥choices) (q : β),
      (A.1 q).card = k q := by
    intro A q
    exact (Finset.mem_powersetCard.mp
      (Fintype.mem_piFinset.mp A.property q)).2
  have hchoiceDisjoint : ∀ A : ↥choices,
      (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
        (fun q ↦ A.1 q) := by
    intro A
    rw [Finset.pairwiseDisjoint_iff]
    intro q _ r _ hinter
    obtain ⟨i, hi⟩ := hinter
    have hi' := Finset.mem_inter.mp hi
    have hiq := hchoiceCell A q hi'.1
    have hir := hchoiceCell A r hi'.2
    have hq : profile i = q := (Finset.mem_filter.mp hiq).2
    have hr : profile i = r := (Finset.mem_filter.mp hir).2
    exact hq.symm.trans hr
  let selected : ↥choices → Finset ι := fun A ↦
    Finset.univ.biUnion (fun q ↦ A.1 q)
  have hselectedCell : ∀ (A : ↥choices) (q : β),
      (selected A).filter (fun i ↦ profile i = q) = A.1 q := by
    intro A q
    ext i
    constructor
    · intro hi
      have hiData := Finset.mem_filter.mp hi
      obtain ⟨r, _hr, hir⟩ := Finset.mem_biUnion.mp hiData.1
      have hirCell := hchoiceCell A r hir
      have hprofileR : profile i = r :=
        (Finset.mem_filter.mp hirCell).2
      have hrq : r = q := hprofileR.symm.trans hiData.2
      simpa only [hrq] using hir
    · intro hi
      have hiCell := hchoiceCell A q hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hi⟩,
          (Finset.mem_filter.mp hiCell).2⟩
  have hselectedInjective : Function.Injective selected := by
    intro A C hAC
    apply Subtype.ext
    funext q
    rw [← hselectedCell A q, ← hselectedCell C q, hAC]
  have hselectedCard : ∀ A : ↥choices,
      (selected A).card = ∑ q : β, k q := by
    intro A
    calc
      (selected A).card =
          ∑ q ∈ (Finset.univ : Finset β), (A.1 q).card := by
        exact Finset.card_biUnion (hchoiceDisjoint A)
      _ = ∑ q ∈ (Finset.univ : Finset β), k q := by
        exact Finset.sum_congr rfl fun q _ ↦ hchoiceCard A q
      _ = ∑ q : β, k q := by simp
  have hselectedSum : ∀ A : ↥choices,
      ∑ i ∈ selected A, g (owner i) =
        ∑ q : β, ∑ i ∈ A.1 q, g (owner i) := by
    intro A
    simpa only [selected, Finset.sum_const_zero, Finset.sum_attach,
      Finset.sum_filter] using
        (Finset.sum_biUnion (f := fun i ↦ g (owner i))
          (hchoiceDisjoint A))
  let ownerSum : ↥choices → G := fun A ↦
    ∑ q : β, ∑ i ∈ A.1 q, g (owner i)
  have hownerSumInjective : Function.Injective ownerSum := by
    intro A C hAC
    apply hselectedInjective
    apply validTuple_subsetSum_eq_of_card_eq g hg owner
    · rw [hselectedCard A, hselectedCard C]
    · rw [hselectedSum A, hselectedSum C]
      exact hAC
  let encode : ↥choices → AddSubgroup.zmultiples y := fun A ↦
    ⟨∑ q : β, ∑ i ∈ A.1 q, target i,
      AddSubgroup.sum_mem _ fun q _ ↦
        AddSubgroup.sum_mem _ fun i _ ↦ hmem i⟩
  have hsumAffine : ∀ A : ↥choices,
      (∑ q : β, ∑ i ∈ A.1 q, target i) =
        ∑ q : β,
          ((2 : ℤ) • (∑ i ∈ A.1 q, g (owner i)) +
            (k q) • offset q) := by
    intro A
    apply Finset.sum_congr rfl
    intro q _hq
    calc
      (∑ i ∈ A.1 q, target i) =
          ∑ i ∈ A.1 q,
            ((2 : ℤ) • g (owner i) + offset q) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [haffine]
        have hiCell := hchoiceCell A q hi
        rw [(Finset.mem_filter.mp hiCell).2]
      _ = (2 : ℤ) • (∑ i ∈ A.1 q, g (owner i)) +
          (k q) • offset q := by
        rw [Finset.sum_add_distrib, Finset.sum_zsmul,
          Finset.sum_const, hchoiceCard A q]
  have hdouble_of_encode_eq : ∀ {A C : ↥choices}, encode A = encode C →
      (2 : ℤ) • ownerSum A = (2 : ℤ) • ownerSum C := by
    intro A C hAC
    have hval := congrArg Subtype.val hAC
    dsimp only [encode] at hval
    rw [hsumAffine A, hsumAffine C] at hval
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_zsmul, Finset.sum_zsmul] at hval
    dsimp only [ownerSum]
    exact add_right_cancel hval
  have hsub_eq_involution_of_ne : ∀ {A C : ↥choices},
      encode A = encode C → A ≠ C → ownerSum A - ownerSum C = h := by
    intro A C hencode hne
    have hdouble := hdouble_of_encode_eq hencode
    have htwoTorsion :
        (ownerSum A - ownerSum C) + (ownerSum A - ownerSum C) = 0 := by
      have hzsmul : (2 : ℤ) • (ownerSum A - ownerSum C) = 0 := by
        rw [zsmul_sub, hdouble, sub_self]
      simpa only [two_zsmul] using hzsmul
    rcases hunique (ownerSum A - ownerSum C) htwoTorsion with
      hzero | hinvolution
    · exact (hne (hownerSumInjective (sub_eq_zero.mp hzero))).elim
    · exact hinvolution
  rcases finiteMap_capacity_or_largeFiber
      (Finset.univ : Finset (AddSubgroup.zmultiples y))
        encode (fun _ ↦ Finset.mem_univ _) 2 with
    hcap | ⟨value, _hvalue, hlarge⟩
  · have hchoicesCard : choices.card =
        ∏ q : β, (cell q).card.choose (k q) := by
      simp only [choices, Fintype.card_piFinset, cellChoices,
        Finset.card_powersetCard]
    rw [Fintype.card_coe, hchoicesCard,
      Finset.card_univ, Fintype.card_zmultiples] at hcap
    simpa only [cell, Nat.mul_comm] using hcap
  · let fiber : Finset ↥choices :=
      Finset.univ.filter (fun A : ↥choices ↦ encode A = value)
    have hlarge' : 2 < fiber.card := by
      simpa only [fiber] using hlarge
    obtain ⟨A, C, D, hA, hC, hD, hAC, hAD, hCD⟩ :=
      Finset.two_lt_card_iff.mp hlarge'
    have hencodeAC : encode A = encode C :=
      (Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hC).2.symm
    have hencodeAD : encode A = encode D :=
      (Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hD).2.symm
    have hsubAC := hsub_eq_involution_of_ne hencodeAC hAC
    have hsubAD := hsub_eq_involution_of_ne hencodeAD hAD
    have hsumCD : ownerSum C = ownerSum D :=
      sub_right_inj.mp (hsubAC.trans hsubAD.symm)
    exact (hCD (hownerSumInjective hsumCD)).elim

/-- Capacity after replacing a complete profile-count vector by its two
actual affine invariants: total cardinality and total offset weight.  This
allows the cell counts to vary freely inside one weighted layer. -/
theorem card_fixedCard_weightSum_le_two_mul_addOrderOf_of_affine_targets
    [Fintype G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (owner : ι ↪ Fin n) (weight : ι → ℤ)
    (y delta base : G) (target : ι → G)
    (haffine : ∀ i, target i =
      (2 : ℤ) • g (owner i) + weight i • delta + base)
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (k : ℕ) (w : ℤ) :
    ((Finset.univ.powersetCard k).filter (fun A : Finset ι ↦
      ∑ i ∈ A, weight i = w)).card ≤ 2 * addOrderOf y := by
  classical
  let L : Finset (Finset ι) :=
    (Finset.univ.powersetCard k).filter (fun A : Finset ι ↦
      ∑ i ∈ A, weight i = w)
  let ownerSum : ↥L → G := fun A ↦
    ∑ i ∈ A.1, g (owner i)
  have hchoiceCard : ∀ A : ↥L, A.1.card = k := by
    intro A
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp A.property).1).2
  have hchoiceWeight : ∀ A : ↥L,
      ∑ i ∈ A.1, weight i = w := by
    intro A
    exact (Finset.mem_filter.mp A.property).2
  have hownerSumInjective : Function.Injective ownerSum := by
    intro A C hAC
    apply Subtype.ext
    apply validTuple_subsetSum_eq_of_card_eq g hg owner
    · rw [hchoiceCard A, hchoiceCard C]
    · simpa only [ownerSum] using hAC
  let encode : ↥L → AddSubgroup.zmultiples y := fun A ↦
    ⟨∑ i ∈ A.1, target i,
      AddSubgroup.sum_mem _ fun i _ ↦ hmem i⟩
  have hsumAffine : ∀ A : ↥L,
      (∑ i ∈ A.1, target i) =
        (2 : ℤ) • ownerSum A + w • delta + k • base := by
    intro A
    calc
      (∑ i ∈ A.1, target i) =
          ∑ i ∈ A.1,
            ((2 : ℤ) • g (owner i) + weight i • delta + base) := by
        exact Finset.sum_congr rfl fun i _ ↦ haffine i
      _ = (2 : ℤ) • ownerSum A + w • delta + k • base := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_zsmul, ← Finset.sum_smul, Finset.sum_const,
          hchoiceWeight A, hchoiceCard A]
  have hdouble_of_encode_eq : ∀ {A C : ↥L}, encode A = encode C →
      (2 : ℤ) • ownerSum A = (2 : ℤ) • ownerSum C := by
    intro A C hAC
    have hval := congrArg Subtype.val hAC
    dsimp only [encode] at hval
    rw [hsumAffine A, hsumAffine C] at hval
    exact add_right_cancel (add_right_cancel hval)
  have hsub_eq_involution_of_ne : ∀ {A C : ↥L},
      encode A = encode C → A ≠ C → ownerSum A - ownerSum C = h := by
    intro A C hencode hne
    have hdouble := hdouble_of_encode_eq hencode
    have htwoTorsion :
        (ownerSum A - ownerSum C) + (ownerSum A - ownerSum C) = 0 := by
      have hzsmul : (2 : ℤ) • (ownerSum A - ownerSum C) = 0 := by
        rw [zsmul_sub, hdouble, sub_self]
      simpa only [two_zsmul] using hzsmul
    rcases hunique (ownerSum A - ownerSum C) htwoTorsion with
      hzero | hinvolution
    · exact (hne (hownerSumInjective (sub_eq_zero.mp hzero))).elim
    · exact hinvolution
  rcases finiteMap_capacity_or_largeFiber
      (Finset.univ : Finset (AddSubgroup.zmultiples y))
        encode (fun _ ↦ Finset.mem_univ _) 2 with
    hcap | ⟨value, _hvalue, hlarge⟩
  · rw [Fintype.card_coe, Finset.card_univ,
      Fintype.card_zmultiples] at hcap
    simpa only [L, Nat.mul_comm] using hcap
  · let fiber : Finset ↥L :=
      Finset.univ.filter (fun A : ↥L ↦ encode A = value)
    have hlarge' : 2 < fiber.card := by
      simpa only [fiber] using hlarge
    obtain ⟨A, C, D, hA, hC, hD, hAC, hAD, hCD⟩ :=
      Finset.two_lt_card_iff.mp hlarge'
    have hencodeAC : encode A = encode C :=
      (Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hC).2.symm
    have hencodeAD : encode A = encode D :=
      (Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hD).2.symm
    have hsubAC := hsub_eq_involution_of_ne hencodeAC hAC
    have hsubAD := hsub_eq_involution_of_ne hencodeAD hAD
    have hsumCD : ownerSum C = ownerSum D :=
      sub_right_inj.mp (hsubAC.trans hsubAD.symm)
    exact (hCD (hownerSumInjective hsumCD)).elim

/-- The all-row normalized certificate behind the 18-profile decomposition.
Every private row carries its complete finite label and, after the canonical
owner rescaling, has owner slope exactly `2`; no dominant subfamily has been
selected. -/
def TwoRetainedMinimalCyclicKernelNormalizedRows
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (scalar : ↥B → ℤ) (coeff : ↥B → Fin n → ℤ)
    (supportCoord : ↥B → Fin n) : Prop :=
  ∀ b : ↥B,
    (((supportCoord b, coeff b (supportCoord b)),
        coeff b (b : Fin n)) ∈ twoRetainedPrivateProfileLabels B) ∧
      ∃ companion : Fin n,
        companion ∉ B ∧ companion ≠ supportCoord b ∧
        Finset.univ \ B = {supportCoord b, companion} ∧
        twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
            (scalar b • y) =
          (2 : ℤ) • g (b : Fin n) +
            twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
              (coeff b (supportCoord b) • g (supportCoord b) +
                (-(coeff b (b : Fin n) + coeff b (supportCoord b))) •
                  g companion)

/-- Apply the joint balanced-layer theorem to every row of the canonical
18-profile exact-two certificate.  The returned profile map covers all of
`B`, and arbitrary prescribed layer sizes are allowed in its cells. -/
theorem TwoRetainedMinimalCyclicKernelNormalizedRows.profileProductChoose_le
    [Fintype G] [DecidableEq G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (y : G) (B : Finset (Fin n))
    (scalar : ↥B → ℤ) (coeff : ↥B → Fin n → ℤ)
    (supportCoord : ↥B → Fin n)
    (hretained : n - B.card = 2)
    (hnormalized : TwoRetainedMinimalCyclicKernelNormalizedRows
      g y B scalar coeff supportCoord)
    (k : ↥(twoRetainedPrivateProfileLabels B) → ℕ) :
    ∃ profile : ↥B → ↥(twoRetainedPrivateProfileLabels B),
      (∏ q : ↥(twoRetainedPrivateProfileLabels B),
        ((Finset.univ.filter (fun b : ↥B ↦ profile b = q)).card.choose
          (k q))) ≤ 2 * addOrderOf y := by
  classical
  have hcomplementCard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  obtain ⟨x, z, hxz, hcomplement⟩ :=
    Finset.card_eq_two.mp hcomplementCard
  let companionOf : Fin n → Fin n := fun a ↦ if a = x then z else x
  have hcompanionUnique : ∀ a c : Fin n,
      a ∈ Finset.univ \ B → c ∈ Finset.univ \ B → c ≠ a →
        c = companionOf a := by
    intro a c haC hcC hca
    have haPair : a = x ∨ a = z := by
      rw [hcomplement] at haC
      simpa only [Finset.mem_insert, Finset.mem_singleton] using haC
    have hcPair : c = x ∨ c = z := by
      rw [hcomplement] at hcC
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcC
    rcases haPair with rfl | rfl
    · have hcz : c = z := hcPair.resolve_left hca
      subst c
      simp only [companionOf, if_pos]
    · have hcx : c = x := hcPair.resolve_right hca
      subst c
      simp only [companionOf, if_neg hxz.symm]
  let owner : ↥B ↪ Fin n :=
    { toFun := fun b ↦ b
      inj' := Subtype.coe_injective }
  let rawProfile : ↥B → ((Fin n × ℤ) × ℤ) := fun b ↦
    ((supportCoord b, coeff b (supportCoord b)),
      coeff b (b : Fin n))
  let profile : ↥B → ↥(twoRetainedPrivateProfileLabels B) := fun b ↦
    ⟨rawProfile b, (hnormalized b).1⟩
  let offset : ↥(twoRetainedPrivateProfileLabels B) → G := fun q ↦
    let label : ((Fin n × ℤ) × ℤ) := q
    twoRetainedOwnerNormalization label.2 •
      (label.1.2 • g label.1.1 +
        (-(label.2 + label.1.2)) • g (companionOf label.1.1))
  let target : ↥B → G := fun b ↦
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
      (scalar b • y)
  have haffine : ∀ b : ↥B,
      target b = (2 : ℤ) • g (owner b) + offset (profile b) := by
    intro b
    rcases (hnormalized b).2 with
      ⟨companion, hcompanionB, hcompanionNe,
        _hrowComplement, hrow⟩
    have hsupportC : supportCoord b ∈ Finset.univ \ B :=
      (Finset.mem_product.mp
        (Finset.mem_product.mp (hnormalized b).1).1).1
    have hcompanionC : companion ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcompanionB⟩
    have hcompanionEq := hcompanionUnique
      (supportCoord b) companion hsupportC hcompanionC hcompanionNe
    have howner : owner b = (b : Fin n) := rfl
    rw [howner]
    simpa only [target, offset, profile, rawProfile,
      hcompanionEq] using hrow
  have htargetMem : ∀ b : ↥B,
      target b ∈ AddSubgroup.zmultiples y := by
    intro b
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
  refine ⟨profile, ?_⟩
  exact
    prod_profile_choose_le_two_mul_addOrderOf_of_uniform_two_affine_targets
      g hg hunique owner profile y offset target haffine htargetMem k

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
        TwoRetainedMinimalCyclicKernelNormalizedRows
          g y B scalar coeff supportCoord ∧
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
                    g y B scalar coeff label F mu S ∧
                  Function.Injective (fun f : ↥S ↦
                    scalar ((f : ↥F) : ↥B) • y) ∧
                  S.card ≤ addOrderOf y - 1 ∧
                  B.card ≤ 18 * (addOrderOf y - 1) ∧
                  (mu = 2 ∨ ∀ k : ℕ,
                    S.card.choose k ≤ addOrderOf y) ∧
                  (∀ k : ℕ,
                    S.card.choose k ≤ 2 * addOrderOf y))

/-- Minimality supplies the full exact-two private-row family canonically;
unlike the cycle-owned subfamily, this retains every deleted coordinate. -/
theorem twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
    [Fintype G] [DecidableEq G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : G) {B : Finset (Fin n)}
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
  have hcomplementCardAll : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  have hnormalizedRows : TwoRetainedMinimalCyclicKernelNormalizedRows
      g y B (fun b ↦ (data b).scalar) (fun b ↦ (data b).coeff)
        supportCoord := by
    intro b
    rcases hrowData b with
      ⟨_htarget, hwitness, _howner, hownerLevel, hprivate,
        hsupportB, _hsupportNonzero, hsupportLevel⟩
    refine ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ _, hsupportB⟩, hsupportLevel⟩,
          hownerLevel⟩
    · have hxC : supportCoord b ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsupportB⟩
      have hCone : 1 < (Finset.univ \ B).card := by omega
      obtain ⟨u, huC, v, hvC, huv⟩ := Finset.one_lt_card.mp hCone
      obtain ⟨companion, hcompanionC, hcompanionNe⟩ :
          ∃ companion ∈ Finset.univ \ B,
            companion ≠ supportCoord b := by
        by_cases hu : u = supportCoord b
        · refine ⟨v, hvC, ?_⟩
          intro hv
          exact huv (hu.trans hv.symm)
        · exact ⟨u, huC, hu⟩
      have hcompanionB : companion ∉ B :=
        (Finset.mem_sdiff.mp hcompanionC).2
      have hcomplement : Finset.univ \ B =
          {supportCoord b, companion} :=
        finset_eq_pair_of_card_eq_two_of_mem
          hcomplementCardAll hxC hcompanionC hcompanionNe.symm
      refine ⟨companion, hcompanionB, hcompanionNe, hcomplement, ?_⟩
      exact privateWitness_twoRetained_normalizedAffine
        g y (data b).scalar hwitness B (b : Fin n) b.property hprivate
          (supportCoord b) companion hsupportB hcompanionB
            hcompanionNe.symm hcomplement hownerLevel
  refine ⟨hretained, (fun b ↦ (data b).scalar),
    (fun b ↦ (data b).coeff), supportCoord,
    minimalCyclicKernelPrivateWitness_coeff_injective g y hmin,
    hrowData, hnormalizedRows, ?_⟩
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
    have htargetInjective : Function.Injective (fun f : ↥S ↦
        (data ((f : ↥F) : ↥B)).scalar • y) :=
      hgeometry.target_injective g hg hh hne hunique hno y B
        (fun b ↦ (data b).scalar) (fun b ↦ (data b).coeff)
          z F mu S hmu
    have htargetNonzero : ∀ f : ↥S,
        (data ((f : ↥F) : ↥B)).scalar • y ≠ 0 := by
      intro f
      exact (hrowData ((f : ↥F) : ↥B)).1
    have hSorder : S.card ≤ addOrderOf y - 1 := by
      have hcard :=
        card_le_addOrderOf_sub_one_of_injective_nonzero_zsmul y
          (fun f : ↥S ↦ (data ((f : ↥F) : ↥B)).scalar)
          htargetNonzero htargetInjective
      simpa only [Fintype.card_coe] using hcard
    have hBorder : B.card ≤ 18 * (addOrderOf y - 1) :=
      hBprofile.trans (Nat.mul_le_mul_left 18 hSorder)
    have hprofileLayers : mu = 2 ∨ ∀ k : ℕ,
        S.card.choose k ≤ addOrderOf y := by
      by_cases hmuTwo : mu = 2
      · exact Or.inl hmuTwo
      · right
        have hmuUnit : mu = -1 ∨ mu = 1 := by
          have hlevels := hmu
          simp only [twoRetainedExternalCoefficientLevels,
            Finset.mem_insert, Finset.mem_singleton] at hlevels
          rcases hlevels with hminus | hone | htwo
          · exact Or.inl hminus
          · exact Or.inr hone
          · exact (hmuTwo htwo).elim
        have hgeometryCopy := hgeometry
        rcases hgeometryCopy with
          ⟨companion, _hcompanionB, _hcompanionNe,
            _hcomplement, hgeometryRow⟩
        let ownerEmbedding : ↥S ↪ Fin n :=
          { toFun := fun f ↦ (((f : ↥S) : ↥F) : ↥B)
            inj' := by
              intro f k hfk
              apply Subtype.ext
              apply Subtype.ext
              apply Subtype.ext
              exact hfk }
        let offset : G :=
          z.2 • g z.1 + (-(mu + z.2)) • g companion
        let target : ↥S → G := fun f ↦
          (data (((f : ↥S) : ↥F) : ↥B)).scalar • y
        have haffine : ∀ f : ↥S,
            target f = mu • g (ownerEmbedding f) + offset := by
          intro f
          have howner : ownerEmbedding f =
              (((f : ↥S) : ↥F) : ↥B) := rfl
          rw [howner]
          simpa only [target, ownerEmbedding, offset, add_assoc] using
            (hgeometryRow f).2.2.2.2
        have htargetMem : ∀ f : ↥S,
            target f ∈ AddSubgroup.zmultiples y := by
          intro f
          exact AddSubgroup.zsmul_mem _
            (AddSubgroup.mem_zmultiples y) _
        intro k
        have hlayer :=
          choose_le_addOrderOf_of_uniform_unit_affine_targets
            g hg ownerEmbedding y offset target mu hmuUnit
              haffine htargetMem k
        simpa only [Fintype.card_coe] using hlayer
    have hprofileLayersUniform : ∀ k : ℕ,
        S.card.choose k ≤ 2 * addOrderOf y := by
      by_cases hmuTwo : mu = 2
      · have hgeometryCopy := hgeometry
        rcases hgeometryCopy with
          ⟨companion, _hcompanionB, _hcompanionNe,
            _hcomplement, hgeometryRow⟩
        let ownerEmbedding : ↥S ↪ Fin n :=
          { toFun := fun f ↦ (((f : ↥S) : ↥F) : ↥B)
            inj' := by
              intro f k hfk
              apply Subtype.ext
              apply Subtype.ext
              apply Subtype.ext
              exact hfk }
        let offset : G :=
          z.2 • g z.1 + (-(mu + z.2)) • g companion
        let target : ↥S → G := fun f ↦
          (data (((f : ↥S) : ↥F) : ↥B)).scalar • y
        have haffine : ∀ f : ↥S,
            target f = (2 : ℤ) • g (ownerEmbedding f) + offset := by
          intro f
          have howner : ownerEmbedding f =
              (((f : ↥S) : ↥F) : ↥B) := rfl
          rw [howner]
          simpa only [target, ownerEmbedding, offset, hmuTwo,
            add_assoc] using (hgeometryRow f).2.2.2.2
        have htargetMem : ∀ f : ↥S,
            target f ∈ AddSubgroup.zmultiples y := by
          intro f
          exact AddSubgroup.zsmul_mem _
            (AddSubgroup.mem_zmultiples y) _
        intro k
        have hlayer :=
          choose_le_two_mul_addOrderOf_of_uniform_two_affine_targets
            g hg hunique ownerEmbedding y offset target
              haffine htargetMem k
        simpa only [Fintype.card_coe] using hlayer
      · have hunit := hprofileLayers.resolve_left hmuTwo
        intro k
        have hlayer := hunit k
        omega
    refine ⟨z, hz, ?_⟩
    dsimp only
    refine ⟨hFnonempty', hBdominant, mu, hmu,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [S, ownerLevel]
    · simpa only [S, ownerLevel] using hFprofile
    · simpa only [S, ownerLevel] using hBprofile
    · simpa only [F, label, S, ownerLevel] using hgeometry
    · simpa only [F, label, S, ownerLevel] using htargetInjective
    · simpa only [F, label, S, ownerLevel] using hSorder
    · simpa only [F, label, S, ownerLevel] using hBorder
    · simpa only [F, label, S, ownerLevel] using hprofileLayers
    · simpa only [F, label, S, ownerLevel] using hprofileLayersUniform

/-- Global five-weight form of the exact-two private family.  Once the two
retained coordinates are named, every row has one of five normalized weights
on their difference; the former 18 profile labels no longer appear in the
affine equation. -/
def TwoRetainedMinimalCyclicKernelFiveWeightRows
    (g : Fin n → G) (y : G) (B : Finset (Fin n)) : Prop :=
  n - B.card = 2 ∧
    ∃ x z : Fin n, ∃ scalar : ↥B → ℤ,
      ∃ coeff : ↥B → Fin n → ℤ, ∃ weight : ↥B → ℤ,
        x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
        Function.Injective coeff ∧
        (∀ b : ↥B,
          scalar b • y ≠ 0 ∧
          Witness g (scalar b • y) (coeff b) ∧
          coeff b (b : Fin n) ≠ 0 ∧
          coeff b (b : Fin n) ∈ twoRetainedExternalCoefficientLevels ∧
          (∀ a ∈ B, a ≠ (b : Fin n) → coeff b a = 0)) ∧
        ∀ b : ↥B,
          weight b ∈ twoRetainedNormalizedWeightLevels ∧
          (weight b = -1 ↔ coeff b (b : Fin n) = 2) ∧
          twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
              (scalar b • y) =
            (2 : ℤ) • g (b : Fin n) +
              weight b • (g x - g z) - (2 : ℤ) • g z

/-- Forget the artificial support-coordinate choice in the 18-profile
package and retain only its canonical five-weight affine content. -/
theorem TwoRetainedMinimalCyclicKernelPrivateRows.fiveWeightRows
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelPrivateRows g y B) :
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B := by
  classical
  rcases hrows with
    ⟨hretained, scalar, coeff, _supportCoord, hcoeffInjective,
      hrowData, _hnormalized, _hdominant⟩
  have hcomplementCard : (Finset.univ \ B).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simpa using hretained
  obtain ⟨x, z, hxz, hcomplement⟩ :=
    Finset.card_eq_two.mp hcomplementCard
  have hxC : x ∈ Finset.univ \ B := by
    rw [hcomplement]
    simp
  have hzC : z ∈ Finset.univ \ B := by
    rw [hcomplement]
    simp
  have hxB : x ∉ B := (Finset.mem_sdiff.mp hxC).2
  have hzB : z ∉ B := (Finset.mem_sdiff.mp hzC).2
  let weight : ↥B → ℤ := fun b ↦
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) * coeff b x
  refine ⟨hretained, x, z, scalar, coeff, weight,
    hxB, hzB, hxz, hcomplement, hcoeffInjective, ?_, ?_⟩
  · intro b
    rcases hrowData b with
      ⟨htarget, hwitness, howner, hownerLevel, hprivate,
        _hsupportB, _hsupport, _hsupportLevel⟩
    exact ⟨htarget, hwitness, howner, hownerLevel, hprivate⟩
  · intro b
    rcases hrowData b with
      ⟨_htarget, hwitness, _howner, hownerLevel, hprivate,
        _hsupportB, _hsupport, _hsupportLevel⟩
    simpa only [weight] using
      privateWitness_twoRetained_fiveWeightAffine
        g y (scalar b) hwitness B (b : Fin n) b.property hprivate
          x z hxB hzB hxz hcomplement hownerLevel

/-- Canonical exact-two specialization of the varying-profile weighted-layer
bound.  All cell-count vectors with the same total size and the same one
dimensional retained weight participate in a single factor-two fiber bound. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fixedCardWeightSum_le
    [Fintype G] [DecidableEq G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (k : ℕ) (w : ℤ) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((Finset.univ.powersetCard k).filter (fun A : Finset ↥B ↦
        ∑ b ∈ A, weight b = w)).card ≤ 2 * addOrderOf y := by
  classical
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      hrowData, hweightData⟩
  let owner : ↥B ↪ Fin n :=
    { toFun := fun b ↦ b
      inj' := Subtype.coe_injective }
  let target : ↥B → G := fun b ↦
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
      (scalar b • y)
  let base : G := -(2 : ℤ) • g z
  have haffine : ∀ b, target b =
      (2 : ℤ) • g (owner b) + weight b • (g x - g z) + base := by
    intro b
    have hrow := (hweightData b).2.2
    have howner : owner b = (b : Fin n) := rfl
    rw [howner]
    simpa only [target, base, sub_eq_add_neg, neg_zsmul] using hrow
  have htargetMem : ∀ b, target b ∈ AddSubgroup.zmultiples y := by
    intro b
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, ?_⟩
  exact card_fixedCard_weightSum_le_two_mul_addOrderOf_of_affine_targets
    g hg hunique owner weight y (g x - g z) base target
      haffine htargetMem k w

/-- Substituting a doubling transition into two five-weight affine rows.
The target difference belongs to the cyclic kernel, so the displayed
retained-coordinate expression does as well. -/
theorem fiveWeightAffine_transition_mem_zmultiples
    {ι : Type*} (g : Fin n → G) (y a : G)
    (owner : ι → Fin n) (R : ι → ι)
    (x z : Fin n) (weight : ι → ℤ) (target : ι → G)
    (haffine : ∀ i, target i =
      (2 : ℤ) • g (owner i) + weight i • (g x - g z) -
        (2 : ℤ) • g z)
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (hdouble : ∀ i,
      g (owner (R i)) - a = (2 : ℤ) • (g (owner i) - a))
    (i : ι) :
    (weight (R i) - 2 * weight i) • (g x - g z) +
        (2 : ℤ) • (g z - a) ∈ AddSubgroup.zmultiples y := by
  have hownerR :
      g (owner (R i)) = (2 : ℤ) • g (owner i) - a := by
    calc
      g (owner (R i)) = (g (owner (R i)) - a) + a := by abel
      _ = (2 : ℤ) • (g (owner i) - a) + a := by rw [hdouble i]
      _ = (2 : ℤ) • g (owner i) - a := by
        rw [zsmul_sub]
        abel
  have htargetIdentity :
      target (R i) - (2 : ℤ) • target i =
        (weight (R i) - 2 * weight i) • (g x - g z) +
          (2 : ℤ) • (g z - a) := by
    rw [haffine (R i), haffine i, hownerR]
    module
  rw [← htargetIdentity]
  exact AddSubgroup.sub_mem _ (hmem (R i))
    (AddSubgroup.zsmul_mem _ (hmem i) 2)

/-- Two cycle transitions eliminate the common affine translate.  Their
integer transition-coefficient difference annihilates the retained
difference modulo the cyclic kernel. -/
theorem fiveWeightAffine_transitionCoefficient_sub_smul_mem_zmultiples
    {ι : Type*} (g : Fin n → G) (y a : G)
    (owner : ι → Fin n) (R : ι → ι)
    (x z : Fin n) (weight : ι → ℤ) (target : ι → G)
    (haffine : ∀ i, target i =
      (2 : ℤ) • g (owner i) + weight i • (g x - g z) -
        (2 : ℤ) • g z)
    (hmem : ∀ i, target i ∈ AddSubgroup.zmultiples y)
    (hdouble : ∀ i,
      g (owner (R i)) - a = (2 : ℤ) • (g (owner i) - a))
    (i j : ι) :
    ((weight (R i) - 2 * weight i) -
        (weight (R j) - 2 * weight j)) • (g x - g z) ∈
      AddSubgroup.zmultiples y := by
  have hi := fiveWeightAffine_transition_mem_zmultiples
    g y a owner R x z weight target haffine hmem hdouble i
  have hj := fiveWeightAffine_transition_mem_zmultiples
    g y a owner R x z weight target haffine hmem hdouble j
  have hsub := AddSubgroup.sub_mem _ hi hj
  convert hsub using 1
  module

/-- One transition version, for a family only partially closed under the
doubling map.  This is the form used by deleted cycle leaves. -/
theorem fiveWeightAffine_pairTransition_mem_zmultiples
    (g : Fin n → G) (y a : G) (x z b c : Fin n)
    (wb wc : ℤ) (tb tc : G)
    (hb : tb = (2 : ℤ) • g b + wb • (g x - g z) - (2 : ℤ) • g z)
    (hc : tc = (2 : ℤ) • g c + wc • (g x - g z) - (2 : ℤ) • g z)
    (htb : tb ∈ AddSubgroup.zmultiples y)
    (htc : tc ∈ AddSubgroup.zmultiples y)
    (hdouble : g c - a = (2 : ℤ) • (g b - a)) :
    (wc - 2 * wb) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
      AddSubgroup.zmultiples y := by
  have hcValue : g c = (2 : ℤ) • g b - a := by
    calc
      g c = (g c - a) + a := by abel
      _ = (2 : ℤ) • (g b - a) + a := by rw [hdouble]
      _ = (2 : ℤ) • g b - a := by
        rw [zsmul_sub]
        abel
  have hidentity :
      tc - (2 : ℤ) • tb =
        (wc - 2 * wb) • (g x - g z) + (2 : ℤ) • (g z - a) := by
    rw [hb, hc, hcValue]
    module
  rw [← hidentity]
  exact AddSubgroup.sub_mem _ htc (AddSubgroup.zsmul_mem _ htb 2)

/-- Two successive doubling transitions across one unavailable intermediate
row.  The endpoint target difference has multiplier four and uniform
translate `6 • (g z - a)`. -/
theorem fiveWeightAffine_pairFourTransition_mem_zmultiples
    (g : Fin n → G) (y a : G) (x z b c : Fin n)
    (wb wc : ℤ) (tb tc : G)
    (hb : tb = (2 : ℤ) • g b + wb • (g x - g z) - (2 : ℤ) • g z)
    (hc : tc = (2 : ℤ) • g c + wc • (g x - g z) - (2 : ℤ) • g z)
    (htb : tb ∈ AddSubgroup.zmultiples y)
    (htc : tc ∈ AddSubgroup.zmultiples y)
    (hfour : g c - a = (4 : ℤ) • (g b - a)) :
    (wc - 4 * wb) • (g x - g z) + (6 : ℤ) • (g z - a) ∈
      AddSubgroup.zmultiples y := by
  have hcValue : g c = (4 : ℤ) • g b - (3 : ℤ) • a := by
    calc
      g c = (g c - a) + a := by abel
      _ = (4 : ℤ) • (g b - a) + a := by rw [hfour]
      _ = (4 : ℤ) • g b - (3 : ℤ) • a := by
        rw [zsmul_sub]
        module
  have hidentity :
      tc - (4 : ℤ) • tb =
        (wc - 4 * wb) • (g x - g z) + (6 : ℤ) • (g z - a) := by
    rw [hb, hc, hcValue]
    module
  rw [← hidentity]
  exact AddSubgroup.sub_mem _ htc (AddSubgroup.zsmul_mem _ htb 4)

/-- Every deleted-to-deleted transition of the saturated cycle inherits the
five-weight kernel invariant from the full minimal-transversal family. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.cycleTransition_mem
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {ι : Type*} (leaf : ι → Fin n) (R : ι → ι) (a : G)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
          (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
              (g x - g z) + (2 : ℤ) • (g z - a) ∈
            AddSubgroup.zmultiples y) ∧
      ∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B)
          j (hj : leaf j ∈ B) (hRj : leaf (R j) ∈ B),
        ((weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) -
            (weight ⟨leaf (R j), hRj⟩ - 2 * weight ⟨leaf j, hj⟩)) •
              (g x - g z) ∈ AddSubgroup.zmultiples y := by
  classical
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  let target : ↥B → G := fun b ↦
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
      (scalar b • y)
  have htargetMem : ∀ b, target b ∈ AddSubgroup.zmultiples y := by
    intro b
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
  have htransition : ∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
      (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
          (g x - g z) + (2 : ℤ) • (g z - a) ∈
        AddSubgroup.zmultiples y := by
    intro i hi hRi
    let b : ↥B := ⟨leaf i, hi⟩
    let c : ↥B := ⟨leaf (R i), hRi⟩
    exact fiveWeightAffine_pairTransition_mem_zmultiples
      g y a x z (b : Fin n) (c : Fin n) (weight b) (weight c)
        (target b) (target c) (hweightData b).2.2 (hweightData c).2.2
          (htargetMem b) (htargetMem c) (hdouble i)
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, htransition, ?_⟩
  intro i hi hRi j hj hRj
  have hiMem := htransition i hi hRi
  have hjMem := htransition j hj hRj
  have hsub := AddSubgroup.sub_mem _ hiMem hjMem
  convert hsub using 1
  module

theorem twoRetainedNormalizedWeight_bounds
    {w : ℤ} (hw : w ∈ twoRetainedNormalizedWeightLevels) :
    -4 ≤ w ∧ w ≤ 2 := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hw
  omega

/-- Exact arithmetic classification of the top surviving punctured-cycle
coefficient.  Four and only four five-weight configurations can make the
boundary expression have absolute value `32`. -/
theorem fiveWeight_boundaryCoefficient_natAbs_eq_thirtyTwo
    (u v a b : ℤ)
    (hu : u ∈ twoRetainedNormalizedWeightLevels)
    (hv : v ∈ twoRetainedNormalizedWeightLevels)
    (ha : a ∈ twoRetainedNormalizedWeightLevels)
    (hb : b ∈ twoRetainedNormalizedWeightLevels)
    (habs : (v - 4 * u - 3 * (b - 2 * a)).natAbs = 32) :
    (u = -4 ∧ v = -2 ∧ a = 2 ∧ b = -2) ∨
    (u = -2 ∧ v = 0 ∧ a = 2 ∧ b = -4) ∨
    (u = 0 ∧ v = -2 ∧ a = -4 ∧ b = 2) ∨
    (u = 2 ∧ v = 0 ∧ a = -4 ∧ b = 0) := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hu hv ha hb
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num at habs <;> norm_num

/-- A bounded integer weight on a finite functional graph is constant when
`weight(R i) - 2*weight(i)` is constant.  The proof uses only the minimum
and maximum weights, so no cycle enumeration is needed. -/
theorem weight_constant_of_transitionCoefficient_constant
    {ι : Type*} [Fintype ι] (i₀ : ι)
    (R : ι → ι) (weight : ι → ℤ)
    (hcoefficient : ∀ i j,
      weight (R i) - 2 * weight i = weight (R j) - 2 * weight j) :
    ∀ i j, weight i = weight j := by
  classical
  have huniv : (Finset.univ : Finset ι).Nonempty :=
    ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨imin, _himin, hmin⟩ :=
    Finset.exists_min_image Finset.univ weight huniv
  obtain ⟨imax, _himax, hmax⟩ :=
    Finset.exists_max_image Finset.univ weight huniv
  have hminStep : weight imin ≤ weight (R imin) :=
    hmin (R imin) (Finset.mem_univ _)
  have hmaxStep : weight (R imax) ≤ weight imax :=
    hmax (R imax) (Finset.mem_univ _)
  have hcoeff := hcoefficient imin imax
  have hminmax : weight imin ≤ weight imax :=
    hmin imax (Finset.mem_univ _)
  have hmaxmin : weight imax ≤ weight imin := by omega
  intro i j
  have hmini : weight imin ≤ weight i := hmin i (Finset.mem_univ _)
  have himaxi : weight i ≤ weight imax := hmax i (Finset.mem_univ _)
  have hminj : weight imin ≤ weight j := hmin j (Finset.mem_univ _)
  have hjmax : weight j ≤ weight imax := hmax j (Finset.mem_univ _)
  omega

/-- The five-weight transition invariant has only two outcomes.  Either all
integer transition coefficients agree, forcing every weight to be equal, or
a nonzero integer of absolute value at most 18 sends the retained difference
into the cyclic kernel. -/
theorem fiveWeightTransition_smallKernelMultiple_or_weight_constant
    {ι : Type*} [Fintype ι] (i₀ : ι)
    (R : ι → ι) (weight : ι → ℤ)
    (hweight : ∀ i, weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta : G) (y : G)
    (hpair : ∀ i j,
      ((weight (R i) - 2 * weight i) -
          (weight (R j) - 2 * weight j)) • delta ∈
        AddSubgroup.zmultiples y) :
    (∃ e : ℤ, e ≠ 0 ∧ -18 ≤ e ∧ e ≤ 18 ∧
        e • delta ∈ AddSubgroup.zmultiples y) ∨
      ∀ i j, weight i = weight j := by
  classical
  by_cases hconstant : ∀ i j,
      weight (R i) - 2 * weight i =
        weight (R j) - 2 * weight j
  · exact Or.inr
      (weight_constant_of_transitionCoefficient_constant
        i₀ R weight hconstant)
  · push Not at hconstant
    obtain ⟨i, j, hij⟩ := hconstant
    let e : ℤ :=
      (weight (R i) - 2 * weight i) -
        (weight (R j) - 2 * weight j)
    have hi := twoRetainedNormalizedWeight_bounds (hweight i)
    have hRi := twoRetainedNormalizedWeight_bounds (hweight (R i))
    have hj := twoRetainedNormalizedWeight_bounds (hweight j)
    have hRj := twoRetainedNormalizedWeight_bounds (hweight (R j))
    refine Or.inl ⟨e, ?_, by omega, by omega, ?_⟩
    · dsimp only [e]
      exact sub_ne_zero.mpr hij
    · simpa only [e] using hpair i j

/-- Provenance-preserving punctured five-weight recurrence.  A nonzero kernel
coefficient is retained either as one available edge-coefficient difference
or as the exact two-step boundary defect. -/
theorem fiveWeightPuncturedPermutation_smallKernelMultipleWithSource_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H) :
    (∃ e : ℤ, e ≠ 0 ∧ -42 ≤ e ∧ e ≤ 42 ∧ e • delta ∈ H ∧
      ((∃ i : ι, i ≠ p ∧ R i ≠ p ∧
        e = (weight (R i) - 2 * weight i) -
          (weight (R i₀) - 2 * weight i₀)) ∨
       (e = (weight (R p) - 4 * weight (R.symm p)) -
          3 * (weight (R i₀) - 2 * weight i₀) ∧
        ∀ i, i ≠ p → R i ≠ p →
          weight (R i) - 2 * weight i =
            weight (R i₀) - 2 * weight i₀))) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  classical
  let q₀ : ℤ := weight (R i₀) - 2 * weight i₀
  have hi₀Bounds := twoRetainedNormalizedWeight_bounds (hweight i₀ hi₀)
  have hRi₀Bounds :=
    twoRetainedNormalizedWeight_bounds (hweight (R i₀) hRi₀)
  have hq₀Bounds : -8 ≤ q₀ ∧ q₀ ≤ 10 := by
    dsimp only [q₀]
    omega
  by_cases hall : ∀ i, i ≠ p → R i ≠ p →
      weight (R i) - 2 * weight i = q₀
  · let u : ι := R.symm p
    let v : ι := R p
    have hu : u ≠ p := by
      intro hup
      apply hp
      have happly : R (R.symm p) = p := R.apply_symm_apply p
      simpa only [u, hup] using happly
    have hv : v ≠ p := by simpa only [v] using hp
    let e : ℤ := weight v - 4 * weight u - 3 * q₀
    have huBounds := twoRetainedNormalizedWeight_bounds (hweight u hu)
    have hvBounds := twoRetainedNormalizedWeight_bounds (hweight v hv)
    have heBounds : -42 ≤ e ∧ e ≤ 42 := by
      dsimp only [e]
      omega
    have heMem : e • delta ∈ H := by
      have hthree := H.zsmul_mem (htransition i₀ hi₀ hRi₀) 3
      have hsub := H.sub_mem htwoStep hthree
      convert hsub using 1
      dsimp only [e, q₀, u, v]
      module
    by_cases heZero : e = 0
    · have hboundary : weight v = 4 * weight u + 3 * q₀ := by
        dsimp only [e] at heZero
        omega
      let extendedWeight : ι → ℤ := fun i ↦
        if i = p then 2 * weight u + q₀ else weight i
      have hcoefficient : ∀ i,
          extendedWeight (R i) - 2 * extendedWeight i = q₀ := by
        intro i
        by_cases hip : i = p
        · subst i
          simp only [extendedWeight, if_pos]
          rw [if_neg hv]
          simpa only [v] using (show
            weight v - 2 * (2 * weight u + q₀) = q₀ by omega)
        · by_cases hRip : R i = p
          · have hiu : i = u := by
              apply R.injective
              rw [hRip]
              simp only [u, R.apply_symm_apply]
            subst i
            simp only [extendedWeight, hu, if_false, u,
              R.apply_symm_apply, if_pos]
            omega
          · simp only [extendedWeight, hip, hRip, if_false]
            exact hall i hip hRip
      have hconstant : ∀ i j,
          extendedWeight (R i) - 2 * extendedWeight i =
            extendedWeight (R j) - 2 * extendedWeight j := by
        intro i j
        rw [hcoefficient i, hcoefficient j]
      have hweightsConstant :=
        weight_constant_of_transitionCoefficient_constant
          i₀ R extendedWeight hconstant
      right
      intro i hi j hj
      have hij := hweightsConstant i j
      simpa only [extendedWeight, hi, hj, if_false] using hij
    · exact Or.inl ⟨e, heZero, heBounds.1, heBounds.2, heMem,
        Or.inr ⟨by simp only [e, q₀, u, v], by
          intro i hi hRi
          simpa only [q₀] using hall i hi hRi⟩⟩
  · push Not at hall
    obtain ⟨i, hi, hRi, hne⟩ := hall
    let e : ℤ := (weight (R i) - 2 * weight i) - q₀
    have hiBounds := twoRetainedNormalizedWeight_bounds (hweight i hi)
    have hRiBounds :=
      twoRetainedNormalizedWeight_bounds (hweight (R i) hRi)
    have heBounds : -18 ≤ e ∧ e ≤ 18 := by
      dsimp only [e, q₀]
      omega
    have heMem : e • delta ∈ H := by
      have hiMem := htransition i hi hRi
      have hi₀Mem := htransition i₀ hi₀ hRi₀
      have hsub := H.sub_mem hiMem hi₀Mem
      convert hsub using 1
      dsimp only [e, q₀]
      module
    exact Or.inl ⟨e, by
      dsimp only [e]
      exact sub_ne_zero.mpr hne, by omega, by omega, heMem,
        Or.inl ⟨i, hi, hRi, by simp only [e, q₀]⟩⟩

/-- Compatibility projection of the provenance-preserving punctured-cycle
split. -/
theorem fiveWeightPuncturedPermutation_smallKernelMultiple_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H) :
    (∃ e : ℤ, e ≠ 0 ∧ -42 ≤ e ∧ e ≤ 42 ∧ e • delta ∈ H) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases fiveWeightPuncturedPermutation_smallKernelMultipleWithSource_or_weight_constant
      R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep with
    ⟨e, he, helow, hehigh, heMem, _hsource⟩ | hconstant
  · exact Or.inl ⟨e, he, helow, hehigh, heMem⟩
  · exact Or.inr hconstant

/-- If every surviving bounded kernel coefficient has absolute value `32`,
the internal-edge source is impossible and the punctured recurrence has only
the four exact boundary configurations classified above.  In the boundary
arm, every available edge retains the same transition coefficient. -/
theorem fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32) :
    (((weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
        weight i₀ = 2 ∧ weight (R i₀) = -2) ∨
     (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
        weight i₀ = 2 ∧ weight (R i₀) = -4) ∨
     (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
        weight i₀ = -4 ∧ weight (R i₀) = 2) ∨
     (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
        weight i₀ = -4 ∧ weight (R i₀) = 0)) ∧
      ∀ i, i ≠ p → R i ≠ p →
        weight (R i) - 2 * weight i =
          weight (R i₀) - 2 * weight i₀) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases fiveWeightPuncturedPermutation_smallKernelMultipleWithSource_or_weight_constant
      R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep with
    ⟨e, he, helow, hehigh, heMem, hsource⟩ | hconstant
  · have he32 := hkernel32 e he helow hehigh heMem
    rcases hsource with ⟨i, hi, hRi, heq⟩ | ⟨heq, hall⟩
    · have hiBounds := twoRetainedNormalizedWeight_bounds (hweight i hi)
      have hRiBounds :=
        twoRetainedNormalizedWeight_bounds (hweight (R i) hRi)
      have hi₀Bounds := twoRetainedNormalizedWeight_bounds (hweight i₀ hi₀)
      have hRi₀Bounds :=
        twoRetainedNormalizedWeight_bounds (hweight (R i₀) hRi₀)
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · left
      rw [heq] at he32
      exact ⟨fiveWeight_boundaryCoefficient_natAbs_eq_thirtyTwo
          (weight (R.symm p)) (weight (R p)) (weight i₀) (weight (R i₀))
            (hweight (R.symm p) (by
              intro hsymm
              apply hp
              have := R.apply_symm_apply p
              simpa only [hsymm] using this))
            (hweight (R p) (by simpa only using hp))
            (hweight i₀ hi₀) (hweight (R i₀) hRi₀) he32,
        hall⟩
  · exact Or.inr hconstant

/-- Compatibility projection of the transition-retaining top-boundary
classification. -/
theorem fiveWeightPuncturedPermutation_thirtyTwo_boundaryPattern_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32) :
    ((weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
        weight i₀ = 2 ∧ weight (R i₀) = -2) ∨
     (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
        weight i₀ = 2 ∧ weight (R i₀) = -4) ∨
     (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
        weight i₀ = -4 ∧ weight (R i₀) = 2) ∨
     (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
        weight i₀ = -4 ∧ weight (R i₀) = 0)) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases
      fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
        R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
          hkernel32 with
    ⟨hpattern, _hall⟩ | hconstant
  · exact Or.inl hpattern
  · exact Or.inr hconstant

/-- Pure five-weight arithmetic behind the top-boundary cycle collapse.  If
one of the four boundary patterns has a common available-edge transition
coefficient, no two available edges can be consecutive. -/
theorem fiveWeight_boundaryPatternWithTransition_noTwoConsecutiveAvailableEdges
    {ι : Type*} (R : Equiv.Perm ι) (p i₀ : ι)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (hpattern :
      (weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -2) ∨
       (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -4) ∨
       (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 2) ∨
       (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 0))
    (hall : ∀ i, i ≠ p → R i ≠ p →
      weight (R i) - 2 * weight i =
        weight (R i₀) - 2 * weight i₀) :
    ∀ i, i ≠ p → R i ≠ p → R (R i) ≠ p → False := by
  intro i hi hRi hRRi
  have hiBounds := twoRetainedNormalizedWeight_bounds (hweight i hi)
  have hRiBounds :=
    twoRetainedNormalizedWeight_bounds (hweight (R i) hRi)
  have hRRiBounds :=
    twoRetainedNormalizedWeight_bounds (hweight (R (R i)) hRRi)
  have hfirst := hall i hi hRi
  have hsecond := hall (R i) hRi hRRi
  rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
    rcases hpattern with ⟨_hu, _hv, hi₀Value, hRi₀Value⟩ <;>
    rw [hi₀Value, hRi₀Value] at hfirst hsecond <;>
    omega

/-- Cycle-return form of the four-pattern transition obstruction. -/
theorem fiveWeight_boundaryPatternWithTransition_shortReturn
    {ι : Type*} (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (hpattern :
      (weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -2) ∨
       (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -4) ∨
       (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 2) ∨
       (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 0))
    (hall : ∀ i, i ≠ p → R i ≠ p →
      weight (R i) - 2 * weight i =
        weight (R i₀) - 2 * weight i₀) :
    R (R p) = p ∨ R (R (R p)) = p := by
  have hnoTwo :=
    fiveWeight_boundaryPatternWithTransition_noTwoConsecutiveAvailableEdges
      R p i₀ weight hweight hpattern hall
  by_cases htwo : R (R p) = p
  · exact Or.inl htwo
  · exact Or.inr (by
      by_contra hthree
      exact hnoTwo (R p) hp htwo hthree)

/-- A two-step return identifies the predecessor and successor of the
unavailable vertex, whereas each top-boundary pattern assigns those two
positions different weights. -/
theorem fiveWeight_boundaryPattern_false_of_returnTwo
    {ι : Type*} (R : Equiv.Perm ι) (p i₀ : ι)
    (weight : ι → ℤ)
    (hpattern :
      (weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -2) ∨
       (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
          weight i₀ = 2 ∧ weight (R i₀) = -4) ∨
       (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 2) ∨
       (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
          weight i₀ = -4 ∧ weight (R i₀) = 0))
    (hreturn : R (R p) = p) : False := by
  have hsame : R.symm p = R p := by
    apply R.injective
    rw [R.apply_symm_apply, hreturn]
  rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
    rcases hpattern with ⟨hu, hv, _hi, _hRi⟩ <;>
    rw [hsame] at hu <;>
    omega

/-- If the successor itself is chosen as the available source, every one of
the four top-boundary patterns assigns it two different weights. -/
theorem fiveWeight_boundaryPattern_false_of_successorSource
    {ι : Type*} (R : Equiv.Perm ι) (p : ι)
    (weight : ι → ℤ)
    (hpattern :
      (weight (R.symm p) = -4 ∧ weight (R p) = -2 ∧
          weight (R p) = 2 ∧ weight (R (R p)) = -2) ∨
       (weight (R.symm p) = -2 ∧ weight (R p) = 0 ∧
          weight (R p) = 2 ∧ weight (R (R p)) = -4) ∨
       (weight (R.symm p) = 0 ∧ weight (R p) = -2 ∧
          weight (R p) = -4 ∧ weight (R (R p)) = 2) ∨
       (weight (R.symm p) = 2 ∧ weight (R p) = 0 ∧
          weight (R p) = -4 ∧ weight (R (R p)) = 0)) : False := by
  rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
    rcases hpattern with ⟨_hu, hv, hi, _hRi⟩ <;>
    omega

/-- The apparent four-pattern arm of the top-boundary classification is
globally inconsistent.  It first forces a return after two or three steps.
The two-step return identifies predecessor and successor.  In the three-step
case, rerunning the same lossless classification with `R p` as source either
assigns two values to `R p`, or makes all available weights constant, which
again contradicts the original predecessor/successor values. -/
theorem fiveWeightPuncturedPermutation_thirtyTwo_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32) :
    ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases
      fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
        R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
          hkernel32 with
    ⟨hpattern, hall⟩ | hconstant
  · have hshort := fiveWeight_boundaryPatternWithTransition_shortReturn
      R p i₀ hp weight hweight hpattern hall
    rcases hshort with hreturnTwo | hreturnThree
    · exact (fiveWeight_boundaryPattern_false_of_returnTwo
        R p i₀ weight hpattern hreturnTwo).elim
    · have hreturnTwoNe : R (R p) ≠ p := by
        intro hreturnTwo
        rw [hreturnTwo] at hreturnThree
        exact hp hreturnThree
      rcases
          fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
            R p (R p) hp hp hreturnTwoNe weight hweight delta C H
              htransition htwoStep hkernel32 with
        ⟨hpattern', _hall'⟩ | hconstant'
      · exact (fiveWeight_boundaryPattern_false_of_successorSource
          R p weight hpattern').elim
      · have hsymmNe : R.symm p ≠ p := by
          intro hsymm
          apply hp
          have happly := R.apply_symm_apply p
          simpa only [hsymm] using happly
        have heq := hconstant' (R.symm p) hsymmNe (R p) hp
        rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
          rcases hpattern with ⟨hu, hv, _hi, _hRi⟩ <;>
          omega
  · exact hconstant

/-- If one full doubling cycle spans `Z*y`, a two- or three-step return forces
the order of `y` to divide the corresponding Mersenne number `3` or `7`.
This is independent of the five-weight construction. -/
theorem addOrderOf_dvd_three_or_seven_of_isCycle_doubling_shortReturn
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (disp : ι → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (p : ι) (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y)
    (hshort : R (R p) = p ∨ R (R (R p)) = p) :
    addOrderOf y ∣ 3 ∨ addOrderOf y ∣ 7 := by
  have hspanLe : AddSubgroup.zmultiples y ≤
      AddSubgroup.zmultiples (disp p) := by
    rw [← hspan]
    apply (AddSubgroup.closure_le _).mpr
    rintro v ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := sameCycle_doubling_eq_pow_two_nsmul
      R disp hdouble (hcycle.sameCycle (hRne p) (hRne i))
    rw [hk]
    exact (AddSubgroup.zmultiples (disp p)).nsmul_mem
      (AddSubgroup.mem_zmultiples (disp p)) (2 ^ k)
  have hyMem : y ∈ AddSubgroup.zmultiples (disp p) :=
    hspanLe (AddSubgroup.mem_zmultiples y)
  rcases hshort with htwo | hthree
  · left
    have hfirst := hdouble p
    have hsecond := hdouble (R p)
    rw [htwo, hfirst] at hsecond
    have hpTorsion : 3 • disp p = 0 := by
      calc
        3 • disp p = 2 • (2 • disp p) - disp p := by module
        _ = disp p - disp p := by rw [← hsecond]
        _ = 0 := sub_self _
    have hZle : AddSubgroup.zmultiples (disp p) ≤
        (nsmulAddMonoidHom 3).ker := by
      rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      exact hpTorsion
    have hyTorsion := hZle hyMem
    rw [AddMonoidHom.mem_ker] at hyTorsion
    exact addOrderOf_dvd_of_nsmul_eq_zero hyTorsion
  · right
    have hfirst := hdouble p
    have hsecond := hdouble (R p)
    have hthird := hdouble (R (R p))
    rw [hthree, hsecond, hfirst] at hthird
    have hpTorsion : 7 • disp p = 0 := by
      calc
        7 • disp p = 2 • (2 • (2 • disp p)) - disp p := by module
        _ = disp p - disp p := by rw [← hthird]
        _ = 0 := sub_self _
    have hZle : AddSubgroup.zmultiples (disp p) ≤
        (nsmulAddMonoidHom 7).ker := by
      rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      exact hpTorsion
    have hyTorsion := hZle hyMem
    rw [AddMonoidHom.mem_ker] at hyTorsion
    exact addOrderOf_dvd_of_nsmul_eq_zero hyTorsion

/-- The four top-boundary configurations cannot support two consecutive
available edges.  Their common transition coefficients are respectively
`-6`, `-8`, `10`, and `8`; iterating any of these affine recurrences twice
leaves the five-weight interval. -/
theorem fiveWeightPuncturedPermutation_thirtyTwo_noTwoConsecutiveAvailableEdges_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32) :
    (∀ i, i ≠ p → R i ≠ p → R (R i) ≠ p → False) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases
      fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
        R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
          hkernel32 with
    ⟨hpattern, hall⟩ | hconstant
  · exact Or.inl
      (fiveWeight_boundaryPatternWithTransition_noTwoConsecutiveAvailableEdges
        R p i₀ weight hweight hpattern hall)
  · exact Or.inr hconstant

/-- A top-boundary nonconstant punctured permutation returns from `p` after
two or three steps.  This is the cycle-length form of the absence of two
consecutive available edges. -/
theorem fiveWeightPuncturedPermutation_thirtyTwo_shortReturn_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32) :
    (R (R p) = p ∨ R (R (R p)) = p) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases
      fiveWeightPuncturedPermutation_thirtyTwo_noTwoConsecutiveAvailableEdges_or_weight_constant
        R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
          hkernel32 with
    hnoTwo | hconstant
  · exact Or.inl (by
      by_cases htwo : R (R p) = p
      · exact Or.inl htwo
      · exact Or.inr (by
          by_contra hthree
          exact hnoTwo (R p) hp htwo hthree))
  · exact Or.inr hconstant

/-- If every leaf of a saturated doubling cycle is deleted by the minimal
transversal, the five-weight transition invariant becomes global on that
cycle.  Either the retained difference has a nonzero kernel multiple with
coefficient at most 18, or every deleted cycle leaf has the same weight. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fullDeletedCycle_split
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : G)
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((∃ e : ℤ, e ≠ 0 ∧ -18 ≤ e ∧ e ≤ 18 ∧
          e • (g x - g z) ∈ AddSubgroup.zmultiples y) ∨
        ∀ i j,
          weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩) := by
  classical
  rcases hrows.cycleTransition_mem g y B leaf R a hdouble with
    ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, _htransition, hpair⟩
  let cycleWeight : Fin d → ℤ := fun i ↦ weight ⟨leaf i, hleafB i⟩
  let i₀ : Fin d := ⟨0, hd⟩
  have hcycleWeight : ∀ i,
      cycleWeight i ∈ twoRetainedNormalizedWeightLevels := by
    intro i
    exact hweight ⟨leaf i, hleafB i⟩
  have hcyclePair : ∀ i j,
      ((cycleWeight (R i) - 2 * cycleWeight i) -
          (cycleWeight (R j) - 2 * cycleWeight j)) • (g x - g z) ∈
        AddSubgroup.zmultiples y := by
    intro i j
    simpa only [cycleWeight] using
      hpair i (hleafB i) (hleafB (R i))
        j (hleafB j) (hleafB (R j))
  have hsplit :=
    fiveWeightTransition_smallKernelMultiple_or_weight_constant
      i₀ R cycleWeight hcycleWeight (g x - g z) y hcyclePair
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
  simpa only [cycleWeight] using hsplit

/-- A constant five-weight transition has only one exceptional value after
the retained cycle vertex is identified.  If `x` is in the cyclic-kernel
coset of the cycle center, the transition gives a nonzero multiple of
`x-z` of size at most four unless `w=-2`; with `z` retained, the sole
exception is `w=0`. -/
theorem constantFiveWeight_transition_terminal
    (x z a : G) (H : AddSubgroup G) (w : ℤ)
    (hw : w ∈ twoRetainedNormalizedWeightLevels)
    (htransition :
      (-w) • (x - z) + (2 : ℤ) • (z - a) ∈ H) :
    ((x - a ∈ H) →
      (∃ e : ℤ, e ≠ 0 ∧ -4 ≤ e ∧ e ≤ 4 ∧ e • (x - z) ∈ H) ∨
        w = -2) ∧
    ((z - a ∈ H) →
      (∃ e : ℤ, e ≠ 0 ∧ -4 ≤ e ∧ e ≤ 4 ∧ e • (x - z) ∈ H) ∨
        w = 0) := by
  have hwBounds := twoRetainedNormalizedWeight_bounds hw
  constructor
  · intro hx
    let e : ℤ := -(w + 2)
    have heBounds : -4 ≤ e ∧ e ≤ 4 := by
      dsimp only [e]
      omega
    have heMem : e • (x - z) ∈ H := by
      have hsub := H.sub_mem htransition (H.zsmul_mem hx 2)
      convert hsub using 1
      dsimp only [e]
      module
    by_cases heZero : e = 0
    · right
      dsimp only [e] at heZero
      omega
    · exact Or.inl ⟨e, heZero, heBounds.1, heBounds.2, heMem⟩
  · intro hz
    let e : ℤ := -w
    have heBounds : -4 ≤ e ∧ e ≤ 4 := by
      dsimp only [e]
      omega
    have heMem : e • (x - z) ∈ H := by
      have hsub := H.sub_mem htransition (H.zsmul_mem hz 2)
      convert hsub using 1
      dsimp only [e]
      module
    by_cases heZero : e = 0
    · right
      dsimp only [e] at heZero
      omega
    · exact Or.inl ⟨e, heZero, heBounds.1, heBounds.2, heMem⟩

/-- Lossless recurrence data for a cycle with one retained leaf.  Besides the
row weights and available-edge transitions, this endpoint exposes a total
cycle weight and the exact fourfold relation across the unavailable leaf. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_recurrence
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) (a : G)
    (p : Fin d) (hp : R p ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ, ∃ cycleWeight : Fin d → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
        (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
            (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y) ∧
      (∀ i (hi : leaf i ∈ B),
        cycleWeight i = weight ⟨leaf i, hi⟩) ∧
      (∀ i, i ≠ p →
        cycleWeight i ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i, i ≠ p → R i ≠ p →
        (cycleWeight (R i) - 2 * cycleWeight i) • (g x - g z) +
            (2 : ℤ) • (g z - a) ∈ AddSubgroup.zmultiples y) ∧
      (cycleWeight (R p) - 4 * cycleWeight (R.symm p)) •
            (g x - g z) +
          (3 : ℤ) • ((2 : ℤ) • (g z - a)) ∈
        AddSubgroup.zmultiples y := by
  classical
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  let target : ↥B → G := fun b ↦
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
      (scalar b • y)
  have htargetMem : ∀ b, target b ∈ AddSubgroup.zmultiples y := by
    intro b
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
  have htransition : ∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
      (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
          (g x - g z) + (2 : ℤ) • (g z - a) ∈
        AddSubgroup.zmultiples y := by
    intro i hi hRi
    let b : ↥B := ⟨leaf i, hi⟩
    let c : ↥B := ⟨leaf (R i), hRi⟩
    exact fiveWeightAffine_pairTransition_mem_zmultiples
      g y a x z (b : Fin n) (c : Fin n) (weight b) (weight c)
        (target b) (target c) (hweightData b).2.2 (hweightData c).2.2
          (htargetMem b) (htargetMem c) (hdouble i)
  let u : Fin d := R.symm p
  let v : Fin d := R p
  have hu : u ≠ p := by
    intro hup
    apply hp
    have happly : R (R.symm p) = p := R.apply_symm_apply p
    simpa only [u, hup] using happly
  have hv : v ≠ p := by simpa only [v] using hp
  have huB : leaf u ∈ B := (hleafB u).2 hu
  have hvB : leaf v ∈ B := (hleafB v).2 hv
  have hfour : g (leaf v) - a = (4 : ℤ) • (g (leaf u) - a) := by
    have huStep : g (leaf p) - a =
        (2 : ℤ) • (g (leaf u) - a) := by
      have hstep := hdouble u
      simpa only [u, R.apply_symm_apply] using hstep
    calc
      g (leaf v) - a = (2 : ℤ) • (g (leaf p) - a) := by
        simpa only [v] using hdouble p
      _ = (2 : ℤ) • ((2 : ℤ) • (g (leaf u) - a)) := by rw [huStep]
      _ = (4 : ℤ) • (g (leaf u) - a) := by module
  have htwoStep :
      (weight ⟨leaf v, hvB⟩ - 4 * weight ⟨leaf u, huB⟩) •
          (g x - g z) + (6 : ℤ) • (g z - a) ∈
        AddSubgroup.zmultiples y := by
    let bu : ↥B := ⟨leaf u, huB⟩
    let bv : ↥B := ⟨leaf v, hvB⟩
    exact fiveWeightAffine_pairFourTransition_mem_zmultiples
      g y a x z (bu : Fin n) (bv : Fin n) (weight bu) (weight bv)
        (target bu) (target bv) (hweightData bu).2.2
          (hweightData bv).2.2 (htargetMem bu) (htargetMem bv) hfour
  let cycleWeight : Fin d → ℤ := fun i ↦
    if hi : leaf i ∈ B then weight ⟨leaf i, hi⟩ else 0
  have hcycleWeight : ∀ i, i ≠ p →
      cycleWeight i ∈ twoRetainedNormalizedWeightLevels := by
    intro i hi
    have hiB : leaf i ∈ B := (hleafB i).2 hi
    simp only [cycleWeight, dif_pos hiB]
    exact hweightData ⟨leaf i, hiB⟩ |>.1
  have hcycleTransition : ∀ i, i ≠ p → R i ≠ p →
      (cycleWeight (R i) - 2 * cycleWeight i) • (g x - g z) +
          (2 : ℤ) • (g z - a) ∈ AddSubgroup.zmultiples y := by
    intro i hi hRi
    have hiB : leaf i ∈ B := (hleafB i).2 hi
    have hRiB : leaf (R i) ∈ B := (hleafB (R i)).2 hRi
    simpa only [cycleWeight, dif_pos hiB, dif_pos hRiB] using
      htransition i hiB hRiB
  have hcycleTwoStep :
      (cycleWeight (R p) - 4 * cycleWeight (R.symm p)) •
          (g x - g z) +
        (3 : ℤ) • ((2 : ℤ) • (g z - a)) ∈
          AddSubgroup.zmultiples y := by
    have hvValue : cycleWeight (R p) = weight ⟨leaf v, hvB⟩ := by
      simp only [cycleWeight, v, dif_pos hvB]
    have huValue : cycleWeight (R.symm p) = weight ⟨leaf u, huB⟩ := by
      simp only [cycleWeight, u, dif_pos huB]
    rw [hvValue, huValue]
    convert htwoStep using 1
    module
  refine ⟨x, z, weight, cycleWeight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, htransition, ?_, hcycleWeight,
      hcycleTransition, hcycleTwoStep⟩
  intro i hiB
  simp only [cycleWeight, dif_pos hiB]

/-- Exact one-retained-leaf extension of `fullDeletedCycle_split`.  The two
cycle edges incident to the retained leaf are replaced by their fourfold
two-step relation, so the only new possible kernel coefficient is bounded by
42 rather than 18. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_split
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) (a : G)
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
        (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
            (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y) ∧
      ((∃ e : ℤ, e ≠ 0 ∧ -42 ≤ e ∧ e ≤ 42 ∧
          e • (g x - g z) ∈ AddSubgroup.zmultiples y) ∨
        ∀ i (hi : leaf i ∈ B) j (hj : leaf j ∈ B),
          weight ⟨leaf i, hi⟩ = weight ⟨leaf j, hj⟩) := by
  obtain ⟨x, z, weight, cycleWeight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hcycleValue, hcycleWeight,
      hcycleTransition, hcycleTwoStep⟩ :=
    hrows.oneRetainedCycle_recurrence g y B leaf R a p hp hleafB hdouble
  have hsplit :=
    fiveWeightPuncturedPermutation_smallKernelMultiple_or_weight_constant
      R p i₀ hp hi₀ hRi₀ cycleWeight hcycleWeight
        (g x - g z) ((2 : ℤ) • (g z - a))
          (AddSubgroup.zmultiples y) hcycleTransition hcycleTwoStep
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    hweight, htransition, ?_⟩
  rcases hsplit with hsmall | hconstant
  · exact Or.inl hsmall
  · right
    intro i hiB j hjB
    have hi : i ≠ p := (hleafB i).1 hiB
    have hj : j ≠ p := (hleafB j).1 hjB
    calc
      weight ⟨leaf i, hiB⟩ = cycleWeight i := (hcycleValue i hiB).symm
      _ = cycleWeight j := hconstant i hi j hj
      _ = weight ⟨leaf j, hjB⟩ := hcycleValue j hjB

/-- Terminal form of the one-retained-leaf five-weight reduction when the
retained leaf lies in the same cyclic-kernel coset of the cycle center as all
cycle leaves.  The constant arm collapses to the bounded-multiple arm except
for the exact pure-pair weights: `-2` when the retained leaf is `x`, or `0`
in the reversed orientation where it is `z`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_terminal
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) (a : G)
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((∃ e : ℤ, e ≠ 0 ∧ -42 ≤ e ∧ e ≤ 42 ∧
          e • (g x - g z) ∈ AddSubgroup.zmultiples y) ∨
        (leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  classical
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hsplit⟩ :=
    hrows.oneRetainedCycle_split g y B leaf R a p i₀ hp hi₀ hRi₀
      hleafB hdouble
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
  rcases hsplit with hsmall | hconstant
  · exact Or.inl hsmall
  · have hiB : leaf i₀ ∈ B := (hleafB i₀).2 hi₀
    have hRiB : leaf (R i₀) ∈ B := (hleafB (R i₀)).2 hRi₀
    let w : ℤ := weight ⟨leaf i₀, hiB⟩
    have hw : w ∈ twoRetainedNormalizedWeightLevels :=
      hweight ⟨leaf i₀, hiB⟩
    have hwEdge : weight ⟨leaf (R i₀), hRiB⟩ = w := by
      simpa only [w] using hconstant (R i₀) hRiB i₀ hiB
    have htransitionSimple :
        (-w) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y := by
      have ht := htransition i₀ hiB hRiB
      rw [hwEdge] at ht
      convert ht using 1
      dsimp only [w]
      module
    have hterminal := constantFiveWeight_transition_terminal
      (g x) (g z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
    have hpNotB : leaf p ∉ B := by
      intro hpB
      exact (hleafB p).1 hpB rfl
    have hpPair : leaf p = x ∨ leaf p = z := by
      have hpComplement : leaf p ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotB⟩
      rw [hcomplement] at hpComplement
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpComplement
    rcases hpPair with hpX | hpZ
    · have hxMem : g x - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpX] using hretainedMem
      rcases hterminal.1 hxMem with hsmall | hwMinusTwo
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        exact Or.inl ⟨e, he, by omega, by omega, heMem⟩
      · exact Or.inr (Or.inl ⟨hpX, by
          intro i hi
          calc
            weight ⟨leaf i, hi⟩ = w :=
              hconstant i hi i₀ hiB
            _ = -2 := hwMinusTwo⟩)
    · have hzMem : g z - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpZ] using hretainedMem
      rcases hterminal.2 hzMem with hsmall | hwZero
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        exact Or.inl ⟨e, he, by omega, by omega, heMem⟩
      · exact Or.inr (Or.inr ⟨hpZ, by
          intro i hi
          calc
            weight ⟨leaf i, hi⟩ = w :=
              hconstant i hi i₀ hiB
            _ = 0 := hwZero⟩)

/-- In a finite group with a unique nonzero involution, the preimage of an
additive subgroup under doubling has at most twice the subgroup's order. -/
theorem card_doublePreimage_le_two_mul
    [Fintype G] {h : G}
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (K : AddSubgroup G) :
    Nat.card (K.comap (nsmulAddMonoidHom 2)) ≤ 2 * Nat.card K := by
  classical
  let L : AddSubgroup G := K.comap (nsmulAddMonoidHom 2)
  let doubleToK : L →+ K := AddMonoidHom.codRestrict
    ((nsmulAddMonoidHom 2).comp L.subtype) K (fun x ↦ x.property)
  let code : ↥doubleToK.ker → Bool := fun u ↦ (u.1.1 : G) = 0
  have hcodeInjective : Function.Injective code := by
    intro u v huv
    have huTwo : (u.1.1 : G) + u.1.1 = 0 := by
      have hu := congrArg Subtype.val u.property
      change (2 : ℕ) • (u.1.1 : G) = 0 at hu
      simpa only [two_nsmul] using hu
    have hvTwo : (v.1.1 : G) + v.1.1 = 0 := by
      have hv := congrArg Subtype.val v.property
      change (2 : ℕ) • (v.1.1 : G) = 0 at hv
      simpa only [two_nsmul] using hv
    rcases hunique _ huTwo with huZero | huHalf
    · rcases hunique _ hvTwo with hvZero | hvHalf
      · apply Subtype.ext
        apply Subtype.ext
        exact huZero.trans hvZero.symm
      · have hfalse : true = false := by
          simpa only [code, huZero, eq_self, decide_true, hvHalf,
            hne, decide_false] using huv
        exact Bool.noConfusion hfalse
    · rcases hunique _ hvTwo with hvZero | hvHalf
      · have hfalse : false = true := by
          simpa only [code, huHalf, hne, decide_false, hvZero,
            eq_self, decide_true] using huv
        exact Bool.noConfusion hfalse
      · apply Subtype.ext
        apply Subtype.ext
        exact huHalf.trans hvHalf.symm
  have hkerCard : Nat.card doubleToK.ker ≤ 2 := by
    have hcard := Fintype.card_le_of_injective code hcodeInjective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using hcard
  have hrangeCard : Nat.card doubleToK.range ≤ Nat.card K := by
    have hcard := Fintype.card_le_of_injective
      (fun u : ↥doubleToK.range ↦ (u : K))
      (fun _ _ huv ↦ Subtype.ext huv)
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hcardL : Nat.card L =
      Nat.card doubleToK.ker * Nat.card doubleToK.range := by
    calc
      Nat.card L = Nat.card doubleToK.ker * doubleToK.ker.index :=
        doubleToK.ker.card_mul_index.symm
      _ = Nat.card doubleToK.ker * Nat.card doubleToK.range := by
        rw [AddSubgroup.index_ker doubleToK]
  change Nat.card L ≤ 2 * Nat.card K
  rw [hcardL]
  exact Nat.mul_le_mul hkerCard hrangeCard

/-- Adjoining one element whose nonzero integer multiple already lies in a
finite subgroup enlarges that subgroup by at most the absolute value of the
coefficient. -/
theorem card_sup_zmultiples_le_natAbs_mul
    [Fintype G] (H : AddSubgroup G) (delta : G) (e : ℤ)
    (he : e ≠ 0) (heMem : e • delta ∈ H) :
    Nat.card ↥(H ⊔ AddSubgroup.zmultiples delta) ≤
      e.natAbs * Nat.card H := by
  classical
  let K : AddSubgroup G := H ⊔ AddSubgroup.zmultiples delta
  let pi : G →+ G ⧸ H := QuotientAddGroup.mk' H
  let f : K →+ G ⧸ H := pi.comp K.subtype
  let kernelToH : ↥f.ker → H := fun u ↦
    ⟨u.1.1, by
      apply (QuotientAddGroup.eq_zero_iff u.1.1).mp
      have hu : f u.1 = 0 := u.property
      change pi u.1.1 = 0 at hu
      exact hu⟩
  have hkernelInjective : Function.Injective kernelToH := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : H ↦ (q : G)) huv
  have hkernelCard : Nat.card f.ker ≤ Nat.card H := by
    have hcard := Fintype.card_le_of_injective kernelToH hkernelInjective
    simpa only [Nat.card_eq_fintype_card] using hcard
  have heQuotient : e • pi delta = 0 := by
    rw [← map_zsmul]
    exact QuotientAddGroup.eq_zero_iff (e • delta) |>.mpr heMem
  have hnatQuotient : e.natAbs • pi delta = 0 := by
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq e with hePos | heNeg
    · rw [hePos] at heQuotient
      exact heQuotient
    · rw [heNeg, neg_smul] at heQuotient
      exact neg_eq_zero.mp heQuotient
  have horderDvd : addOrderOf (pi delta) ∣ e.natAbs :=
    addOrderOf_dvd_of_nsmul_eq_zero hnatQuotient
  have horderLe : addOrderOf (pi delta) ≤ e.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
  have hrangeLe : f.range ≤ AddSubgroup.zmultiples (pi delta) := by
    rintro _ ⟨u, rfl⟩
    rcases AddSubgroup.mem_sup.mp u.property with
      ⟨v, hvH, w, hwDelta, hvw⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hwDelta with ⟨c, rfl⟩
    change pi (u : G) ∈ AddSubgroup.zmultiples (pi delta)
    rw [← hvw, map_add, map_zsmul]
    have hvZero : pi v = 0 := QuotientAddGroup.eq_zero_iff v |>.mpr hvH
    rw [hvZero, zero_add]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) c
  have hrangeCard : Nat.card f.range ≤ e.natAbs := by
    have hdvd := AddSubgroup.card_dvd_of_le hrangeLe
    have hpositive : 0 < Nat.card (AddSubgroup.zmultiples (pi delta)) :=
      Nat.card_pos
    have hle := Nat.le_of_dvd hpositive hdvd
    rw [Nat.card_zmultiples] at hle
    exact hle.trans horderLe
  have hcardK : Nat.card K = Nat.card f.ker * Nat.card f.range := by
    calc
      Nat.card K = Nat.card f.ker * f.ker.index :=
        f.ker.card_mul_index.symm
      _ = Nat.card f.ker * Nat.card f.range := by
        rw [AddSubgroup.index_ker f]
  change Nat.card K ≤ e.natAbs * Nat.card H
  rw [hcardK, mul_comm]
  exact Nat.mul_le_mul hrangeCard hkernelCard

/-- Exact cyclic replacement for a coarse factor-two cardinal estimate.  If
an integer `e` kills `delta` and doubling every element lands in the cyclic
subgroup generated by `delta`, then the whole cyclic group order divides
`2*|e|`. -/
theorem nat_card_dvd_two_mul_natAbs_of_cyclic_double_mem_zmultiples
    {Q : Type*} [AddCommGroup Q] [Finite Q] [IsAddCyclic Q]
    (delta : Q) (e : ℤ) (hezero : e • delta = 0)
    (hdouble : ∀ u : Q,
      (2 : ℕ) • u ∈ AddSubgroup.zmultiples delta) :
    Nat.card Q ∣ 2 * e.natAbs := by
  obtain ⟨a, ha⟩ :=
    (isAddCyclic_iff_exists_zmultiples_eq_top.mp
      (inferInstance : IsAddCyclic Q))
  obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp (hdouble a)
  have hc' : (2 : ℤ) • a = c • delta := by
    change ((2 : ℕ) : ℤ) • a = c • delta
    rw [natCast_zsmul]
    exact hc.symm
  have htwice : (e * 2) • a = 0 := by
    calc
      (e * 2) • a = e • ((2 : ℤ) • a) := by rw [mul_smul]
      _ = e • (c • delta) := by rw [hc']
      _ = c • (e • delta) := by module
      _ = 0 := by rw [hezero, smul_zero]
  have hnat : (e * 2).natAbs • a = 0 := by
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq (e * 2) with hpos | hneg
    · rw [hpos] at htwice
      exact htwice
    · rw [hneg, neg_smul] at htwice
      exact neg_eq_zero.mp htwice
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hnat
  rw [addOrderOf_eq_card_of_zmultiples_eq_top ha] at hdvd
  have htwo : Int.natAbs (2 : ℤ) = 2 := by norm_num
  rw [Int.natAbs_mul, htwo, Nat.mul_comm] at hdvd
  exact hdvd

/-- A bounded retained-difference relation realizes the exact-two private-row
tuple inside an actual subgroup of size at most
`2*|e|*addOrderOf y`.  Each normalized row puts twice its owner difference in
`zmultiples y ⊔ zmultiples (g x-g z)`; the bounded relation controls the latter
extension, and unique two-torsion controls the preimage under doubling. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_validTuple_boundedConfinementSubgroup
    [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (e : ℤ) (he : e ≠ 0) :
    (∃ x z : Fin n,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      e • (g x - g z) ∈ AddSubgroup.zmultiples y) →
    ∃ L : AddSubgroup G, ∃ gL : Fin n → L,
      ValidTuple gL ∧
        Nat.card L ≤ 2 * e.natAbs * addOrderOf y ∧
        ∃ delta : G,
          e • delta ∈ AddSubgroup.zmultiples y ∧
          L = ((AddSubgroup.zmultiples y ⊔
            AddSubgroup.zmultiples delta).comap (nsmulAddMonoidHom 2)) := by
  classical
  rintro ⟨x', z', hx'B, hz'B, hx'z', hcomplement', heMem'⟩
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  have hpairEq : ({x', z'} : Finset (Fin n)) = {x, z} := by
    rw [← hcomplement', ← hcomplement]
  have hx'Mem : x' ∈ ({x, z} : Finset (Fin n)) := by
    rw [← hpairEq]
    simp
  have hz'Mem : z' ∈ ({x, z} : Finset (Fin n)) := by
    rw [← hpairEq]
    simp
  have hdeltaRelation :
      e • (g x - g z) ∈ AddSubgroup.zmultiples y := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'Mem hz'Mem
    rcases hx'Mem with hxx | hxz' <;>
      rcases hz'Mem with hzx | hzz
    · exact (hx'z' (hxx.trans hzx.symm)).elim
    · simpa only [hxx, hzz] using heMem'
    · have hreverse : e • (g z - g x) ∈ AddSubgroup.zmultiples y := by
        simpa only [hxz', hzx] using heMem'
      have hneg := AddSubgroup.neg_mem _ hreverse
      convert hneg using 1
      module
    · exact (hx'z' (hxz'.trans hzz.symm)).elim
  let H : AddSubgroup G := AddSubgroup.zmultiples y
  let delta : G := g x - g z
  let K : AddSubgroup G := H ⊔ AddSubgroup.zmultiples delta
  let L : AddSubgroup G := K.comap (nsmulAddMonoidHom 2)
  have hcoordinate : ∀ i, g i - g z ∈ L := by
    intro i
    change (2 : ℕ) • (g i - g z) ∈ K
    by_cases hiB : i ∈ B
    · let b : ↥B := ⟨i, hiB⟩
      let target : G :=
        twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
          (scalar b • y)
      have htargetH : target ∈ H := by
        exact AddSubgroup.zsmul_mem _
          (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
      have htargetK : target ∈ K :=
        AddSubgroup.mem_sup_left htargetH
      have hweightDelta : weight b • delta ∈ K :=
        AddSubgroup.zsmul_mem _
          (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples delta)) _
      have hsub := K.sub_mem htargetK hweightDelta
      have hrow := (hweightData b).2.2
      convert hsub using 1
      dsimp only [target, delta, b]
      rw [hrow]
      module
    · have hiComplement : i ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩
      rw [hcomplement] at hiComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiComplement
      rcases hiComplement with hix | hiz
      · subst i
        exact K.nsmul_mem
          (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples delta)) 2
      · subst i
        simp
  let gL : Fin n → L := fun i ↦ ⟨g i - g z, hcoordinate i⟩
  have hgL : ValidTuple gL := by
    apply validTuple_of_comp L.subtype
    simpa only [gL, AddSubgroup.coe_subtype] using
      validTuple_sub_const g hg (g z)
  have hKcard : Nat.card K ≤ e.natAbs * addOrderOf y := by
    have hcard := card_sup_zmultiples_le_natAbs_mul H delta e he hdeltaRelation
    simpa only [K, H, delta, Nat.card_zmultiples] using hcard
  have hLcard : Nat.card L ≤ 2 * Nat.card K := by
    simpa only [L] using card_doublePreimage_le_two_mul hunique hne K
  refine ⟨L, gL, hgL, ?_, delta, hdeltaRelation, rfl⟩
  calc
    Nat.card L ≤ 2 * Nat.card K := hLcard
    _ ≤ 2 * (e.natAbs * addOrderOf y) := Nat.mul_le_mul_left 2 hKcard
    _ = 2 * e.natAbs * addOrderOf y := by simp only [Nat.mul_assoc]

/-- Cardinal shadow of the actual bounded-confinement subgroup: validity
inside that subgroup forces the usual finite-abelian lower bound. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.card_le_two_mul_natAbs_mul
    [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (e : ℤ) (he : e ≠ 0) :
    (∃ x z : Fin n,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      e • (g x - g z) ∈ AddSubgroup.zmultiples y) →
    2 ^ (n - 1) ≤ 2 * e.natAbs * addOrderOf y := by
  classical
  intro hrelation
  obtain ⟨L, gL, hgL, hLcard, _hstructure⟩ :=
    hrows.exists_validTuple_boundedConfinementSubgroup
      g hg hunique hne y B e he hrelation
  letI : Fintype L := Fintype.ofFinite L
  have hlower : 2 ^ (n - 1) ≤ Nat.card L := by
    have hcard := two_pow_pred_le_card_of_validTuple gL hgL
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact hlower.trans hLcard

/-- Exact structural cyclic form of bounded confinement.  Either the
confinement subgroup gives a valid tuple at a strictly smaller divisor, or
the quotient by `zmultiples y` has order dividing `2*|e|`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_quotientFactor_dvd
    {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {h : ZMod N}
    (hunique : ∀ u : ZMod N, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod N) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < N ∧ M ∣ N ∧ AdmitsValidTuple n M) ∨
      N / addOrderOf y ∣ 2 * e.natAbs := by
  classical
  obtain ⟨L, gL, hgL, _hLcard, delta, hdeltaMem, hLdef⟩ :=
    hrows.exists_validTuple_boundedConfinementSubgroup
      g hg hunique hne y B e he
        ⟨x, z, hxB, hzB, hxz, hcomplement, heMem⟩
  letI : Fintype L := Fintype.ofFinite L
  have hMpos : 0 < Nat.card L := Nat.card_pos
  have hMdiv : Nat.card L ∣ N := by
    have hdiv : Nat.card L ∣ Nat.card (ZMod N) :=
      AddSubgroup.card_addSubgroup_dvd_card L
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hdiv
  letI : IsAddCyclic L := AddSubgroup.isAddCyclic L
  let equiv : L ≃+ ZMod (Nat.card L) :=
    (zmodAddCyclicAddEquiv (G := L) inferInstance).symm
  have hAdmits : AdmitsValidTuple n (Nat.card L) := by
    refine ⟨fun i ↦ equiv (gL i), ?_⟩
    exact validTuple_comp hgL equiv.toAddMonoidHom equiv.injective
  by_cases hproper : Nat.card L < N
  · exact Or.inl ⟨Nat.card L, hMpos, hproper, hMdiv, hAdmits⟩
  · right
    have hLcardEq : Nat.card L = N := by
      apply Nat.le_antisymm
      · exact Nat.le_of_dvd (NeZero.pos N) hMdiv
      · exact Nat.le_of_not_gt hproper
    have hLtop : L = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      simpa only [Nat.card_zmod] using hLcardEq
    have hall : ∀ v : ZMod N,
        (2 : ℕ) • v ∈ AddSubgroup.zmultiples y ⊔
          AddSubgroup.zmultiples delta := by
      intro v
      have hv : v ∈ L := by rw [hLtop]; simp
      rw [hLdef] at hv
      exact hv
    let H : AddSubgroup (ZMod N) := AddSubgroup.zmultiples y
    let Q := ZMod N ⧸ H
    let pi : ZMod N →+ Q := QuotientAddGroup.mk' H
    letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
      (QuotientAddGroup.mk'_surjective H)
    have hezeroQ : e • pi delta = 0 := by
      rw [← map_zsmul]
      apply QuotientAddGroup.eq_zero_iff (e • delta) |>.mpr
      simpa only [H] using hdeltaMem
    have hdoubleQ : ∀ u : Q,
        (2 : ℕ) • u ∈ AddSubgroup.zmultiples (pi delta) := by
      intro u
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective H u
      rw [← map_nsmul]
      rcases AddSubgroup.mem_sup.mp (hall v) with
        ⟨a, ha, b, hb, hab⟩
      rcases AddSubgroup.mem_zmultiples_iff.mp hb with ⟨c, rfl⟩
      rw [← hab, map_add, map_zsmul]
      have haZero : pi a = 0 :=
        QuotientAddGroup.eq_zero_iff a |>.mpr (by simpa only [H] using ha)
      rw [haZero, zero_add]
      exact AddSubgroup.zsmul_mem _
        (AddSubgroup.mem_zmultiples (pi delta)) c
    have hQdiv : Nat.card Q ∣ 2 * e.natAbs :=
      nat_card_dvd_two_mul_natAbs_of_cyclic_double_mem_zmultiples
        (pi delta) e hezeroQ hdoubleQ
    have hmul : Nat.card Q * addOrderOf y = N := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hQcard : Nat.card Q = N / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    rwa [hQcard] at hQdiv

/-- Structural cyclic form of bounded confinement.  Either the realized
confinement subgroup gives a valid tuple at a strictly smaller divisor of the
ambient modulus, or it is already large enough that the quotient by
`zmultiples y` has order at most `2*|e|`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_quotientFactor_le
    {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {h : ZMod N}
    (hunique : ∀ u : ZMod N, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod N) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < N ∧ M ∣ N ∧ AdmitsValidTuple n M) ∨
      N / addOrderOf y ≤ 2 * e.natAbs := by
  classical
  obtain ⟨L, gL, hgL, hLcard, _hstructure⟩ :=
    hrows.exists_validTuple_boundedConfinementSubgroup
      g hg hunique hne y B e he
        ⟨x, z, hxB, hzB, hxz, hcomplement, heMem⟩
  letI : Fintype L := Fintype.ofFinite L
  have hMpos : 0 < Nat.card L := Nat.card_pos
  have hMdiv : Nat.card L ∣ N := by
    have hdiv : Nat.card L ∣ Nat.card (ZMod N) :=
      AddSubgroup.card_addSubgroup_dvd_card L
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hdiv
  letI : IsAddCyclic L := AddSubgroup.isAddCyclic L
  let equiv : L ≃+ ZMod (Nat.card L) :=
    (zmodAddCyclicAddEquiv (G := L) inferInstance).symm
  have hAdmits : AdmitsValidTuple n (Nat.card L) := by
    refine ⟨fun i ↦ equiv (gL i), ?_⟩
    exact validTuple_comp hgL equiv.toAddMonoidHom equiv.injective
  by_cases hproper : Nat.card L < N
  · exact Or.inl ⟨Nat.card L, hMpos, hproper, hMdiv, hAdmits⟩
  · right
    have hNbound : N ≤ 2 * e.natAbs * addOrderOf y :=
      (Nat.le_of_not_gt hproper).trans hLcard
    apply Nat.div_le_of_le_mul
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hNbound

/-- Exact odd-primary specialization: absent a smaller valid cyclic modulus,
the quotient modulus used by the charge/descent interfaces divides
`2*|e|`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_dvd
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      2 ^ t * (q / addOrderOf y) ∣ 2 * e.natAbs := by
  rcases hrows.exists_smallerValidCyclicModulus_or_quotientFactor_dvd
      g hg hunique hne y B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    rw [← Nat.mul_div_assoc (2 ^ t) hyq]
    exact hfactor

/-- Minimal-counterexample form of exact divisibility: unless bounded
confinement already gives a smaller valid cyclic modulus, the ambient
two-primary factor satisfies `2^t ≤ 2*|e|`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_two_pow_le_two_mul_natAbs
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      2 ^ t ≤ 2 * e.natAbs := by
  rcases hrows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_dvd
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq
      apply NeZero.ne (2 ^ t * q)
      simp only [hq, mul_zero]
    have hquotPos : 0 < q / addOrderOf y := by
      apply Nat.div_pos (Nat.le_of_dvd hqpos hyq)
      exact addOrderOf_pos y
    have hfactorLe :
        2 ^ t * (q / addOrderOf y) ≤ 2 * e.natAbs :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) (Int.natAbs_pos.mpr he)) hfactor
    exact (Nat.le_mul_of_pos_right (2 ^ t) hquotPos).trans hfactorLe

/-- Inequality shadow of the exact odd-primary divisibility dichotomy. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_le
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      2 ^ t * (q / addOrderOf y) ≤ 2 * e.natAbs := by
  rcases hrows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_dvd
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    exact Nat.le_of_dvd (by omega) hfactor

/-- Uniform finite-factor form for coefficients supplied by the five-weight
cycle boundary: absent a smaller valid cyclic modulus, the exact odd-primary
quotient modulus is at most `84`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_le_eightyFour
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      2 ^ t * (q / addOrderOf y) ≤ 84 := by
  rcases hrows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_le
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    have habs : e.natAbs ≤ 42 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
    exact hfactor.trans (by omega)

/-- Uniform boundary cutoff in a modulus-minimal counterexample.  Every
five-weight bounded coefficient has `|e|≤42`, so absent a smaller valid cyclic
modulus the two-adic level is at most six. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_t_le_six
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      t ≤ 6 := by
  rcases hrows.exists_smallerValidCyclicModulus_or_two_pow_le_two_mul_natAbs
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hpower
  · exact Or.inl hsmaller
  · right
    have habs : e.natAbs ≤ 42 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
    have hpower84 : 2 ^ t ≤ 84 := hpower.trans (by omega)
    by_contra ht
    have hseven : 7 ≤ t := by omega
    have h128 : 2 ^ 7 ≤ 2 ^ t := pow_le_pow_right' (by omega) hseven
    have : 128 ≤ 84 := by norm_num at h128 ⊢; omega
    omega

/-- Rigidity at the top surviving boundary stratum.  If `t≥6`, exact
quotient divisibility and `|e|≤42` leave only `t=6`, full odd-primary order
`addOrderOf y=q`, and coefficient magnitude `32`, unless a smaller cyclic
modulus already carries a valid tuple of the same dimension. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.exists_smallerValidCyclicModulus_or_sixthStratum_boundary_rigidity
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 6 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    (∃ M : ℕ,
      0 < M ∧ M < 2 ^ t * q ∧ M ∣ 2 ^ t * q ∧
        AdmitsValidTuple n M) ∨
      (t = 6 ∧ q / addOrderOf y = 1 ∧ e.natAbs = 32) := by
  rcases hrows.exists_smallerValidCyclicModulus_or_oddPrimaryQuotientFactor_dvd
      g hg hunique hne y hyq B x z hxB hzB hxz hcomplement e he heMem with
    hsmaller | hfactor
  · exact Or.inl hsmaller
  · right
    have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq
      apply NeZero.ne (2 ^ t * q)
      simp only [hq, mul_zero]
    have hquotPos : 0 < q / addOrderOf y := by
      apply Nat.div_pos (Nat.le_of_dvd hqpos hyq)
      exact addOrderOf_pos y
    have habsPos : 0 < e.natAbs := Int.natAbs_pos.mpr he
    have habs : e.natAbs ≤ 42 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 42 := by omega
        exact_mod_cast this
    have hfactorLe :
        2 ^ t * (q / addOrderOf y) ≤ 2 * e.natAbs :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) habsPos) hfactor
    have hpower84 : 2 ^ t ≤ 84 :=
      (Nat.le_mul_of_pos_right (2 ^ t) hquotPos).trans
        (hfactorLe.trans (Nat.mul_le_mul_left 2 habs))
    have htLe : t ≤ 6 := by
      by_contra htNot
      have hseven : 7 ≤ t := by omega
      have h128 : 2 ^ 7 ≤ 2 ^ t := pow_le_pow_right' (by omega) hseven
      have : 128 ≤ 84 := by norm_num at h128 ⊢; omega
      omega
    have htEq : t = 6 := by omega
    subst t
    norm_num at hfactorLe
    have hquotOne : q / addOrderOf y = 1 := by omega
    obtain ⟨k, hk⟩ := hfactor
    norm_num [hquotOne] at hk
    have habsEq : e.natAbs = 32 := by omega
    exact ⟨rfl, hquotOne, habsEq⟩

/-- A bounded coefficient in a modulus-minimal sixth-stratum survivor forces
the cyclic kernel to have the full odd order and has absolute value `32`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    q / addOrderOf y = 1 ∧ e.natAbs = 32 := by
  rcases
      hrows.exists_smallerValidCyclicModulus_or_sixthStratum_boundary_rigidity
        (t := 6) (q := q) (by omega) g hg hunique hne y hyq B x z hxB hzB
          hxz hcomplement e he helow hehigh heMem with
    ⟨M, hMpos, hMlt, hMdiv, hvalid⟩ | hrigid
  · exact (hminimal M hMpos hMlt hMdiv hvalid).elim
  · exact hrigid.2

/-- Compatibility projection retaining only the coefficient magnitude. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    e.natAbs = 32 :=
  (hrows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
    g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
      e he helow hehigh heMem).2

/-- In a modulus-minimal sixth-stratum exact-two survivor whose cyclic kernel
has full odd-primary order, the retained difference is either primitive in
the order-`64` quotient or generates its unique index-two subgroup.  This is
an exact quotient-order statement, not a cardinal estimate. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.retainedDifference_quotientOrder_eq_thirtyTwo_or_sixtyFour_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
      AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+
        ZMod (2 ^ 6 * q) ⧸ H := QuotientAddGroup.mk' H
    addOrderOf (pi (g x - g z)) = 32 ∨
      addOrderOf (pi (g x - g z)) = 64 := by
  classical
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 6 * q) ⧸ H
  let pi : ZMod (2 ^ 6 * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ 6 * q) := g x - g z
  let deltaQ : Q := pi delta
  let eNat : ℕ := addOrderOf deltaQ
  let e : ℤ := eNat
  have hquotientModulus :
      (2 ^ 6 * q) / addOrderOf y = 64 := by
    rw [Nat.mul_div_assoc (2 ^ 6) hyq, hfullOdd]
    norm_num
  letI : Fintype Q := Fintype.ofFinite Q
  have hQcardNat : Nat.card Q = 64 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 6 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 6 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hQcard : Fintype.card Q = 64 := by
    simpa only [Nat.card_eq_fintype_card] using hQcardNat
  have hePos : 0 < eNat := addOrderOf_pos deltaQ
  have he : e ≠ 0 := by
    change (eNat : ℤ) ≠ 0
    omega
  have heMem : e • delta ∈ AddSubgroup.zmultiples y := by
    change e • delta ∈ H
    apply (QuotientAddGroup.eq_zero_iff (e • delta)).mp
    change pi (e • delta) = 0
    rw [map_zsmul]
    change (eNat : ℤ) • deltaQ = 0
    simpa only [natCast_zsmul] using addOrderOf_nsmul_eq_zero deltaQ
  have hfactor : (2 ^ 6 * q) / addOrderOf y ∣ 2 * e.natAbs := by
    rcases hrows.exists_smallerValidCyclicModulus_or_quotientFactor_dvd
        g hg hunique hne y B x z hxB hzB hxz hcomplement e he heMem with
      ⟨M, hMpos, hMlt, hMdiv, hvalid⟩ | hfactor
    · exact (hminimal M hMpos hMlt hMdiv hvalid).elim
    · exact hfactor
  have hfactor64 : 64 ∣ 2 * eNat := by
    rw [hquotientModulus] at hfactor
    simpa [e] using hfactor
  have heDvd64 : eNat ∣ 64 := by
    rw [← hQcard]
    exact addOrderOf_dvd_card
  have h32Dvd : 32 ∣ eNat := by
    obtain ⟨k, hk⟩ := hfactor64
    exact ⟨k, by omega⟩
  have heLe : eNat ≤ 64 := Nat.le_of_dvd (by norm_num) heDvd64
  obtain ⟨k, hk⟩ := h32Dvd
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · left
    simpa only [eNat, deltaQ, delta, pi, H, Q] using hk
  · right
    simpa only [eNat, deltaQ, delta, pi, H, Q] using hk

/-- Lossless two-primary phase split for the sixth-stratum exact-two matrix.
Every normalized private row is retained as a quotient equation.  If the
retained difference is primitive of order `64`, the odd weight `-1` cannot
occur: such a row would make that primitive difference a double. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.sixthStratum_quotientPhase
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ b : ↥B,
        (2 : ℤ) • (g (b : Fin n) - g z) +
            weight b • (g x - g z) ∈ AddSubgroup.zmultiples y) ∧
      let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
        AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+
          ZMod (2 ^ 6 * q) ⧸ H := QuotientAddGroup.mk' H
      addOrderOf (pi (g x - g z)) = 32 ∨
        (addOrderOf (pi (g x - g z)) = 64 ∧
          ∀ b : ↥B, weight b ≠ -1) := by
  classical
  have hrowsCopy := hrows
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  have hrelation : ∀ b : ↥B,
      (2 : ℤ) • (g (b : Fin n) - g z) +
          weight b • (g x - g z) ∈ AddSubgroup.zmultiples y := by
    intro b
    have htarget :
        twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
            (scalar b • y) ∈ AddSubgroup.zmultiples y := by
      exact AddSubgroup.zsmul_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
    have hrow := (hweightData b).2.2
    convert htarget using 1
    rw [hrow]
    module
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, hrelation, ?_⟩
  have horder :=
    hrowsCopy.retainedDifference_quotientOrder_eq_thirtyTwo_or_sixtyFour_of_sixthStratum_minimal
      g hg hunique hne y hyq hfullOdd B hminimal x z hxB hzB hxz hcomplement
  rcases horder with hthirtyTwo | hsixtyFour
  · exact Or.inl hthirtyTwo
  · right
    refine ⟨hsixtyFour, ?_⟩
    intro b hb
    let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
      AddSubgroup.zmultiples y
    let Q := ZMod (2 ^ 6 * q) ⧸ H
    let pi : ZMod (2 ^ 6 * q) →+ Q := QuotientAddGroup.mk' H
    let deltaQ : Q := pi (g x - g z)
    let betaQ : Q := pi (g (b : Fin n) - g z)
    letI : Fintype Q := Fintype.ofFinite Q
    have hquotientModulus :
        (2 ^ 6 * q) / addOrderOf y = 64 := by
      rw [Nat.mul_div_assoc (2 ^ 6) hyq, hfullOdd]
      norm_num
    have hQcardNat : Nat.card Q = 64 := by
      have hmul : Nat.card Q * addOrderOf y = 2 ^ 6 * q := by
        simpa only [Q, H, Nat.card_zmod] using
          nat_card_quotient_zmultiples_mul_addOrderOf y
      have hcard : Nat.card Q = (2 ^ 6 * q) / addOrderOf y := by
        exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
      exact hcard.trans hquotientModulus
    have hQcard : Fintype.card Q = 64 := by
      simpa only [Nat.card_eq_fintype_card] using hQcardNat
    have hquotientRelation :
        (2 : ℤ) • betaQ + weight b • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff
        ((2 : ℤ) • (g (b : Fin n) - g z) +
          weight b • (g x - g z))).mpr
      exact hrelation b
    have hdeltaDouble : deltaQ = (2 : ℕ) • betaQ := by
      rw [hb] at hquotientRelation
      change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
      have hrelation' : betaQ + betaQ - deltaQ = 0 := by
        simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
          hquotientRelation
      calc
        deltaQ = (betaQ + betaQ - deltaQ) + deltaQ := by
          rw [hrelation', zero_add]
        _ = betaQ + betaQ := by abel
        _ = (2 : ℕ) • betaQ := (two_nsmul betaQ).symm
    have hcardBeta : (64 : ℕ) • betaQ = 0 := by
      rw [← hQcard]
      exact card_nsmul_eq_zero
    have hthirtyTwoDelta : (32 : ℕ) • deltaQ = 0 := by
      rw [hdeltaDouble]
      calc
        (32 : ℕ) • ((2 : ℕ) • betaQ) = (64 : ℕ) • betaQ := by
          module
        _ = 0 := hcardBeta
    have hdvd : addOrderOf deltaQ ∣ 32 :=
      addOrderOf_dvd_of_nsmul_eq_zero hthirtyTwoDelta
    have horderQ : addOrderOf deltaQ = 64 := by
      simpa only [deltaQ, pi, H, Q] using hsixtyFour
    rw [horderQ] at hdvd
    norm_num at hdvd

/-- In a modulus-minimal sixth-stratum survivor, a fully deleted doubling
cycle cannot take the nonconstant bounded-multiple arm: that arm has
coefficient magnitude at most `18`, whereas sixth-stratum rigidity forces
magnitude `32`.  Hence the five-weight label is constant on all displayed
cycle leaves, without assuming that the doubling permutation is one cycle. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fullDeletedCycle_weight_constant_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ 6 * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∀ i j,
        weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩ := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hsmall | hconstant⟩ :=
    hrows.fullDeletedCycle_split g y B hd leaf R a hleafB hdouble
  · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
    have he32 :=
      hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
        g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
          e he (by omega) (by omega) heMem
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, hconstant⟩

/-- The four apparent top-boundary patterns disappear after their forced
short return is fed back into the same recurrence.  Consequently every
modulus-minimal sixth-stratum one-retained family with one available edge has
constant five-weight label on all deleted leaves. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_weight_constant_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
        (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
            (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y) ∧
      ∀ i (hi : leaf i ∈ B) j (hj : leaf j ∈ B),
        weight ⟨leaf i, hi⟩ = weight ⟨leaf j, hj⟩ := by
  obtain ⟨x, z, weight, cycleWeight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hcycleValue, hcycleWeight,
      hcycleTransition, hcycleTwoStep⟩ :=
    hrows.oneRetainedCycle_recurrence g y B leaf R a p hp hleafB hdouble
  have hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • (g x - g z) ∈ AddSubgroup.zmultiples y → e.natAbs = 32 := by
    intro e he helow hehigh heMem
    exact hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
        e he helow hehigh heMem
  have hconstant :=
    fiveWeightPuncturedPermutation_thirtyTwo_weight_constant
      R p i₀ hp hi₀ hRi₀ cycleWeight hcycleWeight
        (g x - g z) ((2 : ℤ) • (g z - a))
          (AddSubgroup.zmultiples y) hcycleTransition hcycleTwoStep hkernel32
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    hweight, htransition, ?_⟩
  intro i hiB j hjB
  have hi : i ≠ p := (hleafB i).1 hiB
  have hj : j ≠ p := (hleafB j).1 hjB
  calc
    weight ⟨leaf i, hiB⟩ = cycleWeight i := (hcycleValue i hiB).symm
    _ = cycleWeight j := hconstant i hi j hj
    _ = weight ⟨leaf j, hjB⟩ := hcycleValue j hjB

/-- Strong one-retained sixth-stratum endpoint.  Once the boundary-pattern
arm is removed globally, the constant terminal leaves only the two
orientation-equivalent presentations of the pure-pair matrix. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_purePair_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hconstant⟩ :=
    hrows.oneRetainedCycle_weight_constant_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal leaf R a p i₀ hp hi₀ hRi₀
        hleafB hdouble
  have hiB : leaf i₀ ∈ B := (hleafB i₀).2 hi₀
  have hRiB : leaf (R i₀) ∈ B := (hleafB (R i₀)).2 hRi₀
  let w : ℤ := weight ⟨leaf i₀, hiB⟩
  have hw : w ∈ twoRetainedNormalizedWeightLevels :=
    hweight ⟨leaf i₀, hiB⟩
  have hwEdge : weight ⟨leaf (R i₀), hRiB⟩ = w := by
    simpa only [w] using hconstant (R i₀) hRiB i₀ hiB
  have htransitionSimple :
      (-w) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
        AddSubgroup.zmultiples y := by
    have ht := htransition i₀ hiB hRiB
    rw [hwEdge] at ht
    convert ht using 1
    dsimp only [w]
    module
  have hterminal := constantFiveWeight_transition_terminal
    (g x) (g z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
  have hpNotB : leaf p ∉ B := by
    intro hpB
    exact (hleafB p).1 hpB rfl
  have hpPair : leaf p = x ∨ leaf p = z := by
    have hpComplement : leaf p ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotB⟩
    rw [hcomplement] at hpComplement
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpComplement
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
  rcases hpPair with hpX | hpZ
  · have hxMem : g x - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hpX] using hretainedMem
    rcases hterminal.1 hxMem with hsmall | hwMinusTwo
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
            e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inl ⟨hpX, fun i hi ↦
        (hconstant i hi i₀ hiB).trans hwMinusTwo⟩
  · have hzMem : g z - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hpZ] using hretainedMem
    rcases hterminal.2 hzMem with hsmall | hwZero
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
            e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inr ⟨hpZ, fun i hi ↦
        (hconstant i hi i₀ hiB).trans hwZero⟩

/-- Integrated top-stratum one-retained endpoint.  In a modulus-minimal
`2^6*q` survivor, the nonconstant five-weight arm returns to the unavailable
leaf after two or three permutation steps. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_shortReturn_or_weight_constant_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (∀ i (hi : leaf i ∈ B) (hRi : leaf (R i) ∈ B),
        (weight ⟨leaf (R i), hRi⟩ - 2 * weight ⟨leaf i, hi⟩) •
            (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y) ∧
      ((q / addOrderOf y = 1 ∧
          (R (R p) = p ∨ R (R (R p)) = p)) ∨
        ∀ i (hi : leaf i ∈ B) j (hj : leaf j ∈ B),
          weight ⟨leaf i, hi⟩ = weight ⟨leaf j, hj⟩) := by
  obtain ⟨x, z, weight, cycleWeight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hcycleValue, hcycleWeight,
      hcycleTransition, hcycleTwoStep⟩ :=
    hrows.oneRetainedCycle_recurrence g y B leaf R a p hp hleafB hdouble
  have hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • (g x - g z) ∈ AddSubgroup.zmultiples y → e.natAbs = 32 := by
    intro e he helow hehigh heMem
    exact hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
        e he helow hehigh heMem
  have hout :=
    fiveWeightPuncturedPermutation_thirtyTwo_boundaryPatternWithTransition_or_weight_constant
      R p i₀ hp hi₀ hRi₀ cycleWeight hcycleWeight
        (g x - g z) ((2 : ℤ) • (g z - a))
          (AddSubgroup.zmultiples y) hcycleTransition hcycleTwoStep hkernel32
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    hweight, htransition, ?_⟩
  rcases hout with ⟨hpattern, hall⟩ | hconstant
  · have hshort := fiveWeight_boundaryPatternWithTransition_shortReturn
      R p i₀ hp cycleWeight hcycleWeight hpattern hall
    let e : ℤ :=
      (cycleWeight (R p) - 4 * cycleWeight (R.symm p)) -
        3 * (cycleWeight (R i₀) - 2 * cycleWeight i₀)
    have heBounds : -42 ≤ e ∧ e ≤ 42 := by
      rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
        rcases hpattern with ⟨hu, hv, hi, hRi⟩ <;>
        simp only [e, hu, hv, hi, hRi] <;>
        omega
    have he : e ≠ 0 := by
      intro heZero
      rcases hpattern with hpattern | hpattern | hpattern | hpattern <;>
        rcases hpattern with ⟨hu, hv, hi, hRi⟩ <;>
        simp only [e, hu, hv, hi, hRi] at heZero <;>
        omega
    have heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y := by
      have hthree := (AddSubgroup.zmultiples y).zsmul_mem
        (hcycleTransition i₀ hi₀ hRi₀) 3
      have hsub := (AddSubgroup.zmultiples y).sub_mem hcycleTwoStep hthree
      convert hsub using 1
      dsimp only [e]
      module
    have hfull :=
      hrows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
        g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
          e he heBounds.1 heBounds.2 heMem
    exact Or.inl ⟨hfull.1, hshort⟩
  · right
    intro i hiB j hjB
    have hi : i ≠ p := (hleafB i).1 hiB
    have hj : j ≠ p := (hleafB j).1 hjB
    calc
      weight ⟨leaf i, hiB⟩ = cycleWeight i := (hcycleValue i hiB).symm
      _ = cycleWeight j := hconstant i hi j hj
      _ = weight ⟨leaf j, hjB⟩ := hcycleValue j hjB

/-- At the sixth stratum, the constant branch of the integrated endpoint is
again exactly the orientation-equivalent pure pair.  Every alternative
bounded coefficient has magnitude at most four and is therefore incompatible
with the forced magnitude `32`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_shortReturn_or_purePair_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((q / addOrderOf y = 1 ∧
          (R (R p) = p ∨ R (R (R p)) = p)) ∨
        (leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hshort | hconstant⟩ :=
    hrows.oneRetainedCycle_shortReturn_or_weight_constant_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal leaf R a p i₀ hp hi₀ hRi₀
        hleafB hdouble
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      Or.inl hshort⟩
  · refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
    have hiB : leaf i₀ ∈ B := (hleafB i₀).2 hi₀
    have hRiB : leaf (R i₀) ∈ B := (hleafB (R i₀)).2 hRi₀
    let w : ℤ := weight ⟨leaf i₀, hiB⟩
    have hw : w ∈ twoRetainedNormalizedWeightLevels :=
      hweight ⟨leaf i₀, hiB⟩
    have hwEdge : weight ⟨leaf (R i₀), hRiB⟩ = w := by
      simpa only [w] using hconstant (R i₀) hRiB i₀ hiB
    have htransitionSimple :
        (-w) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y := by
      have ht := htransition i₀ hiB hRiB
      rw [hwEdge] at ht
      convert ht using 1
      dsimp only [w]
      module
    have hterminal := constantFiveWeight_transition_terminal
      (g x) (g z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
    have hpNotB : leaf p ∉ B := by
      intro hpB
      exact (hleafB p).1 hpB rfl
    have hpPair : leaf p = x ∨ leaf p = z := by
      have hpComplement : leaf p ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotB⟩
      rw [hcomplement] at hpComplement
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpComplement
    rcases hpPair with hpX | hpZ
    · have hxMem : g x - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpX] using hretainedMem
      rcases hterminal.1 hxMem with hsmall | hwMinusTwo
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        have he32 :=
          hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
            g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
              e he (by omega) (by omega) heMem
        have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
        rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
      · exact Or.inr (Or.inl ⟨hpX, by
          intro i hi
          calc
            weight ⟨leaf i, hi⟩ = w := hconstant i hi i₀ hiB
            _ = -2 := hwMinusTwo⟩)
    · have hzMem : g z - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpZ] using hretainedMem
      rcases hterminal.2 hzMem with hsmall | hwZero
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        have he32 :=
          hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
            g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
              e he (by omega) (by omega) heMem
        have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
        rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
      · exact Or.inr (Or.inr ⟨hpZ, by
          intro i hi
          calc
            weight ⟨leaf i, hi⟩ = w := hconstant i hi i₀ hiB
            _ = 0 := hwZero⟩)

/-- A sixth-stratum modulus-minimal one-retained cycle whose unavailable leaf
does not return in two or three steps is forced into the pure-pair arm. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_purePair_of_sixthStratum_longCycle
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hreturnTwo : R (R p) ≠ p) (hreturnThree : R (R (R p)) ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hshort | hpure⟩ :=
    hrows.oneRetainedCycle_shortReturn_or_purePair_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal leaf R a p i₀ hp hi₀ hRi₀
        hleafB hdouble hretainedMem
  · rcases hshort.2 with htwo | hthree
    · exact (hreturnTwo htwo).elim
    · exact (hreturnThree hthree).elim
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hpure⟩

/-- Critical full-cycle specialization of the sixth-stratum short-return
endpoint.  Exact span generation turns the two possible returns into
`q | 3` or `q | 7`; nontriviality removes `q=1`, and the universal tuple
cardinality bound plus criticality leaves exactly `(n,q)=(8,3),(9,3),(9,7)`.
Every other case is the common pure-pair arm. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalSixthStratum_finitePairs_or_purePair
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (a : ZMod (2 ^ 6 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      (((n = 8 ∧ q = 3) ∨ (n = 9 ∧ q = 3) ∨
          (n = 9 ∧ q = 7)) ∨
        (leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  let disp : Fin d → ZMod (2 ^ 6 * q) :=
    fun i ↦ g (leaf i) - a
  have hspanDisp : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y := by
    simpa only [disp] using hspan
  have hdispMem : ∀ i, disp i ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspanDisp]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hretainedMem :
      g (leaf p) - a ∈ AddSubgroup.zmultiples y := by
    simpa only [disp] using hdispMem p
  have hp : R p ≠ p := hRne p
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hshort | hpure⟩ :=
    hrows.oneRetainedCycle_shortReturn_or_purePair_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal leaf R a p i₀ hp hi₀ hRi₀
        hleafB hdouble hretainedMem
  · have hdoubleNat : ∀ i, disp (R i) = 2 • disp i := by
      intro i
      simpa only [disp, two_nsmul, two_zsmul] using hdouble i
    have horderDvd :=
      addOrderOf_dvd_three_or_seven_of_isCycle_doubling_shortReturn
        R hRcycle hRne disp hdoubleNat p y hspanDisp hshort.2
    have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq
      apply NeZero.ne (2 ^ 6 * q)
      simp only [hq, mul_zero]
    have hqEq : q = addOrderOf y := by
      calc
        q = (q / addOrderOf y) * addOrderOf y :=
          (Nat.div_mul_cancel hyq).symm
        _ = 1 * addOrderOf y := by rw [hshort.1]
        _ = addOrderOf y := one_mul _
    have hyne : y ≠ 0 := by
      intro hyzero
      have hpZero : disp p = 0 := by
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hdispMem p)
        calc
          disp p = k • y := hk.symm
          _ = 0 := by rw [hyzero]; simp
      have hRpZero : disp (R p) = 0 := by
        obtain ⟨k, hk⟩ :=
          AddSubgroup.mem_zmultiples_iff.mp (hdispMem (R p))
        calc
          disp (R p) = k • y := hk.symm
          _ = 0 := by rw [hyzero]; simp
      have hvalueEq : g (leaf p) = g (leaf (R p)) := by
        dsimp only [disp] at hpZero hRpZero
        calc
          g (leaf p) = (g (leaf p) - a) + a := by abel
          _ = 0 + a := by rw [hpZero]
          _ = (g (leaf (R p)) - a) + a := by rw [hRpZero]
          _ = g (leaf (R p)) := by abel
      have hindexEq : p = R p :=
        hleafInj (validTuple_injective g hg hvalueEq)
      exact hp hindexEq.symm
    have hqNeOne : q ≠ 1 := by
      rw [hqEq]
      intro horderOne
      exact hyne (AddMonoid.addOrderOf_eq_one_iff.mp horderOne)
    have hqCases : q = 3 ∨ q = 7 := by
      rcases horderDvd with hthree | hseven
      · left
        have hqThree : q ∣ 3 := by simpa only [hqEq] using hthree
        exact ((Nat.dvd_prime Nat.prime_three).mp hqThree).resolve_left hqNeOne
      · right
        have hqSeven : q ∣ 7 := by simpa only [hqEq] using hseven
        have hprimeSeven : Nat.Prime 7 := by norm_num
        exact ((Nat.dvd_prime hprimeSeven).mp hqSeven).resolve_left hqNeOne
    have hqle : q ≤ 7 := by
      rcases hqCases with rfl | rfl <;> omega
    have hlower : 2 ^ (n - 1) ≤ 2 ^ 6 * q := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using
        (two_pow_pred_le_card_of_validTuple g hg)
    have hnle : n ≤ 9 := by
      by_contra hnNot
      have hnTen : 10 ≤ n := by omega
      have hpow : 2 ^ 9 ≤ 2 ^ (n - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hmodLe : 2 ^ 6 * q ≤ 2 ^ 6 * 7 :=
        Nat.mul_le_mul_left (2 ^ 6) hqle
      norm_num at hpow hmodLe
      omega
    refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, Or.inl ?_⟩
    rcases hqCases with hqThree | hqSeven
    · subst q
      have hnCases : n = 8 ∨ n = 9 := by
        have hnEight : 8 ≤ n := by
          by_contra hnNot
          have hnSeven : n ≤ 7 := by omega
          have hbound : stratumBound n 6 ≤ 128 := by
            interval_cases n <;> norm_num [stratumBound]
          norm_num at hcritical
          omega
        omega
      rcases hnCases with hnEight | hnNine
      · exact Or.inl ⟨hnEight, rfl⟩
      · exact Or.inr (Or.inl ⟨hnNine, rfl⟩)
    · subst q
      have hnNine : n = 9 := by
        have hnNineLower : 9 ≤ n := by
          by_contra hnNot
          have hnEight : n ≤ 8 := by omega
          have hbound : stratumBound n 6 ≤ 248 := by
            interval_cases n <;> norm_num [stratumBound]
          norm_num at hcritical
          omega
        omega
      exact Or.inr (Or.inr ⟨hnNine, rfl⟩)
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      Or.inr hpure⟩

/-- The two-leaf boundary needs no available transition edge.  The single
deleted leaf's private affine row can instead be compared directly with its
displacement in the full cyclic span.  At the sixth stratum this gives a
coefficient of magnitude at most four unless the row is the pure pair, while
modulus minimality forces every nonzero bounded coefficient to have magnitude
thirty-two.  Thus the downstream `d=2` leaf cycle is itself pure-pair; it is
not an invocation of the unrelated private-shift two-cycle theorem. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedTwoLeaf_purePair_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (leaf : Fin 2 → Fin n) (a : ZMod (2 ^ 6 * q)) (p : Fin 2)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin 2 ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  classical
  have hrowsCopy := hrows
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  obtain ⟨i₀, hi₀p⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := Fin 2) (by simp) p
  have hi₀B : leaf i₀ ∈ B := (hleafB i₀).2 hi₀p
  let b : ↥B := ⟨leaf i₀, hi₀B⟩
  let w : ℤ := weight b
  have hw : w ∈ twoRetainedNormalizedWeightLevels :=
    (hweightData b).1
  have haffine := (hweightData b).2.2
  have hleftMem :
      twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
          (scalar b • y) ∈ AddSubgroup.zmultiples y := by
    exact (AddSubgroup.zmultiples y).zsmul_mem
      ((AddSubgroup.zmultiples y).zsmul_mem
        (AddSubgroup.mem_zmultiples y) (scalar b))
      (twoRetainedOwnerNormalization (coeff b (b : Fin n)))
  have hrowMem :
      (2 : ℤ) • g (leaf i₀) + w • (g x - g z) -
          (2 : ℤ) • g z ∈ AddSubgroup.zmultiples y := by
    rw [← haffine]
    simpa only [b, w] using hleftMem
  have hi₀Disp : g (leaf i₀) - a ∈ AddSubgroup.zmultiples y := by
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i₀, rfl⟩
  have htransitionSimple :
      (-w) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
        AddSubgroup.zmultiples y := by
    have hsub := (AddSubgroup.zmultiples y).sub_mem hrowMem
      ((AddSubgroup.zmultiples y).zsmul_mem hi₀Disp 2)
    have hneg := (AddSubgroup.zmultiples y).neg_mem hsub
    convert hneg using 1
    module
  have hterminal := constantFiveWeight_transition_terminal
    (g x) (g z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
  have hpNotB : leaf p ∉ B := by
    intro hpB
    exact (hleafB p).1 hpB rfl
  have hpPair : leaf p = x ∨ leaf p = z := by
    have hpComplement : leaf p ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotB⟩
    rw [hcomplement] at hpComplement
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpComplement
  have hpDisp : g (leaf p) - a ∈ AddSubgroup.zmultiples y := by
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨p, rfl⟩
  have hother : ∀ i : Fin 2, i ≠ p → i = i₀ := by
    intro i hip
    fin_omega
  have hweightOther : ∀ i (hi : leaf i ∈ B), weight ⟨leaf i, hi⟩ = w := by
    intro i hi
    have hip : i ≠ p := (hleafB i).1 hi
    have hii : i = i₀ := hother i hip
    subst i
    have hb : (⟨leaf i₀, hi⟩ : ↥B) = b := by
      apply Subtype.ext
      rfl
    exact (congrArg weight hb).trans rfl
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, ?_⟩
  rcases hpPair with hpX | hpZ
  · have hxMem : g x - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hpX] using hpDisp
    rcases hterminal.1 hxMem with hsmall | hwMinusTwo
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrowsCopy.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
            e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inl ⟨hpX, fun i hi ↦
        (hweightOther i hi).trans hwMinusTwo⟩
  · have hzMem : g z - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hpZ] using hpDisp
    rcases hterminal.2 hzMem with hsmall | hwZero
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrowsCopy.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
            e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inr ⟨hpZ, fun i hi ↦
        (hweightOther i hi).trans hwZero⟩

/-- Lossless sixth-stratum terminal for the all-but-one global leaf
incidence.  A fully deleted family has constant five-weight label, while
every family with a unique retained leaf is orientation-equivalent pure-pair.
The relative permutation may have any number of components. -/
def TwoRetainedSixthStratumLeafTerminal
    (B : Finset (Fin n)) {d : ℕ}
    (leaf : Fin d → Fin n) : Prop :=
  (∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∃ hleafB : ∀ i, leaf i ∈ B,
        ∀ i j,
          weight ⟨leaf i, hleafB i⟩ =
            weight ⟨leaf j, hleafB j⟩) ∨
    ∃ p : Fin d,
      (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
      ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
        x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
        (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
        ((leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
            weight ⟨leaf i, hi⟩ = -2) ∨
          (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
            weight ⟨leaf i, hi⟩ = 0))

/-- Combine the global all-but-one incidence with the exact sixth-stratum
cycle arithmetic.  No single-cycle assumption is needed: the restarted
boundary-pattern collision makes every unique-retained component pure-pair. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.sixthStratum_leafTerminal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (a : ZMod (2 ^ 6 * q))
    (hleafIncidence : (∀ i, leaf i ∈ B) ∨
      ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    TwoRetainedSixthStratumLeafTerminal B leaf := by
  rcases hleafIncidence with hfull | ⟨p, hpunctured⟩
  · left
    obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
        hweight, hconstant⟩ :=
      hrows.fullDeletedCycle_weight_constant_of_sixthStratum_minimal
        g hg hunique hne y hyq B hminimal (by omega) leaf R a hfull hdouble
    exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, hfull, hconstant⟩
  · right
    refine ⟨p, hpunctured, ?_⟩
    by_cases hdTwo : d = 2
    · subst d
      obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
          hweight, hpure⟩ :=
        hrows.oneRetainedTwoLeaf_purePair_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal leaf a p hpunctured hspan
      exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hpure⟩
    have hdThree : 2 < d := by omega
    obtain ⟨i₀, hi₀p, hi₀prev⟩ :=
      Fin.exists_ne_and_ne_of_two_lt p (R.symm p) hdThree
    have hRi₀ : R i₀ ≠ p := by
      intro hRi₀
      apply hi₀prev
      calc
        i₀ = R.symm (R i₀) := (R.symm_apply_apply i₀).symm
        _ = R.symm p := congrArg R.symm hRi₀
    have hpMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y := by
      rw [← hspan]
      exact AddSubgroup.subset_closure ⟨p, rfl⟩
    obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
        hweight, hpure⟩ :=
      hrows.oneRetainedCycle_purePair_of_sixthStratum_minimal
        g hg hunique hne y hyq B hminimal leaf R a p i₀ (hRne p)
          hi₀p hRi₀ hpunctured hdouble hpMem
    exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hpure⟩

/-- Global exact-two specialization of `sixthStratum_leafTerminal`.  Its
hypotheses are precisely the fields retained by the aligned full-cycle
outcome: the common full-span generator, the incidence/charge descent, the
relative fixed-point-free doubling permutation, and the five-weight private
rows.  In particular, the odd-order divisibility and all-but-one incidence
are projected from the global charge package rather than re-assumed. -/
theorem sixthStratum_leafTerminal_of_fullCycleExactTwo
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (B : Finset (Fin (m + 1)))
    (leaf : Fin d → Fin (m + 1))
    (hd : 2 ≤ d)
    (hretained : OddPrimaryFullCycleRetainedExternalChargeDescent
      g y B d leaf)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (hleaf : Function.Injective leaf)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple (m + 1) M) :
    TwoRetainedSixthStratumLeafTerminal B leaf := by
  have hyq : addOrderOf y ∣ q := hretained.1.1.2.2.2.2.1
  have hleafIncidence :=
    OddPrimaryFullCycleIncidenceChargeDescent.fullDeleted_or_exists_unique_retained_leaf
      hretained.1 hleaf
  exact hrows.sixthStratum_leafTerminal
    g hg hunique hne y hyq B hminimal hd leaf R hRne base
      hleafIncidence hdouble hspan

/-- Uniform numerical consequence for every coefficient produced by the
five-weight cycle split. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.card_le_eightyFour_mul
    [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    2 ^ (n - 1) ≤ 84 * addOrderOf y := by
  have habs : e.natAbs ≤ 42 := by
    rcases Int.natAbs_eq e with hePos | heNeg
    · have : (e.natAbs : ℤ) ≤ 42 := by omega
      exact_mod_cast this
    · have : (e.natAbs : ℤ) ≤ 42 := by omega
      exact_mod_cast this
  have hbound := hrows.card_le_two_mul_natAbs_mul
    g hg hunique hne y B e he
      ⟨x, z, hxB, hzB, hxz, hcomplement, heMem⟩
  calc
    2 ^ (n - 1) ≤ 2 * e.natAbs * addOrderOf y := hbound
    _ ≤ 2 * 42 * addOrderOf y :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 habs)
    _ = 84 * addOrderOf y := by omega

/-- Exact coefficient-sensitive exclusion for the bounded-multiple arm.  A
critical cyclic stratum cannot contain such a relation once the ambient
two-primary factor satisfies `4*|e| <= 2^t`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.not_boundedMultiple_of_four_mul_natAbs_le
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound n t)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y)
    (hthreshold : 4 * e.natAbs ≤ 2 ^ t) : False := by
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hq
    apply NeZero.ne (2 ^ t * q)
    simp only [hq, mul_zero]
  have hry : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hyq
  have hcard := hrows.card_le_two_mul_natAbs_mul
    g hg hunique hne y B e he
      ⟨x, z, hxB, hzB, hxz, hcomplement, heMem⟩
  have hbound : 2 ^ (n - 1) ≤ 2 * e.natAbs * q :=
    hcard.trans (Nat.mul_le_mul_left (2 * e.natAbs) hry)
  have hambient : 2 ^ t * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := by omega
    subst n
    simp only [pow_zero] at hambient
    have hNpos : 0 < 2 ^ t * q := Nat.mul_pos (pow_pos (by omega) _) hqpos
    omega
  have hpowN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hnDecomp : n = (n - 1) + 1 := by omega
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by rw [← hnDecomp]
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ]; omega
  have hthresholdQ : 4 * e.natAbs * q ≤ 2 ^ t * q :=
    Nat.mul_le_mul_right q hthreshold
  have hdoubleBound : 2 * 2 ^ (n - 1) ≤ 4 * e.natAbs * q := by
    calc
      2 * 2 ^ (n - 1) ≤ 2 * (2 * e.natAbs * q) :=
        Nat.mul_le_mul_left 2 hbound
      _ = 4 * e.natAbs * q := by ring
  rw [hpowN] at hambient
  omega

/-- Contrapositive numerical form: every surviving bounded relation in a
critical stratum has coefficient larger than one quarter of `2^t`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.two_pow_lt_four_mul_natAbs_of_boundedMultiple
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound n t)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) :
    2 ^ t < 4 * e.natAbs := by
  by_contra hnot
  have hthreshold : 4 * e.natAbs ≤ 2 ^ t := by omega
  exact hrows.not_boundedMultiple_of_four_mul_natAbs_le
    g hg hcritical hunique hne y hyq B x z hxB hzB hxz hcomplement
      e he heMem hthreshold

/-- The bounded-multiple arm is impossible in every critical cyclic stratum
with `t>=8`.  The factor-84 confinement contradicts the factor `2^t` already
present in the ambient modulus. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.not_boundedMultiple_of_eight_le
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 8 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound n t)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z})
    (e : ℤ) (he : e ≠ 0) (helow : -42 ≤ e) (hehigh : e ≤ 42)
    (heMem : e • (g x - g z) ∈ AddSubgroup.zmultiples y) : False := by
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hq
    apply NeZero.ne (2 ^ t * q)
    simp only [hq, mul_zero]
  have hry : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hyq
  have h84 := hrows.card_le_eightyFour_mul
    g hg hunique hne y B x z hxB hzB hxz hcomplement
      e he helow hehigh heMem
  have hbound : 2 ^ (n - 1) ≤ 84 * q :=
    h84.trans (Nat.mul_le_mul_left 84 hry)
  have hambient : 2 ^ t * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := by omega
    subst n
    simp only [pow_zero] at hambient
    have hNpos : 0 < 2 ^ t * q := Nat.mul_pos (pow_pos (by omega) _) hqpos
    omega
  have hpowN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hnDecomp : n = (n - 1) + 1 := by omega
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by rw [← hnDecomp]
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ]; omega
  have h256 : 256 ≤ 2 ^ t := by
    have hp := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
    norm_num at hp ⊢
    exact hp
  have h256q : 256 * q ≤ 2 ^ t * q :=
    Nat.mul_le_mul_right q h256
  omega

/-- High-stratum terminal endpoint for the unique-retained-leaf cycle.  At
`t>=8` the factor-84 estimate removes the bounded-multiple alternative, so
only the orientation-equivalent pure-pair weight remains. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_purePair_of_eight_le
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 8 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound n t)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ t * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hsmall | hpure⟩ :=
    hrows.oneRetainedCycle_terminal g y B leaf R a p i₀ hp hi₀ hRi₀
      hleafB hdouble hretainedMem
  · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
    exact (hrows.not_boundedMultiple_of_eight_le ht g hg hcritical
      hunique hne y hyq B x z hxB hzB hxz hcomplement
        e he helow hehigh heMem).elim
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hpure⟩

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
                TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
                ((∀ j : Fin d, leaf j ∈ B) ∨
                  ∃ p : Fin d, ∀ j : Fin d, leaf j ∈ B ↔ j ≠ p) ∧
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
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
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
    have hleaf : Function.Injective leaf := by
      intro j k hjk
      apply minimalFixedPointFreeCycle_iterates_injective T hcycle
      exact Subtype.ext hjk
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
        have hprivate :=
          twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
            g hg hh hne hunique hno y hretainedCharge.1.1.1 hexact
        have hfive := hprivate.fiveWeightRows g y B
        have hleafSplit :=
          OddPrimaryFullCycleIncidenceChargeDescent.fullDeleted_or_exists_unique_retained_leaf
            hretainedCharge.1 hleaf
        refine ⟨hprivate, hfive, hleafSplit, ?_⟩
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
      g hg hh hne hunique hno r T hcycle center hout componentThreshold
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
