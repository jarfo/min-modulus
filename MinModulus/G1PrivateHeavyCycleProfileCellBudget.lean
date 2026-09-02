/-
# Deterministic cycle cells and their global mass budget

The near-spanning labelled light-profile family is a finset of cycle indices.
This module records its exact deterministic `(incoming label, profile)`
fibers.  A cell is contained in the full cycle fiber of its profile, so its
cardinality is bounded by the source-zero padding power.  Active cells omit
their deterministic label and therefore enter the one-budget cross-label
incidence family.

The diagonal cells are retained separately.  Outside the three-omission
frontier, a profile can occur under at most two labels; injectivity of raw
profile reduction and the raw/canonical two-element orbits then charge the
whole active diagonal to four times canonical diagonal mass.
-/
import MinModulus.G1PrivateHeavyCrossLabelProfileBudget

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Cauchy--Schwarz after partitioning a weighted finset of pairs by its first
coordinate.  The quadratic term is exactly its same-label off-diagonal plus
its diagonal. -/
theorem square_sum_le_activeLabels_mul_sameLabelQuadratic
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset (α × β)) (w : α × β → ℕ) :
    (C.sum w) ^ 2 ≤ (C.image Prod.fst).card *
      ((C.offDiag.filter fun p ↦ p.1.1 = p.2.1).sum
          (fun p ↦ w p.1 * w p.2) +
        C.sum (fun p ↦ w p * w p)) := by
  classical
  let L := C.image Prod.fst
  let fiber : α → Finset (α × β) := fun z ↦
    C.filter fun p ↦ p.1 = z
  let mass : α → ℕ := fun z ↦ (fiber z).sum w
  let pairWeight : (α × β) × (α × β) → ℕ := fun p ↦
    w p.1 * w p.2
  let Q := C.offDiag.filter fun p ↦ p.1.1 = p.2.1
  have hmapsC : C.filter (fun p ↦ p.1 ∈ L) = C := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hmass : L.sum mass = C.sum w := by
    have hfiber := Finset.sum_fiberwise_eq_sum_filter C L Prod.fst w
    rw [hmapsC] at hfiber
    simpa [mass, fiber] using hfiber
  have hmapsQ : Q.filter (fun p ↦ p.1.1 ∈ L) = Q := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hpQ := Finset.mem_filter.mp hp
    have hpOff := Finset.mem_offDiag.mp hpQ.1
    exact Finset.mem_image.mpr ⟨p.1, hpOff.1, rfl⟩
  have hpairs : L.sum (fun z ↦ (fiber z).offDiag.sum pairWeight) =
      Q.sum pairWeight := by
    have hfiber := Finset.sum_fiberwise_eq_sum_filter Q L
      (fun p ↦ p.1.1) pairWeight
    rw [hmapsQ] at hfiber
    calc
      L.sum (fun z ↦ (fiber z).offDiag.sum pairWeight) =
          L.sum (fun z ↦
            (Q.filter fun p ↦ p.1.1 = z).sum pairWeight) := by
        apply Finset.sum_congr rfl
        intro z _hz
        congr 1
        ext p
        simp only [fiber, Q, Finset.mem_offDiag, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hpC, hpz⟩, ⟨huC, huz⟩, hpu⟩
          exact ⟨⟨⟨hpC, huC, hpu⟩, hpz.trans huz.symm⟩, hpz⟩
        · rintro ⟨⟨⟨hpC, huC, hpu⟩, hsame⟩, hpz⟩
          exact ⟨⟨hpC, hpz⟩, ⟨huC, hsame.symm.trans hpz⟩, hpu⟩
      _ = Q.sum pairWeight := hfiber
  have hdiag : L.sum (fun z ↦
      (fiber z).sum fun p ↦ w p * w p) =
      C.sum (fun p ↦ w p * w p) := by
    have hfiber := Finset.sum_fiberwise_eq_sum_filter C L Prod.fst
      (fun p ↦ w p * w p)
    rw [hmapsC] at hfiber
    simpa [fiber] using hfiber
  have hsquare : ∀ z, mass z * mass z =
      (fiber z).offDiag.sum pairWeight +
        (fiber z).sum (fun p ↦ w p * w p) := by
    intro z
    let F := fiber z
    calc
      mass z * mass z = (F ×ˢ F).sum pairWeight := by
        rw [Finset.sum_product]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
      _ = (F.diag ∪ F.offDiag).sum pairWeight := by
        rw [Finset.diag_union_offDiag]
      _ = F.diag.sum pairWeight + F.offDiag.sum pairWeight :=
        Finset.sum_union (Finset.disjoint_diag_offDiag F)
      _ = F.offDiag.sum pairWeight +
          F.sum (fun p ↦ w p * w p) := by
        rw [Finset.sum_diag]
        exact Nat.add_comm _ _
  have hquadratic : L.sum (fun z ↦ mass z ^ 2) =
      Q.sum pairWeight + C.sum (fun p ↦ w p * w p) := by
    simp_rw [pow_two, hsquare, Finset.sum_add_distrib, hpairs, hdiag]
  have hcs := sq_sum_le_card_mul_sum_sq (s := L) (f := mass)
  rw [hmass, hquadratic] at hcs
  exact hcs

/-- Squared-weight mass of the critical canonical collision diagonal. -/
noncomputable def criticalCanonicalDiagonalMass
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : ℕ :=
  (criticalCanonicalReducedCollisions g).sum (fun r ↦
    reducedCollisionWeight (m := n) r *
      reducedCollisionWeight (m := n) r)

/-- The deterministic incoming label and complete avoiding profile carried by
one retained cycle index. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileAt
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)) :
    Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) := by
  classical
  refine ⟨minimalSupportPrivateShiftCycleIncomingEdgeLabel
      g hg hh hno hmin a i.val,
    ⟨minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i.val, ?_⟩⟩
  apply
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles_iff
      g hno hmin a d _).mpr
  exact ⟨i.val,
    ((mem_minimalSupportPrivateShiftCycleLabelledLightProfileIndices_iff
      g hg hh hno hmin a d i.val).mp i.property).2.2, rfl⟩

omit [DecidableEq G] in
@[simp] theorem minimalSupportPrivateShiftCycleLabelProfileAt_fst
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)) :
    (minimalSupportPrivateShiftCycleLabelProfileAt
      g hg hh hno hmin a d i).1 =
      minimalSupportPrivateShiftCycleIncomingEdgeLabel
        g hg hh hno hmin a i.val := by
  rfl

omit [DecidableEq G] in
@[simp] theorem minimalSupportPrivateShiftCycleLabelProfileAt_snd_val
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)) :
    (minimalSupportPrivateShiftCycleLabelProfileAt
      g hg hh hno hmin a d i).2.val =
      minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i.val := by
  rfl

omit [DecidableEq G] in
/-- Every deterministic cell profile omits its deterministic incoming label. -/
theorem minimalSupportPrivateShiftCycleLabelProfileAt_omits
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)) :
    (minimalSupportPrivateShiftCycleLabelProfileAt
      g hg hh hno hmin a d i).2.val
        (minimalSupportPrivateShiftCycleLabelProfileAt
          g hg hh hno hmin a d i).1 = -1 := by
  have hi :=
    (mem_minimalSupportPrivateShiftCycleLabelledLightProfileIndices_iff
      g hg hh hno hmin a d i.val).mp i.property
  simpa only [minimalSupportPrivateShiftCycleLabelProfileAt_fst,
    minimalSupportPrivateShiftCycleLabelProfileAt_snd_val,
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness] using hi.2.1.2.2

/-- The finite set of active deterministic `(label, profile)` cells. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCells
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    Finset (Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) := by
  classical
  exact
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d).attach.image
        (minimalSupportPrivateShiftCycleLabelProfileAt
          g hg hh hno hmin a d)

/-- Indices in one deterministic `(label, profile)` cell. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCell
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) :
    Finset ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d) := by
  classical
  exact
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d).attach.filter fun i ↦
        minimalSupportPrivateShiftCycleLabelProfileAt
          g hg hh hno hmin a d i = p

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleLabelProfileCells_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) :
    p ∈ minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d ↔
      ∃ i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
          g hg hh hno hmin a d),
        minimalSupportPrivateShiftCycleLabelProfileAt
          g hg hh hno hmin a d i = p := by
  classical
  simp [minimalSupportPrivateShiftCycleLabelProfileCells]

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleLabelProfileCell_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d))
    (i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)) :
    i ∈ minimalSupportPrivateShiftCycleLabelProfileCell
        g hg hh hno hmin a d p ↔
      minimalSupportPrivateShiftCycleLabelProfileAt
        g hg hh hno hmin a d i = p := by
  classical
  simp [minimalSupportPrivateShiftCycleLabelProfileCell]

omit [DecidableEq G] in
/-- Every active cell is nonempty. -/
theorem minimalSupportPrivateShiftCycleLabelProfileCell_nonempty
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d))
    (hp : p ∈ minimalSupportPrivateShiftCycleLabelProfileCells
      g hg hh hno hmin a d) :
    (minimalSupportPrivateShiftCycleLabelProfileCell
      g hg hh hno hmin a d p).Nonempty := by
  obtain ⟨i, hi⟩ :=
    (mem_minimalSupportPrivateShiftCycleLabelProfileCells_iff
      g hg hh hno hmin a d p).mp hp
  exact ⟨i,
    (mem_minimalSupportPrivateShiftCycleLabelProfileCell_iff
      g hg hh hno hmin a d p i).mpr hi⟩

omit [DecidableEq G] in
/-- A deterministic cell is contained in the full cycle fiber of its complete
profile. -/
theorem card_labelProfileCell_le_incomingAvoidingWitnessFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) :
    (minimalSupportPrivateShiftCycleLabelProfileCell
        g hg hh hno hmin a d p).card ≤
      (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card := by
  classical
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg hh hno hmin a d
  let C := minimalSupportPrivateShiftCycleLabelProfileCell
    g hg hh hno hmin a d p
  let F := minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
    g hno hmin a d p.2.val
  change C.card ≤ F.card
  refine Finset.card_le_card_of_injOn (s := C) (t := F)
    (fun i : ↥R ↦ i.val) ?_ ?_
  · intro i hi
    apply
      (mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff
        g hno hmin a d p.2.val i.val).mpr
    have hip :=
      (mem_minimalSupportPrivateShiftCycleLabelProfileCell_iff
        g hg hh hno hmin a d p i).mp hi
    have hsnd := congrArg (fun q ↦ q.2.val) hip
    simpa only [minimalSupportPrivateShiftCycleLabelProfileAt_snd_val] using
      hsnd
  · intro i hi j hj hij
    exact Subtype.ext hij

omit [DecidableEq G] in
/-- An active cell cardinality is paid by the source-zero padding power of its
complete profile fiber. -/
theorem card_labelProfileCell_le_pow_profileFiber_sub_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d))
    (hp : p ∈ minimalSupportPrivateShiftCycleLabelProfileCells
      g hg hh hno hmin a d) :
    (minimalSupportPrivateShiftCycleLabelProfileCell
        g hg hh hno hmin a d p).card ≤
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1) := by
  let C := minimalSupportPrivateShiftCycleLabelProfileCell
    g hg hh hno hmin a d p
  let F := minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
    g hno hmin a d p.2.val
  have hCF : C.card ≤ F.card := by
    simpa [C, F] using
      card_labelProfileCell_le_incomingAvoidingWitnessFiber
        g hg hh hno hmin a d p
  have hCpos : 0 < C.card := Finset.card_pos.mpr
    (minimalSupportPrivateShiftCycleLabelProfileCell_nonempty
      g hg hh hno hmin a d p hp)
  have hFpos : 0 < F.card := hCpos.trans_le hCF
  have hpow := add_one_le_two_pow (F.card - 1)
  have hpred : F.card - 1 + 1 = F.card := Nat.sub_add_cancel hFpos
  rw [hpred] at hpow
  exact hCF.trans hpow

omit [DecidableEq G] in
/-- The deterministic cells partition the retained cycle indices exactly. -/
theorem card_labelledLightProfileIndices_eq_sum_labelProfileCellCards
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card =
      (minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d).sum (fun p ↦
          (minimalSupportPrivateShiftCycleLabelProfileCell
            g hg hh hno hmin a d p).card) := by
  classical
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg hh hno hmin a d
  let labelProfile := minimalSupportPrivateShiftCycleLabelProfileAt
    g hg hh hno hmin a d
  calc
    R.card = R.attach.card := by simp
    _ = ∑ p ∈ R.attach.image labelProfile,
        (R.attach.filter fun i ↦ labelProfile i = p).card :=
      Finset.card_eq_sum_card_image labelProfile R.attach
    _ = (minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d).sum (fun p ↦
            (minimalSupportPrivateShiftCycleLabelProfileCell
              g hg hh hno hmin a d p).card) := by
      rfl

omit [DecidableEq G] in
/-- The profile of every active deterministic cell omits its cell label. -/
theorem active_labelProfileCell_omits
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d))
    (hp : p ∈ minimalSupportPrivateShiftCycleLabelProfileCells
      g hg hh hno hmin a d) :
    p.2.val p.1 = -1 := by
  obtain ⟨i, hi⟩ :=
    (mem_minimalSupportPrivateShiftCycleLabelProfileCells_iff
      g hg hh hno hmin a d p).mp hp
  have homit := minimalSupportPrivateShiftCycleLabelProfileAt_omits
    g hg hh hno hmin a d i
  rw [hi] at homit
  exact homit

/-- Squared raw padding weight also splits exactly into the two orientations
of each canonical collision. -/
theorem sum_reducedCollisionWeightSquare_eq_two_mul_canonical
    {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∑ r : ReducedSubsetSumCollision g h,
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) =
      2 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let R := noncanonicalReducedCollisions (g := g) hh
  let squareWeight : ReducedSubsetSumCollision g h → ℕ := fun r ↦
    reducedCollisionWeight (m := m) r *
      reducedCollisionWeight (m := m) r
  have hswap : ∀ r : ReducedSubsetSumCollision g h,
      squareWeight (reducedSubsetSumCollisionSwapEquiv hh r) =
        squareWeight r := by
    intro r
    simp only [squareWeight, reducedCollisionWeight_swap hh r]
  have hR : R.sum squareWeight = C.sum squareWeight := by
    dsimp [R, C]
    rw [← swappedCanonicalReducedCollisions_eq_noncanonical hh hh0]
    unfold swappedCanonicalReducedCollisions
    rw [Finset.sum_image
      (reducedSubsetSumCollisionSwapEquiv hh).injective.injOn]
    exact Finset.sum_congr rfl fun r _ ↦ hswap r
  change (Finset.univ : Finset (ReducedSubsetSumCollision g h)).sum
      squareWeight = 2 * C.sum squareWeight
  calc
    (Finset.univ : Finset (ReducedSubsetSumCollision g h)).sum
        squareWeight = C.sum squareWeight + R.sum squareWeight := by
      symm
      simpa [C, R, canonicalReducedCollisions,
        noncanonicalReducedCollisions] using
        Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (ReducedSubsetSumCollision g h))
          (IsCanonicalReducedCollision hh) squareWeight
    _ = 2 * C.sum squareWeight := by rw [hR, two_mul]

/-- The raw reduced collision underlying one active deterministic cell. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    (g : Fin (m + 1) → G) (_hg : ValidTuple g) {h : G}
    (_hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) : ReducedSubsetSumCollision g h :=
  incomingAvoidingLightProfileRawCollision g hno hmin a d p.2

/-- Active cells above one raw reduced collision. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) := by
  classical
  exact (minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d).filter fun p ↦
      minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
        g hg hh hno hmin a d p = q

omit [DecidableEq G] in
/-- Outside the three-omission frontier, one raw collision supports active
cycle cells under at most two deterministic labels. -/
theorem card_labelProfileCellRawCollisionFiber_le_two
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) :
    (minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
      g hg hh hno hmin a d q).card ≤ 2 := by
  classical
  let P := minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    g hno hmin a d
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d
  let F := minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
    g hg hh hno hmin a d q
  by_cases hF : F.Nonempty
  · obtain ⟨p0, hp0F⟩ := hF
    have hp0C := (Finset.mem_filter.mp hp0F).1
    have hp0Raw := (Finset.mem_filter.mp hp0F).2
    have hp0Raw' : raw p0 = q := by simpa [raw] using hp0Raw
    let cq := subsetCollisionCoeffs q.val.1 q.val.2
    let O := witnessOmissionCoordinates cq
    have hcq : cq = p0.2.val := by
      calc
        cq = subsetCollisionCoeffs (raw p0).val.1
            (raw p0).val.2 := by
          dsimp [cq]
          rw [hp0Raw']
        _ = p0.2.val := reducedCollisionOfTailLightWitness_coeffs g
          (incomingAvoidingLightProfile_isWitness
            g hno hmin a d p0.2)
          (incomingAvoidingLightProfile_tailLight
            g hno hmin a d p0.2)
    have hcqWitness : Witness g h cq := by
      rw [hcq]
      exact incomingAvoidingLightProfile_isWitness
        g hno hmin a d p0.2
    have hOcard : O.card ≤ 2 :=
      card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
        g hthree cq hcqWitness
    have hlabelInj : Set.InjOn
        (fun p : Fin (m + 1) × ↥P ↦ p.1) (↑F) := by
      intro p hp u hu hlabel
      apply Prod.ext hlabel
      apply incomingAvoidingLightProfileRawCollision_injective
        g hno hmin a d
      have hpRaw := (Finset.mem_filter.mp hp).2
      have huRaw := (Finset.mem_filter.mp hu).2
      exact hpRaw.trans huRaw.symm
    have hlabelsSubset : F.image
        (fun p : Fin (m + 1) × ↥P ↦ p.1) ⊆ O := by
      intro z hz
      obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hz
      have hpC := (Finset.mem_filter.mp hpF).1
      have hpRaw := (Finset.mem_filter.mp hpF).2
      have hpRaw' : raw p = q := by simpa [raw] using hpRaw
      apply (witnessOmissionCoordinates_exact cq p.1).1
      calc
        cq p.1 = subsetCollisionCoeffs (raw p).val.1
            (raw p).val.2 p.1 := by
          dsimp [cq]
          rw [hpRaw']
        _ = p.2.val p.1 := congrFun
          (reducedCollisionOfTailLightWitness_coeffs g
            (incomingAvoidingLightProfile_isWitness
              g hno hmin a d p.2)
            (incomingAvoidingLightProfile_tailLight
              g hno hmin a d p.2)) p.1
        _ = -1 := active_labelProfileCell_omits
          g hg hh hno hmin a d p hpC
    have himageCard : (F.image
        (fun p : Fin (m + 1) × ↥P ↦ p.1)).card = F.card :=
      Finset.card_image_of_injOn hlabelInj
    change F.card ≤ 2
    rw [← himageCard]
    exact (Finset.card_le_card hlabelsSubset).trans hOcard
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 2
    simp [hFempty]

/-- The complete diagonal contribution of active cycle cells is charged by
four times canonical diagonal mass.  This retains labels which carry only one
profile. -/
theorem sum_activeLabelProfileCellFiberPowerSquares_le_four_mul_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d).sum (fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1)) ≤
      4 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  classical
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d
  let fiberWeight : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  let squareWeight : ReducedSubsetSumCollision g h → ℕ := fun r ↦
    reducedCollisionWeight (m := m) r *
      reducedCollisionWeight (m := m) r
  let D := (canonicalReducedCollisions (g := g) hh).sum squareWeight
  have hprofileWeight : ∀ p ∈ C, fiberWeight p ≤
      reducedCollisionWeight (m := m) (raw p) := by
    intro p _hp
    have hpow :=
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle p.2.val
          (incomingAvoidingLightProfile_isWitness g hno hmin a d p.2)
          (incomingAvoidingLightProfile_tailLight g hno hmin a d p.2)
    calc
      fiberWeight p ≤ reducedCollisionWeight (m := m)
          (canonicalizeReducedCollision hh (raw p)) := by
        simpa only [fiberWeight, raw,
          minimalSupportPrivateShiftCycleLabelProfileCellRawCollision,
          canonicalCollisionOfTailLightWitness,
          incomingAvoidingLightProfileRawCollision] using hpow
      _ = reducedCollisionWeight (m := m) (raw p) :=
        canonicalizeReducedCollision_weight hh (raw p)
  have hmaps : ∀ p ∈ C,
      raw p ∈ (Finset.univ : Finset (ReducedSubsetSumCollision g h)) := by
    simp
  have hfiber : ∀ q ∈
      (Finset.univ : Finset (ReducedSubsetSumCollision g h)),
      (C.filter fun p ↦ raw p = q).card ≤ 2 := by
    intro q _hq
    simpa [C, raw,
      minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber] using
      card_labelProfileCellRawCollisionFiber_le_two
        g hg hh hthree hno hmin a d q
  have hmapBound : C.sum (fun p ↦ squareWeight (raw p)) ≤
      2 * (Finset.univ : Finset (ReducedSubsetSumCollision g h)).sum
        squareWeight :=
    sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
      C Finset.univ raw squareWeight hmaps 2 hfiber
  have hrawDiagonal :
      (Finset.univ : Finset (ReducedSubsetSumCollision g h)).sum
          squareWeight = 2 * D := by
    simpa [squareWeight, D] using
      sum_reducedCollisionWeightSquare_eq_two_mul_canonical
        (g := g) hh hh0
  change C.sum (fun p ↦ fiberWeight p * fiberWeight p) ≤ 4 * D
  calc
    C.sum (fun p ↦ fiberWeight p * fiberWeight p) ≤
        C.sum (fun p ↦ squareWeight (raw p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.mul_le_mul (hprofileWeight p hp) (hprofileWeight p hp)
    _ ≤ 2 * (Finset.univ : Finset
          (ReducedSubsetSumCollision g h)).sum squareWeight := hmapBound
    _ = 4 * D := by rw [hrawDiagonal]; ring

/-- Labels which actually occur among the retained deterministic cells. -/
noncomputable def minimalSupportPrivateShiftCycleActiveProfileLabels
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d).image Prod.fst

/-- Ordered pairs of distinct active cells with the same label. -/
noncomputable def minimalSupportPrivateShiftCycleSameLabelCellPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) := by
  classical
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  exact C.offDiag.filter fun p ↦ p.1.1 = p.2.1

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : (Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d)) ×
      (Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) :
    p ∈ minimalSupportPrivateShiftCycleSameLabelCellPairs
        g hg hh hno hmin a d ↔
      p.1 ∈ minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d ∧
        p.2 ∈ minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d ∧
        p.1 ≠ p.2 ∧ p.1.1 = p.2.1 := by
  classical
  simp [minimalSupportPrivateShiftCycleSameLabelCellPairs, and_assoc]

/-- Forget the repeated label in a same-label active cell pair. -/
noncomputable def minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles
    (g : Fin (m + 1) → G) (_hg : ValidTuple g) {h : G}
    (_hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : (Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d)) ×
      (Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) :
    Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d)) :=
  (p.1.1, (p.1.2, p.2.2))

/-- Ordered pairs of distinct active profiles carrying the same deterministic
cycle label. -/
noncomputable def minimalSupportPrivateShiftCycleActiveLabelProfilePairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    Finset (Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) := by
  classical
  let P := minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    g hno hmin a d
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  exact ((Finset.univ : Finset (Fin (m + 1))).product
    P.attach.offDiag).filter fun t ↦
      (t.1, t.2.1) ∈ C ∧ (t.1, t.2.2) ∈ C

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleActiveLabelProfilePairs_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (t : Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) :
    t ∈ minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d ↔
      t.2.1 ≠ t.2.2 ∧
        (t.1, t.2.1) ∈ minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d ∧
        (t.1, t.2.2) ∈ minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d := by
  classical
  simp [minimalSupportPrivateShiftCycleActiveLabelProfilePairs]

omit [DecidableEq G] in
/-- Same-label active cell pairs and active profile-pair incidences are the
same weighted family. -/
theorem sum_sameLabelCellPairCards_eq_activeLabelProfilePairCellCards
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    (minimalSupportPrivateShiftCycleSameLabelCellPairs
        g hg hh hno hmin a d).sum (fun p ↦
      (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d p.1).card *
        (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d p.2).card) =
      (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
      (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d (t.1, t.2.1)).card *
        (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d (t.1, t.2.2)).card) := by
  classical
  let toProfiles := minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles
    g hg hh hno hmin a d
  apply Finset.sum_bij (fun p _hp ↦ toProfiles p)
  · intro p hp
    have hp' :=
      (mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
        g hg hh hno hmin a d p).mp hp
    apply
      (mem_minimalSupportPrivateShiftCycleActiveLabelProfilePairs_iff
        g hg hh hno hmin a d (toProfiles p)).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro hprofile
      apply hp'.2.2.1
      exact Prod.ext hp'.2.2.2 hprofile
    · simpa [toProfiles,
        minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles] using hp'.1
    · have hp2 : (p.1.1, p.2.2) = p.2 :=
        Prod.ext hp'.2.2.2 rfl
      simpa [toProfiles,
        minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles, hp2] using
        hp'.2.1
  · intro p hp u hu hpu
    have hp' :=
      (mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
        g hg hh hno hmin a d p).mp hp
    have hu' :=
      (mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
        g hg hh hno hmin a d u).mp hu
    dsimp [toProfiles,
      minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles] at hpu
    have hlabel : p.1.1 = u.1.1 := congrArg (fun t ↦ t.1) hpu
    have hfirstProfile : p.1.2 = u.1.2 :=
      congrArg (fun t ↦ t.2.1) hpu
    have hsecondProfile : p.2.2 = u.2.2 :=
      congrArg (fun t ↦ t.2.2) hpu
    apply Prod.ext
    · exact Prod.ext hlabel hfirstProfile
    · exact Prod.ext
        (hp'.2.2.2.symm.trans (hlabel.trans hu'.2.2.2))
        hsecondProfile
  · intro t ht
    have ht' :=
      (mem_minimalSupportPrivateShiftCycleActiveLabelProfilePairs_iff
        g hg hh hno hmin a d t).mp ht
    let p := ((t.1, t.2.1), (t.1, t.2.2))
    refine ⟨p, ?_, ?_⟩
    · apply
        (mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
          g hg hh hno hmin a d p).mpr
      exact ⟨ht'.2.1, ht'.2.2, by
        intro hp
        apply ht'.1
        exact congrArg Prod.snd hp, rfl⟩
    · rfl
  · intro p hp
    have hp' :=
      (mem_minimalSupportPrivateShiftCycleSameLabelCellPairs_iff
        g hg hh hno hmin a d p).mp hp
    have hp2 : (p.1.1, p.2.2) = p.2 :=
      Prod.ext hp'.2.2.2 rfl
    simp [toProfiles,
      minimalSupportPrivateShiftCycleSameLabelCellPairToProfiles, hp2]

omit [DecidableEq G] in
/-- Every active deterministic profile label is one of the external cycle-edge
labels. -/
theorem activeProfileLabels_subset_privateShiftCycleEdgeLabels
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    minimalSupportPrivateShiftCycleActiveProfileLabels
        g hg hh hno hmin a d ⊆
      minimalSupportPrivateShiftCycleEdgeLabels
        g hg hh hno hmin a d := by
  intro z hz
  obtain ⟨p, hpC, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i, hi⟩ :=
    (mem_minimalSupportPrivateShiftCycleLabelProfileCells_iff
      g hg hh hno hmin a d p).mp hpC
  apply
    (mem_minimalSupportPrivateShiftCycleEdgeLabels_iff
      g hg hh hno hmin a d p.1).mpr
  refine ⟨(finRotate d).symm i.val, ?_⟩
  have hlabel := congrArg Prod.fst hi
  simpa [minimalSupportPrivateShiftCycleIncomingEdgeLabel] using hlabel

omit [DecidableEq G] in
/-- Active labels retain the ambient external-coordinate capacity bound. -/
theorem card_minimalSupport_add_activeProfileLabels_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    B.card + (minimalSupportPrivateShiftCycleActiveProfileLabels
      g hg hh hno hmin a d).card ≤ m + 1 := by
  have hsub := activeProfileLabels_subset_privateShiftCycleEdgeLabels
    g hg hh hno hmin a d
  have hcard := Finset.card_le_card hsub
  exact (Nat.add_le_add_left hcard B.card).trans
    (card_minimalSupport_add_privateShiftCycleEdgeLabels_le
      g hg hh hno hmin a d)

omit [DecidableEq G] in
/-- Every same-label active profile pair belongs to the global
common-omission incidence family. -/
theorem activeLabelProfilePairs_subset_commonOmissionPairIncidences
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d ⊆
      incomingAvoidingLightProfileCommonOmissionPairIncidences
        g hno hmin a d := by
  intro t ht
  have ht' :=
    (mem_minimalSupportPrivateShiftCycleActiveLabelProfilePairs_iff
      g hg hh hno hmin a d t).mp ht
  apply
    (mem_incomingAvoidingLightProfileCommonOmissionPairIncidences_iff
      g hno hmin a d t).mpr
  exact ⟨ht'.1,
    active_labelProfileCell_omits
      g hg hh hno hmin a d (t.1, t.2.1) ht'.2.1,
    active_labelProfileCell_omits
      g hg hh hno hmin a d (t.1, t.2.2) ht'.2.2⟩

/-- The active same-label off-diagonal inherits the one-budget global charge. -/
theorem sum_activeLabelProfilePairFiberPowers_le_cross_and_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.1.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.2.val).card - 1)) ≤
      16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      8 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  have hsubset :=
    activeLabelProfilePairs_subset_commonOmissionPairIncidences
      g hg hh hno hmin a d
  calc
    (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.1.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.2.val).card - 1)) ≤
      (incomingAvoidingLightProfileCommonOmissionPairIncidences
        g hno hmin a d).sum (fun t ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.1.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.2.val).card - 1)) :=
      Finset.sum_le_sum_of_subset hsubset
    _ ≤ 16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
          (fun p ↦ reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        8 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r) :=
      sum_commonOmissionProfilePairFiberPowers_le_cross_and_diagonal
        g hg hh hh0 hthree hno hmin a hcycle

/-- The complete active-cell quadratic budget: distinct profiles use the
global crossing charge, while diagonal/single-profile cells cost only four
additional copies of canonical diagonal mass. -/
theorem sum_activeLabelProfilePairFiberPowers_add_cellSquares_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.1.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.2.val).card - 1)) +
      (minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d).sum (fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1)) ≤
      16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  have hoff := sum_activeLabelProfilePairFiberPowers_le_cross_and_diagonal
    g hg hh hh0 hthree hno hmin a hcycle
  have hdiag :=
    sum_activeLabelProfileCellFiberPowerSquares_le_four_mul_diagonal
      g hg hh hh0 hthree hno hmin a hcycle
  omega

/-- The same quadratic budget expressed directly in deterministic cycle-cell
cardinalities. -/
theorem sum_activeLabelProfilePairCellCards_add_cellCardSquares_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
      (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d (t.1, t.2.1)).card *
        (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d (t.1, t.2.2)).card) +
      (minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d).sum (fun p ↦
      (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d p).card *
        (minimalSupportPrivateShiftCycleLabelProfileCell
          g hg hh hno hmin a d p).card) ≤
      16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  let J := minimalSupportPrivateShiftCycleActiveLabelProfilePairs
    g hg hh hno hmin a d
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let cellCard : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    (minimalSupportPrivateShiftCycleLabelProfileCell
      g hg hh hno hmin a d p).card
  let fiberWeight : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d) → ℕ := fun r ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r.val).card - 1)
  have hcell : ∀ p ∈ C, cellCard p ≤ fiberWeight p.2 := by
    intro p hp
    exact card_labelProfileCell_le_pow_profileFiber_sub_one
      g hg hh hno hmin a d p hp
  have hpairs : J.sum (fun t ↦
      cellCard (t.1, t.2.1) * cellCard (t.1, t.2.2)) ≤
      J.sum (fun t ↦ fiberWeight t.2.1 * fiberWeight t.2.2) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht' :=
      (mem_minimalSupportPrivateShiftCycleActiveLabelProfilePairs_iff
        g hg hh hno hmin a d t).mp ht
    exact Nat.mul_le_mul (hcell (t.1, t.2.1) ht'.2.1)
      (hcell (t.1, t.2.2) ht'.2.2)
  have hdiagonal : C.sum (fun p ↦ cellCard p * cellCard p) ≤
      C.sum (fun p ↦ fiberWeight p.2 * fiberWeight p.2) := by
    apply Finset.sum_le_sum
    intro p hp
    exact Nat.mul_le_mul (hcell p hp) (hcell p hp)
  have hbudget :=
    sum_activeLabelProfilePairFiberPowers_add_cellSquares_le
      g hg hh hh0 hthree hno hmin a hcycle
  change J.sum (fun t ↦
      cellCard (t.1, t.2.1) * cellCard (t.1, t.2.2)) +
    C.sum (fun p ↦ cellCard p * cellCard p) ≤ _
  have hleft :
      J.sum (fun t ↦
          cellCard (t.1, t.2.1) * cellCard (t.1, t.2.2)) +
        C.sum (fun p ↦ cellCard p * cellCard p) ≤
      J.sum (fun t ↦ fiberWeight t.2.1 * fiberWeight t.2.2) +
        C.sum (fun p ↦ fiberWeight p.2 * fiberWeight p.2) :=
    Nat.add_le_add hpairs hdiagonal
  exact hleft.trans (by simpa [J, C, fiberWeight] using hbudget)

omit [DecidableEq G] in
/-- The exact cell partition and Cauchy--Schwarz convert the retained index
count into the same-label cell quadratic, with the number of active labels as
the only multiplicative loss. -/
theorem square_card_labelledLightProfileIndices_le_activeLabels_mul_cellQuadratic
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card ^ 2 ≤
      (minimalSupportPrivateShiftCycleActiveProfileLabels
        g hg hh hno hmin a d).card *
      ((minimalSupportPrivateShiftCycleActiveLabelProfilePairs
          g hg hh hno hmin a d).sum (fun t ↦
        (minimalSupportPrivateShiftCycleLabelProfileCell
            g hg hh hno hmin a d (t.1, t.2.1)).card *
          (minimalSupportPrivateShiftCycleLabelProfileCell
            g hg hh hno hmin a d (t.1, t.2.2)).card) +
        (minimalSupportPrivateShiftCycleLabelProfileCells
          g hg hh hno hmin a d).sum (fun p ↦
        (minimalSupportPrivateShiftCycleLabelProfileCell
            g hg hh hno hmin a d p).card *
          (minimalSupportPrivateShiftCycleLabelProfileCell
            g hg hh hno hmin a d p).card)) := by
  classical
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg hh hno hmin a d
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let cellCard : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    (minimalSupportPrivateShiftCycleLabelProfileCell
      g hg hh hno hmin a d p).card
  have hpartition : R.card = C.sum cellCard := by
    simpa [R, C, cellCard] using
      card_labelledLightProfileIndices_eq_sum_labelProfileCellCards
        g hg hh hno hmin a d
  have hquadratic :=
    square_sum_le_activeLabels_mul_sameLabelQuadratic C cellCard
  have hpairs :=
    sum_sameLabelCellPairCards_eq_activeLabelProfilePairCellCards
      g hg hh hno hmin a d
  have hpairs' :
      (C.offDiag.filter fun p ↦ p.1.1 = p.2.1).sum (fun p ↦
        cellCard p.1 * cellCard p.2) =
      (minimalSupportPrivateShiftCycleActiveLabelProfilePairs
        g hg hh hno hmin a d).sum (fun t ↦
        cellCard (t.1, t.2.1) * cellCard (t.1, t.2.2)) := by
    simpa [C, cellCard,
      minimalSupportPrivateShiftCycleSameLabelCellPairs] using hpairs
  rw [hpairs'] at hquadratic
  rw [hpartition]
  simpa [C, cellCard,
    minimalSupportPrivateShiftCycleActiveProfileLabels] using hquadratic

/-- The full deterministic retained-index square is controlled by one global
crossing-plus-diagonal mass budget. -/
theorem square_card_labelledLightProfileIndices_le_activeLabels_mul_mass
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card ^ 2 ≤
      (minimalSupportPrivateShiftCycleActiveProfileLabels
        g hg hh hno hmin a d).card *
      (16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r)) := by
  have hquadratic :=
    square_card_labelledLightProfileIndices_le_activeLabels_mul_cellQuadratic
      g hg hh hno hmin a d
  have hbudget :=
    sum_activeLabelProfilePairCellCards_add_cellCardSquares_le
      g hg hh hh0 hthree hno hmin a hcycle
  exact hquadratic.trans (Nat.mul_le_mul_left _ hbudget)

/-- Active-label capacity removes the remaining label-count parameter. -/
theorem square_card_labelledLightProfileIndices_le_externalCapacity_mul_mass
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card ^ 2 ≤
      (m + 1 - B.card) *
      (16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r)) := by
  let L := minimalSupportPrivateShiftCycleActiveProfileLabels
    g hg hh hno hmin a d
  let mass :=
    16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r)
  have hactive :=
    square_card_labelledLightProfileIndices_le_activeLabels_mul_mass
      g hg hh hh0 hthree hno hmin a hcycle
  have hcapacity := card_minimalSupport_add_activeProfileLabels_le
    g hg hh hno hmin a d
  change B.card + L.card ≤ m + 1 at hcapacity
  have hL : L.card ≤ m + 1 - B.card := by
    omega
  change _ ≤ (m + 1 - B.card) * mass
  exact hactive.trans (Nat.mul_le_mul_right mass hL)

/-- If the deterministic family covers all but at most one cycle index, the
same one-budget estimate controls the square of `d-1`. -/
theorem square_cyclePred_le_externalCapacity_mul_mass_of_labelled_add_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hd : d ≤
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card + 1) :
    (d - 1) ^ 2 ≤ (m + 1 - B.card) *
      (16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r)) := by
  have hpred : d - 1 ≤
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card := by
    omega
  calc
    (d - 1) ^ 2 ≤
        (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
          g hg hh hno hmin a d).card ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hpred hpred
    _ ≤ (m + 1 - B.card) *
        (16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) +
          12 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
            reducedCollisionWeight (m := m) r *
              reducedCollisionWeight (m := m) r)) :=
      square_card_labelledLightProfileIndices_le_externalCapacity_mul_mass
        g hg hh hh0 hthree hno hmin a hcycle

/-- Critical operational form: outside the already exposed crossing and
structural frontiers, the least-period private shift cycle satisfies one
global external-capacity times crossing-plus-diagonal estimate. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_cyclePred_mass
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      (d - 1) ^ 2 ≤ (n + 1 - B.card) *
        (16 * criticalCanonicalCrossMass g +
          12 * criticalCanonicalDiagonalMass g) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hh : h + h = 0 := by
    simpa [h] using half_add_half hN
  have hh0 : h ≠ 0 := by
    simpa [h] using half_ne_zero hN hM
  by_cases hthree : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree))
  rcases
      critical_privateShiftCycle_cross_or_profiles_or_labelledLightProfileIndices_add_one
        hq g hg hno hmin a hcycle hB with
    hcross | htriangle | hthree' | hpure | hlabelled
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    have hmass :=
      square_cyclePred_le_externalCapacity_mul_mass_of_labelled_add_one
        g hg hh hh0 hthree hno hmin a hcycle hlabelled
    simpa [h, criticalCanonicalCrossMass,
      criticalCanonicalDiagonalMass, criticalCanonicalReducedCollisions,
      criticalCanonicalPositiveNegativeCrossPairs] using hmass

end MinModulus
