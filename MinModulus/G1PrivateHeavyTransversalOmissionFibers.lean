/-
# Fibers of external common-omission labels

Every ordered pair of distinct minimal-transversal vertices has an external
coordinate omitted by both canonical private witnesses.  Choose one such
coordinate.  This turns the complete directed graph on the deletion set into
a finite labelled graph and exposes the exact pigeonhole dichotomy needed
next: many distinct external labels, or one label carried by many pairs.
-/
import MinModulus.G1PrivateHeavyTransversalCommonOmission

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Ordered pairs of distinct vertices of a finite deletion set. -/
def MinimalSupportDistinctOrderedPair (B : Finset (Fin m)) :=
  {p : (↥B × ↥B) // p.1 ≠ p.2}

noncomputable instance instFintypeMinimalSupportDistinctOrderedPair
    (B : Finset (Fin m)) : Fintype (MinimalSupportDistinctOrderedPair B) := by
  classical
  unfold MinimalSupportDistinctOrderedPair
  infer_instance

/-- There are exactly `|B|(|B|-1)` ordered distinct pairs. -/
theorem card_minimalSupportDistinctOrderedPair
    (B : Finset (Fin m)) :
    Fintype.card (MinimalSupportDistinctOrderedPair B) =
      B.card * (B.card - 1) := by
  classical
  unfold MinimalSupportDistinctOrderedPair
  rw [Fintype.card_subtype]
  change #(Finset.univ.filter (fun p : ↥B × ↥B ↦ p.1 ≠ p.2)) =
    B.card * (B.card - 1)
  let D : Finset (↥B × ↥B) :=
    Finset.univ.image (fun b : ↥B ↦ (b, b))
  have hfilter :
      Finset.univ.filter (fun p : ↥B × ↥B ↦ p.1 ≠ p.2) =
        Finset.univ \ D := by
    ext p
    simp [D, Prod.ext_iff]
  have hDcard : D.card = B.card := by
    have hinj : Function.Injective (fun b : ↥B ↦ (b, b)) := by
      intro a b hab
      exact congrArg Prod.fst hab
    calc
      D.card = (Finset.univ : Finset ↥B).card :=
        Finset.card_image_of_injective Finset.univ hinj
      _ = B.card := by simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ D), hDcard]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- Select one external common omission for each ordered distinct private
witness pair. -/
noncomputable def minimalSupportPrivateCommonOmissionLabel
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (p : MinimalSupportDistinctOrderedPair B) : Fin m :=
  Classical.choose
    (exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
      g hg hh hmin p.val.1 p.val.2 p.property)

theorem minimalSupportPrivateCommonOmissionLabel_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (p : MinimalSupportDistinctOrderedPair B) :
    minimalSupportPrivateCommonOmissionLabel g hg hh hmin p ∉ B ∧
      minimalSupportPrivateWitness g h hmin p.val.1
          (minimalSupportPrivateCommonOmissionLabel g hg hh hmin p) = -1 ∧
      minimalSupportPrivateWitness g h hmin p.val.2
          (minimalSupportPrivateCommonOmissionLabel g hg hh hmin p) = -1 :=
  Classical.choose_spec
    (exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
      g hg hh hmin p.val.1 p.val.2 p.property)

/-- External coordinates actually used as chosen pair labels. -/
noncomputable def minimalSupportPrivateCommonOmissionLabels
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset (Fin m) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateCommonOmissionLabel g hg hh hmin)

@[simp] theorem mem_minimalSupportPrivateCommonOmissionLabels_iff
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) (z : Fin m) :
    z ∈ minimalSupportPrivateCommonOmissionLabels g hg hh hmin ↔
      ∃ p : MinimalSupportDistinctOrderedPair B,
        minimalSupportPrivateCommonOmissionLabel g hg hh hmin p = z := by
  classical
  simp [minimalSupportPrivateCommonOmissionLabels]

/-- Every selected label is external to the minimal transversal. -/
theorem minimalSupportPrivateCommonOmissionLabels_disjoint
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Disjoint
      (minimalSupportPrivateCommonOmissionLabels g hg hh hmin) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨p, rfl⟩ :=
    (mem_minimalSupportPrivateCommonOmissionLabels_iff
      g hg hh hmin z).mp hz
  exact (minimalSupportPrivateCommonOmissionLabel_spec
    g hg hh hmin p).1 hzB

/-- Ordered pairs whose selected external common omission is `z`. -/
noncomputable def minimalSupportPrivateCommonOmissionFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin m) : Finset (MinimalSupportDistinctOrderedPair B) := by
  classical
  exact Finset.univ.filter (fun p ↦
    minimalSupportPrivateCommonOmissionLabel g hg hh hmin p = z)

@[simp] theorem mem_minimalSupportPrivateCommonOmissionFiber_iff
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin m) (p : MinimalSupportDistinctOrderedPair B) :
    p ∈ minimalSupportPrivateCommonOmissionFiber g hg hh hmin z ↔
      minimalSupportPrivateCommonOmissionLabel g hg hh hmin p = z := by
  classical
  simp [minimalSupportPrivateCommonOmissionFiber]

/-- Every member of a label fiber is a pair of private witnesses both
omitting that label. -/
theorem minimalSupportPrivateCommonOmissionFiber_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {z : Fin m} {p : MinimalSupportDistinctOrderedPair B}
    (hp : p ∈ minimalSupportPrivateCommonOmissionFiber g hg hh hmin z) :
    z ∉ B ∧
      minimalSupportPrivateWitness g h hmin p.val.1 z = -1 ∧
      minimalSupportPrivateWitness g h hmin p.val.2 z = -1 := by
  have hpLabel :=
    (mem_minimalSupportPrivateCommonOmissionFiber_iff
      g hg hh hmin z p).mp hp
  rw [← hpLabel]
  exact minimalSupportPrivateCommonOmissionLabel_spec g hg hh hmin p

/-- Exact label-fiber dichotomy.  If `L*r` is smaller than the total number
of ordered distinct pairs, then either at least `L` external labels occur or
one external label is carried by more than `r` pairs. -/
theorem minimalSupportPrivateCommonOmission_labelImage_or_largeFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (L r : ℕ) (hcount : L * r < B.card * (B.card - 1)) :
    L ≤ (minimalSupportPrivateCommonOmissionLabels g hg hh hmin).card ∨
      ∃ z ∈ minimalSupportPrivateCommonOmissionLabels g hg hh hmin,
        r < (minimalSupportPrivateCommonOmissionFiber
          g hg hh hmin z).card := by
  classical
  let P := MinimalSupportDistinctOrderedPair B
  let label : P → Fin m :=
    minimalSupportPrivateCommonOmissionLabel g hg hh hmin
  let labels := minimalSupportPrivateCommonOmissionLabels g hg hh hmin
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < (Finset.univ : Finset P).card := by
      rw [Finset.card_univ, card_minimalSupportDistinctOrderedPair]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ p ∈ (Finset.univ : Finset P), label p ∈ labels := by
      intro p _hp
      simp [label, labels, minimalSupportPrivateCommonOmissionLabels]
    obtain ⟨z, hz, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨z, hz, ?_⟩
    simpa [label, minimalSupportPrivateCommonOmissionFiber] using hfiber

end MinModulus
