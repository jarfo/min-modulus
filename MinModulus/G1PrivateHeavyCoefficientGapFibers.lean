/-
# Directed coefficient-gap fibers of selected private owners

For any selected private-owner family, label every ordered distinct pair by a
coordinate where the target witness exceeds the source witness by at least
two.  Privacy says the label is either the target owner or lies outside the
deletion set.

Target-owner labels certify that the target witness is coefficient-heavy at
its owner.  External labels consume ambient coordinates or have a large pair
fiber.  This turns the joint-fiber pair expansion into an exact quantitative
interface.
-/
import MinModulus.G1PrivateHeavyJointFiberAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Ordered distinct pairs from an arbitrary selected private-owner set. -/
def MinimalSupportSelectedDistinctOrderedPair
    {B : Finset (Fin m)} (S : Finset ↥B) :=
  {p : ↥S × ↥S // p.1 ≠ p.2}

noncomputable instance instFintypeMinimalSupportSelectedDistinctOrderedPair
    {B : Finset (Fin m)} (S : Finset ↥B) :
    Fintype (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  unfold MinimalSupportSelectedDistinctOrderedPair
  infer_instance

/-- Exact number of ordered distinct selected pairs. -/
theorem card_minimalSupportSelectedDistinctOrderedPair
    {B : Finset (Fin m)} (S : Finset ↥B) :
    Fintype.card (MinimalSupportSelectedDistinctOrderedPair S) =
      S.card * (S.card - 1) := by
  classical
  unfold MinimalSupportSelectedDistinctOrderedPair
  rw [Fintype.card_subtype]
  change #(Finset.univ.filter (fun p : ↥S × ↥S ↦ p.1 ≠ p.2)) =
    S.card * (S.card - 1)
  let D : Finset (↥S × ↥S) :=
    Finset.univ.image (fun b : ↥S ↦ (b, b))
  have hfilter :
      Finset.univ.filter (fun p : ↥S × ↥S ↦ p.1 ≠ p.2) =
        Finset.univ \ D := by
    ext p
    simp [D, Prod.ext_iff]
  have hDcard : D.card = S.card := by
    have hinj : Function.Injective (fun b : ↥S ↦ (b, b)) := by
      intro a b hab
      exact congrArg Prod.fst hab
    calc
      D.card = (Finset.univ : Finset ↥S).card :=
        Finset.card_image_of_injective Finset.univ hinj
      _ = S.card := by simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ D), hDcard]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- Choose a directed coefficient-gap label for every selected ordered pair. -/
noncomputable def minimalSupportSelectedPrivateCoefficientGapCoordinate
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (p : MinimalSupportSelectedDistinctOrderedPair S) : Fin m :=
  Classical.choose
    (exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
      g hg h hmin p.val.1.val p.val.2.val (by
        intro howners
        exact p.property (Subtype.ext howners)))

theorem minimalSupportSelectedPrivateCoefficientGapCoordinate_spec
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (p : MinimalSupportSelectedDistinctOrderedPair S) :
    minimalSupportPrivateWitness g h hmin p.val.1.val
          (minimalSupportSelectedPrivateCoefficientGapCoordinate
            g hg h hmin S p) + 2 ≤
        minimalSupportPrivateWitness g h hmin p.val.2.val
          (minimalSupportSelectedPrivateCoefficientGapCoordinate
            g hg h hmin S p) ∧
      (minimalSupportSelectedPrivateCoefficientGapCoordinate
            g hg h hmin S p = p.val.2.val ∨
        minimalSupportSelectedPrivateCoefficientGapCoordinate
            g hg h hmin S p ∉ B) :=
  Classical.choose_spec
    (exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
      g hg h hmin p.val.1.val p.val.2.val (by
        intro howners
        exact p.property (Subtype.ext howners)))

/-- Pairs whose selected gap is the target owner. -/
noncomputable def minimalSupportSelectedPrivateTargetGapPairs
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact Finset.univ.filter (fun p ↦
    minimalSupportSelectedPrivateCoefficientGapCoordinate
      g hg h hmin S p = p.val.2.val)

/-- Pairs whose selected gap is external to `B`. -/
noncomputable def minimalSupportSelectedPrivateExternalGapPairs
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact Finset.univ.filter (fun p ↦
    minimalSupportSelectedPrivateCoefficientGapCoordinate
      g hg h hmin S p ∉ B)

/-- Target and external gap pairs partition all ordered distinct pairs. -/
theorem card_minimalSupportSelectedPrivateTargetGap_add_externalGapPairs
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    (minimalSupportSelectedPrivateTargetGapPairs
      g hg h hmin S).card +
    (minimalSupportSelectedPrivateExternalGapPairs
      g hg h hmin S).card = S.card * (S.card - 1) := by
  classical
  let T := minimalSupportSelectedPrivateTargetGapPairs g hg h hmin S
  let E := minimalSupportSelectedPrivateExternalGapPairs g hg h hmin S
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro p hpT hpE
    have hpT' := Finset.mem_filter.mp hpT
    have hpE' := Finset.mem_filter.mp hpE
    apply hpE'.2
    rw [hpT'.2]
    exact p.val.2.val.property
  have hunion : T ∪ E = Finset.univ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases (minimalSupportSelectedPrivateCoefficientGapCoordinate_spec
      g hg h hmin S p).2 with htarget | hexternal
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htarget⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexternal⟩)
  change T.card + E.card = S.card * (S.card - 1)
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp [card_minimalSupportSelectedDistinctOrderedPair]

/-- Selected owners whose private witness has coefficient at least two at
the owner itself. -/
noncomputable def minimalSupportSelectedPrivateOwnerHeavyVertices
    (g : Fin m → G) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) : Finset ↥S := by
  classical
  exact Finset.univ.filter (fun b ↦
    2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val)

/-- A target-owner gap certifies that its target is owner-heavy. -/
theorem minimalSupportSelectedPrivateTargetGap_target_ownerHeavy
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    {p : MinimalSupportSelectedDistinctOrderedPair S}
    (hp : p ∈ minimalSupportSelectedPrivateTargetGapPairs
      g hg h hmin S) :
    p.val.2 ∈ minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S := by
  classical
  have htarget := (Finset.mem_filter.mp hp).2
  have hgap :=
    (minimalSupportSelectedPrivateCoefficientGapCoordinate_spec
      g hg h hmin S p).1
  rw [htarget] at hgap
  have howners : (p.val.1.val : Fin m) ≠ (p.val.2.val : Fin m) := by
    intro hval
    apply p.property
    apply Subtype.ext
    exact Subtype.ext hval
  have hsourceZero := minimalSupportPrivateWitness_eq_zero_of_ne
    g h hmin p.val.1.val p.val.2.val.property (Ne.symm howners)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

/-- Target-gap pairs inject into owner-heavy targets times arbitrary selected
sources, giving an exact multiplicity bound. -/
theorem card_minimalSupportSelectedPrivateTargetGapPairs_le_ownerHeavy_mul_card
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    (minimalSupportSelectedPrivateTargetGapPairs
        g hg h hmin S).card ≤
      (minimalSupportSelectedPrivateOwnerHeavyVertices
        g h hmin S).card * S.card := by
  classical
  let T := minimalSupportSelectedPrivateTargetGapPairs g hg h hmin S
  let O := minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S
  let enc : ↥T → ↥O × ↥S := fun p ↦
    (⟨p.val.val.2,
      minimalSupportSelectedPrivateTargetGap_target_ownerHeavy
        g hg h hmin S p.property⟩, p.val.val.1)
  have henc : Function.Injective enc := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Prod.snd hpq
    · exact congrArg Subtype.val (congrArg Prod.fst hpq)
  have hcard := Fintype.card_le_of_injective enc henc
  change T.card ≤ O.card * S.card
  calc
    T.card = Fintype.card ↥T := (Fintype.card_coe T).symm
    _ ≤ Fintype.card (↥O × ↥S) := hcard
    _ = O.card * S.card := by simp

/-- External gap coordinates used by selected ordered pairs. -/
noncomputable def minimalSupportSelectedPrivateExternalGapLabels
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) : Finset (Fin m) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapPairs
    g hg h hmin S).image
      (minimalSupportSelectedPrivateCoefficientGapCoordinate
        g hg h hmin S)

/-- External selected pairs with one fixed coefficient-gap label. -/
noncomputable def minimalSupportSelectedPrivateExternalGapFiber
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapPairs
    g hg h hmin S).filter (fun p ↦
      minimalSupportSelectedPrivateCoefficientGapCoordinate
        g hg h hmin S p = z)

/-- External gap labels lie outside `B`. -/
theorem minimalSupportSelectedPrivateExternalGapLabels_disjoint
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    Disjoint (minimalSupportSelectedPrivateExternalGapLabels
      g hg h hmin S) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp hp).2 hzB

/-- Exact image/fiber dichotomy for external coefficient gaps. -/
theorem minimalSupportSelectedPrivateExternalGap_labelImage_or_largeFiber
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportSelectedPrivateExternalGapPairs
        g hg h hmin S).card) :
    L ≤ (minimalSupportSelectedPrivateExternalGapLabels
      g hg h hmin S).card ∨
      ∃ z ∈ minimalSupportSelectedPrivateExternalGapLabels
          g hg h hmin S,
        r < (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S z).card := by
  classical
  let E := minimalSupportSelectedPrivateExternalGapPairs g hg h hmin S
  let label : MinimalSupportSelectedDistinctOrderedPair S → Fin m :=
    minimalSupportSelectedPrivateCoefficientGapCoordinate g hg h hmin S
  let labels := minimalSupportSelectedPrivateExternalGapLabels
    g hg h hmin S
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < E.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ p ∈ E, label p ∈ labels := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨z, hz, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨z, hz, ?_⟩
    simpa [label, E, minimalSupportSelectedPrivateExternalGapFiber]
      using hfiber

/-- Target-owner heaviness, ambient external-label capacity, or a large
external directed-gap fiber. -/
theorem minimalSupportSelectedPrivate_ownerHeavy_or_capacity_or_largeExternalGapFiber
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (K L r : ℕ)
    (hcount : K * S.card + L * r < S.card * (S.card - 1)) :
    K < (minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S).card ∨
      B.card + L ≤ m ∨
      ∃ z : Fin m, z ∉ B ∧
        r < (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S z).card := by
  have hpartition :=
    card_minimalSupportSelectedPrivateTargetGap_add_externalGapPairs
      g hg h hmin S
  have htargetBound :=
    card_minimalSupportSelectedPrivateTargetGapPairs_le_ownerHeavy_mul_card
      g hg h hmin S
  by_cases htarget : K * S.card <
      (minimalSupportSelectedPrivateTargetGapPairs g hg h hmin S).card
  · left
    have hSpos : 0 < S.card := by
      by_contra hzero
      have hScard : S.card = 0 := Nat.eq_zero_of_not_pos hzero
      simp [hScard] at hcount
    have hmul : S.card * K < S.card *
        (minimalSupportSelectedPrivateOwnerHeavyVertices
          g h hmin S).card := by
      simpa [Nat.mul_comm] using htarget.trans_le htargetBound
    exact (Nat.mul_lt_mul_left hSpos).mp hmul
  · right
    have htargetLe :
        (minimalSupportSelectedPrivateTargetGapPairs
          g hg h hmin S).card ≤ K * S.card :=
      Nat.le_of_not_gt htarget
    have hExternalCount : L * r <
        (minimalSupportSelectedPrivateExternalGapPairs
          g hg h hmin S).card := by
      omega
    rcases minimalSupportSelectedPrivateExternalGap_labelImage_or_largeFiber
        g hg h hmin S L r hExternalCount with hlabels | hfiber
    · left
      have hdisj := minimalSupportSelectedPrivateExternalGapLabels_disjoint
        g hg h hmin S
      have hcap : B.card +
          (minimalSupportSelectedPrivateExternalGapLabels
            g hg h hmin S).card ≤ m := by
        rw [← Finset.card_union_of_disjoint hdisj.symm]
        simpa using Finset.card_le_univ
          (B ∪ minimalSupportSelectedPrivateExternalGapLabels
            g hg h hmin S)
      omega
    · right
      obtain ⟨z, hzLabel, hzFiber⟩ := hfiber
      have hzExternal : z ∉ B := by
        have hdisj := minimalSupportSelectedPrivateExternalGapLabels_disjoint
          g hg h hmin S
        exact Finset.disjoint_left.mp hdisj hzLabel
      exact ⟨z, hzExternal, hzFiber⟩

/-- Owners underlying one joint external heavy/escape fiber. -/
noncomputable def minimalSupportPrivateJointExternalHeavyEscapeOwners
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) : Finset ↥B := by
  classical
  exact (minimalSupportPrivateJointExternalHeavyEscapeFiber
    g hg h t q ht hq hmin hqzero z e).image Subtype.val

/-- Passing from a joint fiber to its private owners loses no cardinality. -/
theorem card_minimalSupportPrivateJointExternalHeavyEscapeOwners
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) :
    (minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e).card =
    (minimalSupportPrivateJointExternalHeavyEscapeFiber
      g hg h t q ht hq hmin hqzero z e).card := by
  classical
  rw [minimalSupportPrivateJointExternalHeavyEscapeOwners,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- Directed-gap count specialized to the owner set of a joint external
heavy/escape fiber. -/
theorem minimalSupportPrivateJointFiber_ownerHeavy_or_capacity_or_largeExternalGapFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) (K L r : ℕ)
    (hcount : let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      K * S.card + L * r < S.card * (S.card - 1)) :
    let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)
    K < (minimalSupportSelectedPrivateOwnerHeavyVertices
        g h hmin S).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ w : Fin (m + 1), w ∉ B ∧
        r < (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S w).card := by
  let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
    g hg h t q ht hq hmin hqzero z e
  exact minimalSupportSelectedPrivate_ownerHeavy_or_capacity_or_largeExternalGapFiber
    g hg h hmin S K L r hcount

end MinModulus
