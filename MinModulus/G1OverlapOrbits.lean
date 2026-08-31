/-
# Orbit structure of the critical subset-sum overlap

Every point of the overlap between a valid anchored subset-sum cube and its
translate by `h` has a unique ordered presentation

`ssum g S = ssum g T + h`.

When `h` is a nonzero involution, swapping `S` and `T` is a fixed-point-free
involution on these presentations.  Thus the entire overlap, not just one
selected collision, decomposes into two-element half-translation orbits.  In
particular its cardinality is even, strengthening a strict lower bound past
an even threshold by a full two points.
-/
import MinModulus.G1CriticalRange

namespace MinModulus

open Finset

/-- A finite type equipped with a fixed-point-free involution has even
cardinality. -/
theorem even_fintype_card_of_fixedPointFree_involution
    {α : Type*} [Fintype α]
    (f : α → α) (hinv : Function.Involutive f) (hfix : ∀ x, f x ≠ x) :
    Even (Fintype.card α) := by
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α)
    (Fintype.equivFin α).injective
  let L : Finset α := Finset.univ.filter (fun x => x < f x)
  let R : Finset α := L.image f
  have hfinj : Function.Injective f := hinv.injective
  have hcardR : R.card = L.card := by
    exact Finset.card_image_of_injective L hfinj
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    obtain ⟨y, hyL, hyx⟩ := Finset.mem_image.mp hxR
    have hxlt : x < f x := (Finset.mem_filter.mp hxL).2
    have hylt : y < f y := (Finset.mem_filter.mp hyL).2
    have hfx : f x = y := by
      rw [← hyx, hinv y]
    have hxlt' : f y < y := hyx.trans_lt (hxlt.trans_eq hfx)
    exact (not_lt_of_ge (le_of_lt hylt)) hxlt'
  have hunion : L ∪ R = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_cases hlt : x < f x
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    · have hrev : f x < x := lt_of_le_of_ne (le_of_not_gt hlt) (hfix x)
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨f x, ?_, hinv x⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hinv x] using hrev⟩
  refine ⟨L.card, ?_⟩
  rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj, hcardR]

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Points in the intersection of the anchored subset-sum cube and its
translate by `h`. -/
def SubsetSumOverlap (g : Fin (m + 1) → G) (h : G) :=
  {x : G // x ∈ (subsetSumRange g) ∩ (subsetSumShiftRange g h)}

/-- Ordered pairs of subsets whose anchored sums differ by `h`. -/
def SubsetSumCollision (g : Fin (m + 1) → G) (h : G) :=
  {p : Finset (Fin m) × Finset (Fin m) //
    ssum g p.1 = ssum g p.2 + h}

noncomputable instance instFintypeSubsetSumCollision
    (g : Fin (m + 1) → G) (h : G) : Fintype (SubsetSumCollision g h) := by
  unfold SubsetSumCollision
  infer_instance

/-- Send an ordered collision `(S,T)` to its first subset sum. -/
def subsetSumCollisionToOverlap (g : Fin (m + 1) → G) (h : G) :
    SubsetSumCollision g h → SubsetSumOverlap g h := fun p =>
  ⟨ssum g p.val.1, by
    apply Finset.mem_inter.mpr
    constructor
    · rw [subsetSumRange]
      exact Finset.mem_image.mpr ⟨p.val.1, Finset.mem_univ _, rfl⟩
    · rw [subsetSumShiftRange]
      apply Finset.mem_image.mpr
      refine ⟨ssum g p.val.2, ?_, p.property.symm⟩
      rw [subsetSumRange]
      exact Finset.mem_image.mpr ⟨p.val.2, Finset.mem_univ _, rfl⟩⟩

/-- For a valid tuple, every overlap point has a unique ordered collision
presentation. -/
theorem subsetSumCollisionToOverlap_bijective
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    Function.Bijective (subsetSumCollisionToOverlap g h) := by
  have hinj := ssum_injective g hg
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply hinj
      have hv := congrArg Subtype.val hpq
      exact hv
    · apply hinj
      apply add_right_cancel (b := h)
      calc
        ssum g p.val.2 + h = ssum g p.val.1 := p.property.symm
        _ = ssum g q.val.1 := by
          exact congrArg Subtype.val hpq
        _ = ssum g q.val.2 + h := q.property
  · intro x
    have hxrange := (Finset.mem_inter.mp x.property).1
    have hxshift := (Finset.mem_inter.mp x.property).2
    change x.val ∈ subsetSumRange g at hxrange
    change x.val ∈ subsetSumShiftRange g h at hxshift
    change x.val ∈ Finset.univ.image (ssum g) at hxrange
    obtain ⟨S, _, hS⟩ := Finset.mem_image.mp hxrange
    change x.val ∈ (subsetSumRange g).image (fun z => z + h) at hxshift
    obtain ⟨y, hyrange, hy⟩ := Finset.mem_image.mp hxshift
    change y ∈ Finset.univ.image (ssum g) at hyrange
    obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hyrange
    have hrel : ssum g S = ssum g T + h := by
      calc
        ssum g S = x.val := hS
        _ = y + h := hy.symm
        _ = ssum g T + h := by rw [hT]
    refine ⟨⟨(S, T), hrel⟩, ?_⟩
    apply Subtype.ext
    exact hS

/-- The exact equivalence between ordered collisions and overlap points. -/
noncomputable def subsetSumCollisionEquivOverlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    SubsetSumCollision g h ≃ SubsetSumOverlap g h :=
  Equiv.ofBijective (subsetSumCollisionToOverlap g h)
    (subsetSumCollisionToOverlap_bijective g hg h)

omit [DecidableEq G] in
/-- Reversing a collision preserves its target when `h+h=0`. -/
lemma subsetSumCollision_reverse_value {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (p : SubsetSumCollision g h) :
    ssum g p.val.2 = ssum g p.val.1 + h := by
  calc
    ssum g p.val.2 = (ssum g p.val.2 + h) + h := by
      rw [add_assoc, hh, add_zero]
    _ = ssum g p.val.1 + h := by rw [← p.property]

/-- Swap the two subsets of every order-two collision. -/
def subsetSumCollisionSwapEquiv {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) : SubsetSumCollision g h ≃ SubsetSumCollision g h where
  toFun p := ⟨(p.val.2, p.val.1), subsetSumCollision_reverse_value hh p⟩
  invFun p := ⟨(p.val.2, p.val.1), subsetSumCollision_reverse_value hh p⟩
  left_inv p := by rfl
  right_inv p := by rfl

omit [DecidableEq G] in
/-- Swapping a collision has no fixed point when `h` is nonzero. -/
theorem subsetSumCollisionSwapEquiv_ne
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (p : SubsetSumCollision g h) : subsetSumCollisionSwapEquiv hh p ≠ p := by
  intro hp
  have hpairs := congrArg Subtype.val hp
  have hTS : p.val.2 = p.val.1 := congrArg Prod.fst hpairs
  apply hh0
  apply add_left_cancel (a := ssum g p.val.1)
  simpa [hTS] using p.property.symm

/-- Ordered collisions with a nonzero order-two target occur in pairs. -/
theorem even_card_subsetSumCollision
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0) :
    Even (Fintype.card (SubsetSumCollision g h)) := by
  refine even_fintype_card_of_fixedPointFree_involution
    (fun p => subsetSumCollisionSwapEquiv hh p) (fun _ => rfl) ?_
  exact subsetSumCollisionSwapEquiv_ne hh hh0

/-- Validity identifies the number of ordered subset collisions with the
cardinality of the translated-cube overlap. -/
theorem card_subsetSumCollision_eq_card_overlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    Fintype.card (SubsetSumCollision g h) =
      ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  letI : Fintype (SubsetSumOverlap g h) :=
    Fintype.ofEquiv (SubsetSumCollision g h)
      (subsetSumCollisionEquivOverlap g hg h)
  calc
    Fintype.card (SubsetSumCollision g h) =
        Fintype.card (SubsetSumOverlap g h) :=
      Fintype.card_congr (subsetSumCollisionEquivOverlap g hg h)
    _ = ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
      simp [SubsetSumOverlap]

/-- A valid cube's overlap with its translate by a nonzero involution has
even cardinality. -/
theorem even_card_subsetSumOverlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    Even ((subsetSumRange g ∩ subsetSumShiftRange g h).card) := by
  have he := even_card_subsetSumCollision (g := g) hh hh0
  rw [card_subsetSumCollision_eq_card_overlap g hg h] at he
  exact he

/-- If an even lower threshold is strictly exceeded by the overlap, its free
two-element orbits improve the integer bound by two rather than by one. -/
theorem add_two_le_card_subsetSumOverlap_of_even_lt
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) {K : ℕ} (hK : Even K)
    (hlt : K < ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card) :
    K + 2 ≤ ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  have hover := even_card_subsetSumOverlap g hg hh hh0
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hover
  omega

end MinModulus
