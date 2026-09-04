/-
# Short-profile concentration in the primitive three-residue terminal

One retained profile is substantially shorter than the coarse interval used
by the first fiber-capacity bound.  In the window `{-1,0,1}` it is `K`; in
the window `{-2,-1,0}` it is `L`.  In either case every row contributes only
`-1`, `0`, or `1`, so the total profile interval has length equal to the
number of nonzero contributors, not twice the whole transversal size.

Critical sixth-stratum capacity therefore forces at least 32 nonzero short-
profile rows.  Since a nonzero short coefficient is either `-1` or `1`, one
fixed coefficient occurs on at least 16 owners.  This is the first constant-
size structured family extracted from every large-transversal survivor.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveFiberCapacity

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The coordinates on which a signed unit profile is nonzero. -/
def shortProfileSupport {B : Finset (Fin n)} (s : ↥B → ℤ) : Finset ↥B :=
  Finset.univ.filter (fun b ↦ s b ≠ 0)

/-- A two-spaced integer set in an interval of arbitrary natural length `D`
has at most `D / 2 + 1` elements. -/
theorem card_le_div_two_add_one_of_mem_interval_of_pairwise_gap_two
    (S : Finset ℤ) (lo : ℤ) (D : ℕ)
    (hbound : ∀ a ∈ S, lo ≤ a ∧ a ≤ lo + D)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a + 2 ≤ b ∨ b + 2 ≤ a) :
    S.card ≤ D / 2 + 1 := by
  classical
  let compress : ℤ → ℤ := fun a ↦ (a - lo) / 2
  let target : Finset ℤ := Finset.Icc 0 (D / 2 : ℕ)
  have hcompressMem : ∀ a ∈ S, compress a ∈ target := by
    intro a ha
    have hab := hbound a ha
    simp only [target, Finset.mem_Icc]
    dsimp only [compress]
    omega
  have hcompressInj : Set.InjOn compress S := by
    intro a ha b hb hab
    by_contra hne
    have hsep := hgap a ha b hb hne
    dsimp only [compress] at hab
    omega
  have hcardImage : (S.image compress).card = S.card :=
    Finset.card_image_of_injOn hcompressInj
  have hsubset : S.image compress ⊆ target := by
    intro a ha
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp ha
    exact hcompressMem b hbS
  calc
    S.card = (S.image compress).card := hcardImage.symm
    _ ≤ target.card := Finset.card_le_card hsubset
    _ = D / 2 + 1 := by
      simp only [target, Int.card_Icc, sub_zero]
      omega

/-- Exact signed-unit decomposition: the sum of a short profile over a
subset is its number of `+1` rows minus its number of `-1` rows. -/
theorem sum_shortProfile_eq_pos_card_sub_neg_card
    {B : Finset (Fin n)} (s : ↥B → ℤ)
    (hs : ∀ b : ↥B, s b ∈ ({-1, 0, 1} : Finset ℤ))
    (A : Finset ↥B) :
    (∑ b ∈ A, s b) =
      ((A.filter (fun b ↦ s b = 1)).card : ℤ) -
        ((A.filter (fun b ↦ s b = -1)).card : ℤ) := by
  classical
  have hpoint : ∀ b : ↥B,
      s b = (if s b = 1 then 1 else 0) -
        (if s b = -1 then 1 else 0) := by
    intro b
    have hb := hs b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hneg | hzero | hpos <;> omega
  calc
    (∑ b ∈ A, s b) =
        ∑ b ∈ A, ((if s b = 1 then 1 else 0) -
          (if s b = -1 then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro b _hb
            exact hpoint b
    _ = ((A.filter (fun b ↦ s b = 1)).card : ℤ) -
          ((A.filter (fun b ↦ s b = -1)).card : ℤ) := by
            simp only [Finset.sum_sub_distrib]
            simp

/-- The positive and negative rows partition the support of a signed unit
profile. -/
theorem card_pos_add_card_neg_eq_shortProfileSupport
    {B : Finset (Fin n)} (s : ↥B → ℤ)
    (hs : ∀ b : ↥B, s b ∈ ({-1, 0, 1} : Finset ℤ)) :
    (Finset.univ.filter (fun b ↦ s b = 1)).card +
        (Finset.univ.filter (fun b ↦ s b = -1)).card =
      (shortProfileSupport s).card := by
  classical
  let P : Finset ↥B := Finset.univ.filter (fun b ↦ s b = 1)
  let M : Finset ↥B := Finset.univ.filter (fun b ↦ s b = -1)
  have hdisjoint : Disjoint P M := by
    refine Finset.disjoint_left.mpr ?_
    intro b hbP hbM
    have hp : s b = 1 := (Finset.mem_filter.mp hbP).2
    have hm : s b = -1 := (Finset.mem_filter.mp hbM).2
    omega
  have hunion : P ∪ M = shortProfileSupport s := by
    ext b
    have hb := hs b
    simp only [P, M, shortProfileSupport, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hneg | hzero | hpos <;> omega
  rw [← hunion, Finset.card_union_of_disjoint hdisjoint]

/-- Every fiber whose collision profiles are two-spaced is bounded by half
the support size of a signed unit profile, plus one. -/
theorem card_shortProfile_fiber_le_div_two_add_one
    {α : Type*} [DecidableEq α]
    {B : Finset (Fin n)} (s : ↥B → ℤ)
    (hs : ∀ b : ↥B, s b ∈ ({-1, 0, 1} : Finset ℤ))
    (value : Finset ↥B → α)
    (hcross : ∀ A C : Finset ↥B, A ≠ C → value A = value C →
      (∑ b ∈ A, s b) - (∑ b ∈ C, s b) ≤ -2 ∨
        2 ≤ (∑ b ∈ A, s b) - (∑ b ∈ C, s b))
    (target : α) :
    ((Finset.univ : Finset (Finset ↥B)).filter
      (fun A ↦ value A = target)).card ≤
        (shortProfileSupport s).card / 2 + 1 := by
  classical
  let F : Finset (Finset ↥B) :=
    Finset.univ.filter (fun A ↦ value A = target)
  let profile : Finset ↥B → ℤ := fun A ↦ ∑ b ∈ A, s b
  let S : Finset ℤ := F.image profile
  let P : Finset ↥B := Finset.univ.filter (fun b ↦ s b = 1)
  let M : Finset ↥B := Finset.univ.filter (fun b ↦ s b = -1)
  have hprofileInj : Set.InjOn profile F := by
    intro A hAF C hCF hprofileEq
    by_contra hAC
    have hvalueA : value A = target := (Finset.mem_filter.mp hAF).2
    have hvalueC : value C = target := (Finset.mem_filter.mp hCF).2
    have hsep := hcross A C hAC (hvalueA.trans hvalueC.symm)
    dsimp only [profile] at hprofileEq
    omega
  have hcardS : S.card = F.card :=
    Finset.card_image_of_injOn hprofileInj
  have hgap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      a + 2 ≤ b ∨ b + 2 ≤ a := by
    intro a ha b hb hab
    obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨C, hCF, rfl⟩ := Finset.mem_image.mp hb
    have hAC : A ≠ C := by
      intro h
      subst C
      exact hab rfl
    have hvalueA : value A = target := (Finset.mem_filter.mp hAF).2
    have hvalueC : value C = target := (Finset.mem_filter.mp hCF).2
    have hsep := hcross A C hAC (hvalueA.trans hvalueC.symm)
    dsimp only [profile]
    omega
  have hbound : ∀ a ∈ S,
      -(M.card : ℤ) ≤ a ∧
        a ≤ -(M.card : ℤ) + (shortProfileSupport s).card := by
    intro a ha
    obtain ⟨A, _hAF, rfl⟩ := Finset.mem_image.mp ha
    have hformula := sum_shortProfile_eq_pos_card_sub_neg_card s hs A
    have hposSubset : A.filter (fun b ↦ s b = 1) ⊆ P := by
      intro b hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    have hnegSubset : A.filter (fun b ↦ s b = -1) ⊆ M := by
      intro b hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    have hpos := Finset.card_le_card hposSubset
    have hneg := Finset.card_le_card hnegSubset
    have hwidth := card_pos_add_card_neg_eq_shortProfileSupport s hs
    dsimp only [profile]
    dsimp only [P, M] at hpos hneg ⊢
    omega
  have hcard :=
    card_le_div_two_add_one_of_mem_interval_of_pairwise_gap_two
      S (-(M.card : ℤ)) (shortProfileSupport s).card hbound hgap
  simpa only [S, F, hcardS] using hcard

/-- The primitive state after choosing the genuinely shorter retained
profile.  The final conjunct is the critical concentration forced by
capacity. -/
def PrimitiveLargeShortProfileRows
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ x z : Fin n, ∃ k short : ↥B → ℤ,
    x ∉ B ∧ z ∉ B ∧ x ≠ z ∧
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)) =
          64 ∧
      (∀ b : ↥B, k b ∈ ({-2, -1, 0, 1} : Finset ℤ)) ∧
      (((∀ b : ↥B, k b ≠ -2) ∧ ∀ b : ↥B, short b = k b) ∨
        ((∀ b : ↥B, k b ≠ 1) ∧
          ∀ b : ↥B, short b = -1 - k b)) ∧
      (∀ b : ↥B, short b ∈ ({-1, 0, 1} : Finset ℤ)) ∧
      (∀ b : ↥B,
        correctedOwnerValue g x z k b ∈ AddSubgroup.zmultiples y) ∧
      (∀ A C : Finset ↥B, A ≠ C →
        (∑ b ∈ A, correctedOwnerValue g x z k b) =
          ∑ b ∈ C, correctedOwnerValue g x z k b →
        (∑ b ∈ A, short b) - (∑ b ∈ C, short b) ≤ -2 ∨
          2 ≤ (∑ b ∈ A, short b) - (∑ b ∈ C, short b)) ∧
      32 ≤ (shortProfileSupport short).card

/-- Critical full-kernel capacity forces a short-profile support of at least
32 rows. -/
theorem PrimitiveThreeResidueCorrectedRows.toLargeShortProfileRows_of_critical
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hrows : PrimitiveThreeResidueCorrectedRows g y B)
    (hretained : n - B.card = 2)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hcritical : 2 ^ 6 * q < stratumBound n 6) :
    PrimitiveLargeShortProfileRows g y B := by
  classical
  rcases hrows with ⟨x, z, k, hxB, hzB, hxz, hprimitive,
    hk, hwindow, hmem, hcross⟩
  let value : Finset ↥B → AddSubgroup.zmultiples y := fun A ↦
    ⟨∑ b ∈ A, correctedOwnerValue g x z k b,
      AddSubgroup.sum_mem _ fun b _ ↦ hmem b⟩
  have horder : q = addOrderOf y :=
    (Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd).symm
  have hBcard : B.card ≤ n := by
    simpa using Finset.card_le_univ B
  have hn : n = B.card + 2 := by omega
  have hcriticalPow : 2 ^ 6 * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  rw [hn, pow_add] at hcriticalPow
  norm_num at hcriticalPow
  have hcriticalSixteen : 16 * q < 2 ^ B.card := by omega
  rcases hwindow with hnoMinusTwo | hnoOne
  · let short : ↥B → ℤ := k
    have hshortMem : ∀ b : ↥B,
        short b ∈ ({-1, 0, 1} : Finset ℤ) := by
      intro b
      have hb := hk b
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
      rcases hb with hminusTwo | hminusOne | hzero | hone
      · exact (hnoMinusTwo b hminusTwo).elim
      · exact Or.inl hminusOne
      · exact Or.inr (Or.inl hzero)
      · exact Or.inr (Or.inr hone)
    have hshortCross : ∀ A C : Finset ↥B, A ≠ C → value A = value C →
        (∑ b ∈ A, short b) - (∑ b ∈ C, short b) ≤ -2 ∨
          2 ≤ (∑ b ∈ A, short b) - (∑ b ∈ C, short b) := by
      intro A C hAC hvalue
      have hsum := congrArg Subtype.val hvalue
      rcases hcross A C hAC hsum with hleft | hright
      · exact Or.inl hleft.1
      · exact Or.inr hright.2
    have hsupport : 32 ≤ (shortProfileSupport short).card := by
      by_contra hsmall
      have hsupportLe : (shortProfileSupport short).card ≤ 31 := by omega
      rcases finiteMap_capacity_or_largeFiber
          (Finset.univ : Finset (AddSubgroup.zmultiples y)) value
            (fun _ ↦ Finset.mem_univ _) 16 with
        hcap | ⟨target, _htarget, hlarge⟩
      · have hcap' : 2 ^ B.card ≤ q * 16 := by
          simpa only [Fintype.card_finset, Fintype.card_coe,
            Finset.card_univ, Fintype.card_zmultiples, ← horder] using hcap
        omega
      · have hfiber := card_shortProfile_fiber_le_div_two_add_one
          short hshortMem value hshortCross target
        have hfiberLe :
            ((Finset.univ : Finset (Finset ↥B)).filter
              (fun A ↦ value A = target)).card ≤ 16 := by
          omega
        exact (Nat.not_lt_of_ge hfiberLe hlarge).elim
    refine ⟨x, z, k, short, hxB, hzB, hxz, hprimitive, hk,
      Or.inl ⟨hnoMinusTwo, fun _ ↦ rfl⟩, hshortMem, hmem, ?_, hsupport⟩
    intro A C hAC hsum
    exact hshortCross A C hAC (Subtype.ext hsum)
  · let short : ↥B → ℤ := fun b ↦ -1 - k b
    have hshortMem : ∀ b : ↥B,
        short b ∈ ({-1, 0, 1} : Finset ℤ) := by
      intro b
      have hb := hk b
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
      rcases hb with hminusTwo | hminusOne | hzero | hone
      · exact Or.inr (Or.inr (by dsimp only [short]; omega))
      · exact Or.inr (Or.inl (by dsimp only [short]; omega))
      · exact Or.inl (by dsimp only [short]; omega)
      · exact (hnoOne b hone).elim
    have hshortSum : ∀ A : Finset ↥B,
        (∑ b ∈ A, short b) = correctedSubsetZCoefficient k A := by
      intro A
      simp only [short, correctedSubsetZCoefficient,
        correctedSubsetXCoefficient, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      omega
    have hshortCross : ∀ A C : Finset ↥B, A ≠ C → value A = value C →
        (∑ b ∈ A, short b) - (∑ b ∈ C, short b) ≤ -2 ∨
          2 ≤ (∑ b ∈ A, short b) - (∑ b ∈ C, short b) := by
      intro A C hAC hvalue
      have hsum := congrArg Subtype.val hvalue
      rcases hcross A C hAC hsum with hleft | hright
      · right
        rw [hshortSum A, hshortSum C]
        exact hleft.2
      · left
        rw [hshortSum A, hshortSum C]
        exact hright.1
    have hsupport : 32 ≤ (shortProfileSupport short).card := by
      by_contra hsmall
      have hsupportLe : (shortProfileSupport short).card ≤ 31 := by omega
      rcases finiteMap_capacity_or_largeFiber
          (Finset.univ : Finset (AddSubgroup.zmultiples y)) value
            (fun _ ↦ Finset.mem_univ _) 16 with
        hcap | ⟨target, _htarget, hlarge⟩
      · have hcap' : 2 ^ B.card ≤ q * 16 := by
          simpa only [Fintype.card_finset, Fintype.card_coe,
            Finset.card_univ, Fintype.card_zmultiples, ← horder] using hcap
        omega
      · have hfiber := card_shortProfile_fiber_le_div_two_add_one
          short hshortMem value hshortCross target
        have hfiberLe :
            ((Finset.univ : Finset (Finset ↥B)).filter
              (fun A ↦ value A = target)).card ≤ 16 := by
          omega
        exact (Nat.not_lt_of_ge hfiberLe hlarge).elim
    refine ⟨x, z, k, short, hxB, hzB, hxz, hprimitive, hk,
      Or.inr ⟨hnoOne, fun _ ↦ rfl⟩, hshortMem, hmem, ?_, hsupport⟩
    intro A C hAC hsum
    exact hshortCross A C hAC (Subtype.ext hsum)

/-- The constant short-profile class is an actual large quotient-residue
class: all sixteen selected owners differ pairwise by elements of the odd
kernel. -/
theorem PrimitiveLargeShortProfileRows.exists_kernelCoset_card_sixteen
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hrows : PrimitiveLargeShortProfileRows g y B) :
    ∃ S : Finset (Fin n),
      16 ≤ S.card ∧ S ⊆ B ∧
        ∀ b ∈ S, ∀ c ∈ S,
          g b - g c ∈ AddSubgroup.zmultiples y := by
  classical
  rcases hrows with ⟨x, z, k, short, _hxB, _hzB, _hxz, _hprimitive,
    _hk, hwindow, hshortMem, hmem, _hcross, hsupport⟩
  let P : Finset ↥B :=
    Finset.univ.filter (fun b : ↥B ↦ short b = 1)
  let M : Finset ↥B :=
    Finset.univ.filter (fun b : ↥B ↦ short b = -1)
  have hsum := card_pos_add_card_neg_eq_shortProfileSupport
    short hshortMem
  obtain ⟨e, he, F, hFdef, hFcard⟩ :
      ∃ e : ℤ, (e = -1 ∨ e = 1) ∧ ∃ F : Finset ↥B,
        F = Finset.univ.filter (fun b : ↥B ↦ short b = e) ∧
          16 ≤ F.card := by
    by_cases hP : 16 ≤ P.card
    · exact ⟨1, Or.inr rfl, P, by simp only [P], hP⟩
    · have hM : 16 ≤ M.card := by
        dsimp only [P, M] at hsum hP ⊢
        omega
      exact ⟨-1, Or.inl rfl, M, by simp only [M], hM⟩
  let S : Finset (Fin n) := F.image (fun b : ↥B ↦ (b : Fin n))
  have hScard : S.card = F.card := by
    simpa only [S] using
      Finset.card_image_of_injective F Subtype.coe_injective
  have hSsub : S ⊆ B := by
    intro b hb
    obtain ⟨bB, _hbF, rfl⟩ := Finset.mem_image.mp hb
    exact bB.property
  refine ⟨S, by omega, hSsub, ?_⟩
  intro b hbS c hcS
  obtain ⟨bB, hbF, rfl⟩ := Finset.mem_image.mp hbS
  obtain ⟨cB, hcF, rfl⟩ := Finset.mem_image.mp hcS
  have hbShort : short bB = e := by
    rw [hFdef] at hbF
    exact (Finset.mem_filter.mp hbF).2
  have hcShort : short cB = e := by
    rw [hFdef] at hcF
    exact (Finset.mem_filter.mp hcF).2
  have hkEq : k bB = k cB := by
    rcases hwindow with ⟨_hnoMinusTwo, hshortEq⟩ |
        ⟨_hnoOne, hshortEq⟩
    · rw [hshortEq bB] at hbShort
      rw [hshortEq cB] at hcShort
      exact hbShort.trans hcShort.symm
    · rw [hshortEq bB] at hbShort
      rw [hshortEq cB] at hcShort
      omega
  have hsub := AddSubgroup.sub_mem _ (hmem bB) (hmem cB)
  convert hsub using 1
  simp only [correctedOwnerValue]
  rw [hkEq]
  module

/-- Restricting a valid tuple to coordinates in one coset of `Z*y`, then
translating into the subgroup, gives the set-free exponential lower bound at
the subgroup scale. -/
theorem two_pow_pred_le_addOrderOf_of_valid_kernelCoset
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcoset : ∀ b ∈ S, ∀ c ∈ S,
      g b - g c ∈ AddSubgroup.zmultiples y) :
    2 ^ (S.card - 1) ≤ addOrderOf y := by
  classical
  obtain ⟨base, hbaseS⟩ := hS
  let e : Fin S.card ↪ Fin n := (S.orderEmbOfFin rfl).toEmbedding
  have heS : ∀ i : Fin S.card, e i ∈ S := by
    intro i
    exact S.orderEmbOfFin_mem rfl i
  let disp : Fin S.card → G := fun i ↦ g (e i) - g base
  have hdispMem : ∀ i : Fin S.card,
      disp i ∈ AddSubgroup.zmultiples y := by
    intro i
    exact hcoset (e i) (heS i) base hbaseS
  have hsubValid : ValidTuple (fun i ↦ g (e i)) :=
    validTuple_embedding e g hg
  have htranslated : ValidTuple disp := by
    simpa only [disp] using
      validTuple_sub_const (fun i ↦ g (e i)) hsubValid (g base)
  let gH : Fin S.card → AddSubgroup.zmultiples y := fun i ↦
    ⟨disp i, hdispMem i⟩
  have hgH : ValidTuple gH := by
    apply validTuple_of_comp (AddSubgroup.zmultiples y).subtype
    simpa [gH] using htranslated
  have hcard := two_pow_pred_le_card_of_validTuple gH hgH
  rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hcard
  exact hcard

/-- The critical primitive survivor is not only large in dimension: its odd
kernel itself has order at least `2^15`. -/
theorem PrimitiveLargeShortProfileRows.two_pow_fifteen_le_oddFactor
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hrows : PrimitiveLargeShortProfileRows g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1) :
    2 ^ 15 ≤ q := by
  obtain ⟨S, hScard, _hSsub, hcoset⟩ :=
    hrows.exists_kernelCoset_card_sixteen g y B
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hsubgroup := two_pow_pred_le_addOrderOf_of_valid_kernelCoset
    g hg y S hS hcoset
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  rw [horder] at hsubgroup
  calc
    2 ^ 15 ≤ 2 ^ (S.card - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ q := hsubgroup

end MinModulus
