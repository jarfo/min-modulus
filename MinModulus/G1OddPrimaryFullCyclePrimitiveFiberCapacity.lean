/-
# Fiber capacity for the primitive three-residue terminal

The corrected-subset collision law makes each target fiber a two-spaced set
in one integer profile coordinate.  A three-residue window puts that profile
inside an interval of length `2|B|`.  Compressing consecutive integer pairs
therefore bounds every fiber by `|B|+1`, and all corrected subsets give

    2^|B| <= (|B|+1) * addOrderOf(y).

This is not yet the factor-16 bound required to close arbitrary sixth-stratum
transversals, but it closes the coarse-capacity obstruction for `|B| <= 15`
and forces every surviving terminal into a genuinely large-transversal
regime where private/leaf provenance is available.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveCollisions

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A finite set of integers with pairwise gaps at least two, contained in an
interval of length `2D`, has at most `D+1` elements. -/
theorem card_le_add_one_of_mem_interval_of_pairwise_gap_two
    (S : Finset ℤ) (lo : ℤ) (D : ℕ)
    (hbound : ∀ a ∈ S, lo ≤ a ∧ a ≤ lo + 2 * (D : ℤ))
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a + 2 ≤ b ∨ b + 2 ≤ a) :
    S.card ≤ D + 1 := by
  classical
  let compress : ℤ → ℤ := fun a ↦ (a - lo) / 2
  let target : Finset ℤ := Finset.Icc 0 (D : ℤ)
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
    _ = D + 1 := by simp [target, Int.card_Icc]

/-- Abstract fiber bound for a three-value corrected-row profile.  The
collision hypothesis only needs the first retained coordinate of the full
crossing law. -/
theorem card_threeResidueProfile_fiber_le_add_one
    {α : Type*} [DecidableEq α]
    {B : Finset (Fin n)} (k : ↥B → ℤ)
    (hk : ∀ b : ↥B, k b ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hwindow : (∀ b : ↥B, k b ≠ -2) ∨ ∀ b : ↥B, k b ≠ 1)
    (value : Finset ↥B → α)
    (hcross : ∀ A C : Finset ↥B, A ≠ C → value A = value C →
      correctedSubsetXCoefficient k A -
            correctedSubsetXCoefficient k C ≤ -2 ∨
        2 ≤ correctedSubsetXCoefficient k A -
          correctedSubsetXCoefficient k C)
    (target : α) :
    ((Finset.univ : Finset (Finset ↥B)).filter
      (fun A ↦ value A = target)).card ≤ B.card + 1 := by
  classical
  let F : Finset (Finset ↥B) :=
    Finset.univ.filter (fun A ↦ value A = target)
  let profile : Finset ↥B → ℤ := fun A ↦
    correctedSubsetXCoefficient k A
  let S : Finset ℤ := F.image profile
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
  have hAcard : ∀ A : Finset ↥B, A.card ≤ B.card := by
    intro A
    have hle := Finset.card_le_univ A
    simpa only [Fintype.card_coe] using hle
  rcases hwindow with hnoMinusTwo | hnoOne
  · have hkBounds : ∀ b : ↥B, -1 ≤ k b ∧ k b ≤ 1 := by
      intro b
      have hmem := hk b
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hminusTwo | hminusOne | hzero | hone
      · exact (hnoMinusTwo b hminusTwo).elim
      · omega
      · omega
      · omega
    have hbound : ∀ a ∈ S,
        -(B.card : ℤ) ≤ a ∧ a ≤ -(B.card : ℤ) + 2 * (B.card : ℤ) := by
      intro a ha
      obtain ⟨A, _hAF, rfl⟩ := Finset.mem_image.mp ha
      have hcard := hAcard A
      have hlower : -(A.card : ℤ) ≤ correctedSubsetXCoefficient k A := by
        dsimp only [correctedSubsetXCoefficient]
        calc
          -(A.card : ℤ) = ∑ b ∈ A, (-1 : ℤ) := by simp
          _ ≤ ∑ b ∈ A, k b :=
            Finset.sum_le_sum fun b _ ↦ (hkBounds b).1
      have hupper : correctedSubsetXCoefficient k A ≤ (A.card : ℤ) := by
        dsimp only [correctedSubsetXCoefficient]
        calc
          (∑ b ∈ A, k b) ≤ ∑ b ∈ A, (1 : ℤ) :=
            Finset.sum_le_sum fun b _ ↦ (hkBounds b).2
          _ = (A.card : ℤ) := by simp
      dsimp only [profile]
      constructor <;> omega
    have hcard := card_le_add_one_of_mem_interval_of_pairwise_gap_two
      S (-(B.card : ℤ)) B.card hbound hgap
    simpa only [S, F, hcardS] using hcard
  · have hkBounds : ∀ b : ↥B, -2 ≤ k b ∧ k b ≤ 0 := by
      intro b
      have hmem := hk b
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hminusTwo | hminusOne | hzero | hone
      · omega
      · omega
      · omega
      · exact (hnoOne b hone).elim
    have hbound : ∀ a ∈ S,
        (-2 : ℤ) * B.card ≤ a ∧
          a ≤ (-2 : ℤ) * B.card + 2 * (B.card : ℤ) := by
      intro a ha
      obtain ⟨A, _hAF, rfl⟩ := Finset.mem_image.mp ha
      have hcard := hAcard A
      have hlower : (-2 : ℤ) * A.card ≤
          correctedSubsetXCoefficient k A := by
        dsimp only [correctedSubsetXCoefficient]
        calc
          (-2 : ℤ) * A.card = ∑ b ∈ A, (-2 : ℤ) := by
            simp [mul_comm]
          _ ≤ ∑ b ∈ A, k b :=
            Finset.sum_le_sum fun b _ ↦ (hkBounds b).1
      have hupper : correctedSubsetXCoefficient k A ≤ 0 := by
        dsimp only [correctedSubsetXCoefficient]
        calc
          (∑ b ∈ A, k b) ≤ ∑ b ∈ A, (0 : ℤ) :=
            Finset.sum_le_sum fun b _ ↦ (hkBounds b).2
          _ = 0 := by simp
      dsimp only [profile]
      constructor <;> omega
    have hcard := card_le_add_one_of_mem_interval_of_pairwise_gap_two
      S ((-2 : ℤ) * B.card) B.card hbound hgap
    simpa only [S, F, hcardS] using hcard

/-- Global capacity consequence of the primitive three-residue terminal. -/
theorem PrimitiveThreeResidueCorrectedRows.two_pow_card_le
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hrows : PrimitiveThreeResidueCorrectedRows g y B) :
    2 ^ B.card ≤ addOrderOf y * (B.card + 1) := by
  classical
  rcases hrows with ⟨x, z, k, _hxB, _hzB, _hxz, _hprimitive,
    hk, hwindow, hmem, hcross⟩
  let value : Finset ↥B → AddSubgroup.zmultiples y := fun A ↦
    ⟨∑ b ∈ A, correctedOwnerValue g x z k b,
      AddSubgroup.sum_mem _ fun b _ ↦ hmem b⟩
  rcases finiteMap_capacity_or_largeFiber
      (Finset.univ : Finset (AddSubgroup.zmultiples y)) value
        (fun _ ↦ Finset.mem_univ _) (B.card + 1) with
    hcap | ⟨target, _htarget, hlarge⟩
  · simpa only [Fintype.card_finset, Fintype.card_coe,
      Finset.card_univ, Fintype.card_zmultiples] using hcap
  · have hfiber := card_threeResidueProfile_fiber_le_add_one
      k hk hwindow value (fun A C hAC hvalue ↦ by
        have hsum := congrArg Subtype.val hvalue
        rcases hcross A C hAC hsum with hleft | hright
        · exact Or.inl hleft.1
        · exact Or.inr hright.2) target
    exact (Nat.not_lt_of_ge hfiber hlarge).elim

/-- A critical sixth-stratum exact-two survivor cannot have a small
transversal.  The factor `|B|+1` is at most the critical factor `16` through
cardinality fifteen, while criticality itself forces `16q < 2^|B|`. -/
theorem PrimitiveThreeResidueCorrectedRows.sixteen_le_card_of_critical
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hrows : PrimitiveThreeResidueCorrectedRows g y B)
    (hretained : n - B.card = 2)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hcritical : 2 ^ 6 * q < stratumBound n 6) :
    16 ≤ B.card := by
  have horder : q = addOrderOf y :=
    (Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd).symm
  have hcapacity := hrows.two_pow_card_le g y B
  rw [← horder] at hcapacity
  have hBcard : B.card ≤ n := by
    simpa using Finset.card_le_univ B
  have hn : n = B.card + 2 := by omega
  have hcriticalPow : 2 ^ 6 * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  rw [hn, pow_add] at hcriticalPow
  norm_num at hcriticalPow
  by_contra hsmall
  have hBsucc : B.card + 1 ≤ 16 := by omega
  have hcapacity' : 2 ^ B.card ≤ 16 * q := by
    calc
      2 ^ B.card ≤ q * (B.card + 1) := hcapacity
      _ ≤ q * 16 := Nat.mul_le_mul_left q hBsucc
      _ = 16 * q := by omega
  omega

end MinModulus
