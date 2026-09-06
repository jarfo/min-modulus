/-
# Direct half-size descent through a large parity fibre

If all but one entry of a valid cyclic tuple have the same parity, delete
the exceptional coordinate, translate the retained entries, and divide
their even representatives by two. This constructs the smaller valid
tuple at half the modulus without common touch or any SI hypothesis.

Thus failure of the G1 deletion conclusion forces both parity fibres to
contain at least two entries. This is a proved restriction of the same
G1 residual, not an additional global assumption or a claim that all
subbinary tuples have a singleton parity class.
-/
import MinModulus.SIMultiplierBound
import MinModulus.G1CriticalThreeOmissions

namespace MinModulus
open Finset

/-- Dividing the even representatives by two produces an actual valid
tuple in the cyclic group of half the order. -/
theorem validTuple_half_of_even_values
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M)) (hg : ValidTuple g)
    (heven : ∀ i, Even (g i).val) :
    ValidTuple (fun i ↦ (((g i).val / 2 : ℕ) : ZMod M)) := by
  have hf : ∀ i, zmodDoubleHom M (((g i).val / 2 : ℕ) : ZMod M) = g i := by
    intro i
    rw [zmodDoubleHom_natCast, Nat.mul_div_cancel' (heven i).two_dvd,
      ZMod.natCast_zmod_val]
  apply validTuple_of_comp (zmodDoubleHom M)
  simpa only [hf] using hg

/-- Any same-parity embedded subtuple can be translated and halved while
preserving validity. The original coordinates and the division are actual,
not supplied by an assumed quotient-validity statement. -/
theorem admitsValidTuple_half_of_same_parity_embedding
    {n k M : ℕ} [NeZero M]
    (g : Fin n → ZMod (2 * M)) (hg : ValidTuple g) (e : Fin k ↪ Fin n)
    (b : ZMod 2)
    (hparity : ∀ i, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e i)) = b) :
    AdmitsValidTuple k M := by
  let B : ZMod (2 * M) := b.val
  let v : Fin k → ZMod (2 * M) := fun i ↦ g (e i) - B
  have hv : ValidTuple v := validTuple_sub_const _ (validTuple_embedding e g hg) B
  have hev : ∀ i, Even (v i).val := by
    intro i
    have hzero : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (v i) = 0 := by
      rw [map_sub, hparity]
      simp [B]
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hzero
    exact even_iff_two_dvd.mpr hzero
  exact ⟨_, validTuple_half_of_even_values v hv hev⟩

/-- If all coordinates except a specified one have the same parity,
deleting it and halving the retained coset solves the required G1 descent.
No criticality, half-witness, common-touch, or SI assumption is needed. -/
theorem admitsValidTuple_half_of_all_but_one_same_parity
    {n M : ℕ} [NeZero M]
    (g : Fin (n + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (j : Fin (n + 1)) (b : ZMod 2)
    (hparity : ∀ i, i ≠ j → ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = b) :
    AdmitsValidTuple n M := by
  apply admitsValidTuple_half_of_same_parity_embedding g hg
    ⟨j.succAbove, Fin.succAbove_right_injective⟩ b
  intro i
  exact hparity _ (Fin.succAbove_ne j i)

/-- A parity fibre with at least n entries in an (n+1)-tuple supplies the
same direct half-size descent. -/
theorem admitsValidTuple_half_of_parity_fibre_card_ge
    {n M : ℕ} [NeZero M]
    (g : Fin (n + 1) → ZMod (2 * M)) (hg : ValidTuple g) (b : ZMod 2)
    (hcard : n ≤ (Finset.univ.filter (fun i ↦
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = b)).card) :
    AdmitsValidTuple n M := by
  classical
  let S := Finset.univ.filter (fun i ↦ ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = b)
  let T := Finset.univ \ S
  have hT : T.card ≤ 1 := by
    change (Finset.univ \ S).card ≤ 1
    rw [Finset.card_sdiff, Finset.inter_univ]
    simp only [Finset.card_univ, Fintype.card_fin]
    change n ≤ S.card at hcard
    omega
  by_cases hnone : T = ∅
  · apply admitsValidTuple_half_of_all_but_one_same_parity g hg (0 : Fin (n + 1)) b
    intro i _
    have hi : i ∈ S := by
      by_contra hi
      have : i ∈ T := by simp [T, hi]
      simp [hnone] at this
    exact (Finset.mem_filter.mp hi).2
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hnone
    apply admitsValidTuple_half_of_all_but_one_same_parity g hg j b
    intro i hij
    have hi : i ∈ S := by
      by_contra hi
      have hit : i ∈ T := by simp [T, hi]
      exact hij ((Finset.card_le_one.mp hT) i hit j hj)
    exact (Finset.mem_filter.mp hi).2

/-- The two parity fibres partition the entire tuple. -/
theorem parity_fibre_card_zero_add_one
    {n M : ℕ} (g : Fin n → ZMod (2 * M)) :
    (Finset.univ.filter (fun i ↦ ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 0)).card +
    (Finset.univ.filter (fun i ↦ ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 1)).card = n := by
  classical
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  have hcases (i : Fin n) : π (g i) = 0 ∨ π (g i) = 1 := by
    have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact h _
  have hnot : (Finset.univ.filter (fun i ↦ ¬π (g i) = 0)) =
      Finset.univ.filter (fun i ↦ π (g i) = 1) := by
    ext i
    rcases hcases i with h | h <;> simp [h]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i ↦ π (g i) = 0)
  rw [hnot] at h
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- A valid even-modulus tuple either admits the smaller half-modulus tuple
already, or both parity fibres have at least two coordinates. This applies
in all dimensions and does not assume any unrestricted global gate. -/
theorem admitsValidTuple_half_or_two_large_parity_fibres
    {n M : ℕ} [NeZero M]
    (g : Fin (n + 1) → ZMod (2 * M)) (hg : ValidTuple g) :
    AdmitsValidTuple n M ∨
      (2 ≤ (Finset.univ.filter (fun i ↦
        ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 0)).card ∧
       2 ≤ (Finset.univ.filter (fun i ↦
        ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 1)).card) := by
  classical
  by_cases hzero : n ≤ (Finset.univ.filter (fun i ↦
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 0)).card
  · exact Or.inl (admitsValidTuple_half_of_parity_fibre_card_ge g hg 0 hzero)
  by_cases hone : n ≤ (Finset.univ.filter (fun i ↦
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g i) = 1)).card
  · exact Or.inl (admitsValidTuple_half_of_parity_fibre_card_ge g hg 1 hone)
  have hsum := parity_fibre_card_zero_add_one g
  exact Or.inr (by omega)

/-- Transport the parity-fibre split to an explicitly factored even
modulus, preserving the actual coordinates and parity reduction. -/
theorem admitsValidTuple_half_or_two_large_parity_fibres_of_eq_two_mul
    {n N M : ℕ} [NeZero M] (hN : N = 2 * M) (hd : 2 ∣ N)
    (g : Fin (n + 1) → ZMod N) (hg : ValidTuple g) :
    AdmitsValidTuple n M ∨
      (2 ≤ (Finset.univ.filter (fun i ↦ ZMod.castHom hd (ZMod 2) (g i) = 0)).card ∧
       2 ≤ (Finset.univ.filter (fun i ↦ ZMod.castHom hd (ZMod 2) (g i) = 1)).card) := by
  subst N
  exact admitsValidTuple_half_or_two_large_parity_fibres g hg

/-- The existing G1 obligation is equivalent to its restriction to tuples
with at least two entries of each parity. This removes proved cases from
that same obligation; it does not add a new global gate. -/
theorem criticalThreeOmissionDeleteStep_iff_two_large_parity_fibres :
    CriticalThreeOmissionDeleteStep ↔
    (∀ {n s q : ℕ}, Odd q →
      ∀ g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q),
        ValidTuple g →
        2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
        WitnessThreeDistinctOmissions g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) →
        (∀ b : ZMod 2, 2 ≤ (Finset.univ.filter (fun i ↦
          ZMod.castHom (by rw [pow_succ', mul_assoc]; exact dvd_mul_right 2 _) (ZMod 2)
            (g i) = b)).card) →
        AdmitsValidTuple n (2 ^ s * q)) := by
  constructor
  · intro h n s q hq g hg hcritical hthree _
    exact h hq g hg hcritical hthree
  · intro h n s q hq g hg hcritical hthree
    have hM : 0 < 2 ^ s * q := mul_pos (by positivity) hq.pos
    letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hM⟩
    have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by rw [pow_succ', mul_assoc]
    have hd : 2 ∣ 2 ^ (s + 1) * q := by rw [hN]; exact dvd_mul_right 2 _
    rcases admitsValidTuple_half_or_two_large_parity_fibres_of_eq_two_mul hN hd g hg with
      hdone | hlarge
    · exact hdone
    · apply h hq g hg hcritical hthree
      intro b
      have hb : b = 0 ∨ b = 1 := by
        have hh : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
        exact hh b
      rcases hb with rfl | rfl
      · exact hlarge.1
      · exact hlarge.2

/-- The unchanged three-input global induction can now use deletion only
in the two-large-parity-fibre part of its three-omission residual. G2 and
G3 remain explicit, and the restricted G1 premise is still open. -/
theorem global_lower_bound_of_two_large_parity_threeOmissionDeleteStep
    (hdelete : ∀ {n s q : ℕ}, Odd q →
      ∀ g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q),
        ValidTuple g →
        2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
        WitnessThreeDistinctOmissions g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) →
        (∀ b : ZMod 2, 2 ≤ (Finset.univ.filter (fun i ↦
          ZMod.castHom (by rw [pow_succ', mul_assoc]; exact dvd_mul_right 2 _) (ZMod 2)
            (g i) = b)).card) →
        AdmitsValidTuple n (2 ^ s * q))
    (hG2 : OddStratumLowerBound) (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_threeOmissionDeleteStep
    (criticalThreeOmissionDeleteStep_iff_two_large_parity_fibres.mpr hdelete) hG2 hG3 hn hN hv

end MinModulus
