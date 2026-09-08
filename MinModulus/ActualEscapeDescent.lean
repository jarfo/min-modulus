import MinModulus.GlobalEscapeThreshold

/-! Actual affine escape counts survive identification and deletion.
The half child keeps the original projected coordinates. Removing an
escape decreases its count strictly; removing another coordinate never
increases it. In particular these facts apply at the exact G3 half
modulus, without any endpoint-classification assumption. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Every actual target survives deletion when an identified partner
is retained. This holds for arbitrary additive maps and escape counts. -/
theorem affine_target_preserved_by_hom_deletion
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j k : Fin (n+1)) (b : G)
    (hkj : k ≠ j) (hpair : φ (g j)=φ (g k)) (i : Fin n)
    (htarget : ∃ l, g l=2 • g (j.succAbove i)+b) :
    ∃ l, φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b := by
  obtain ⟨l,hl⟩ := htarget
  have hv : φ (g l)=2 • φ (g (j.succAbove i))+φ b := by rw [hl,map_add,map_nsmul]
  by_cases hlj : l=j
  · obtain ⟨k',hk'⟩ := Fin.exists_succAbove_eq hkj
    exact ⟨k',by rw [hk',← hpair]; simpa only [hlj] using hv⟩
  · obtain ⟨l',hl'⟩ := Fin.exists_succAbove_eq hlj
    exact ⟨l',by rw [hl']; exact hv⟩

/-- Child escapes embed into the original escape set with the deleted
coordinate erased. Quotienting may remove further escapes. -/
theorem affine_escape_image_subset_erase_of_hom_deletion
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j k : Fin (n+1)) (b : G)
    (hkj : k ≠ j) (hpair : φ (g j)=φ (g k)) :
    ((Finset.univ.filter (fun i : Fin n ↦ ¬ ∃ l,
      φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b)).image j.succAbove) ⊆
      (Finset.univ.filter (fun i ↦ ¬ ∃ l, g l=2 • g i+b)).erase j := by
  classical
  intro i hi
  obtain ⟨i,hmem,rfl⟩ := Finset.mem_image.mp hi
  refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne j i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro ht
  exact (Finset.mem_filter.mp hmem).2 (affine_target_preserved_by_hom_deletion φ g j k b hkj hpair i ht)

/-- The actual count after quotient deletion is at most the old count
minus the indicator that the deleted coordinate was an escape. -/
theorem affine_escape_card_le_erase_of_hom_deletion
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j k : Fin (n+1)) (b : G)
    (hkj : k ≠ j) (hpair : φ (g j)=φ (g k)) :
    (Finset.univ.filter (fun i : Fin n ↦ ¬ ∃ l,
      φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b)).card ≤
      ((Finset.univ.filter (fun i ↦ ¬ ∃ l, g l=2 • g i+b)).erase j).card := by
  classical
  have hh := Finset.card_le_card (affine_escape_image_subset_erase_of_hom_deletion φ g j k b hkj hpair)
  rwa [Finset.card_image_of_injective _ (Fin.succAbove_right_injective)] at hh

/-- Actual escape counts cannot increase under identification and deletion. -/
theorem affine_escape_card_le_of_hom_deletion
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j k : Fin (n+1)) (b : G)
    (hkj : k ≠ j) (hpair : φ (g j)=φ (g k)) :
    (Finset.univ.filter (fun i : Fin n ↦ ¬ ∃ l,
      φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b)).card ≤
      (Finset.univ.filter (fun i ↦ ¬ ∃ l, g l=2 • g i+b)).card := by
  classical
  exact (affine_escape_card_le_erase_of_hom_deletion φ g j k b hkj hpair).trans
    (Finset.card_le_card (Finset.erase_subset _ _))

/-- Deleting an actual escape strictly reduces the actual count. -/
theorem affine_escape_card_lt_of_hom_deletion_of_escape
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j k : Fin (n+1)) (b : G)
    (hkj : k ≠ j) (hpair : φ (g j)=φ (g k))
    (hj : ¬ ∃ l, g l=2 • g j+b) :
    (Finset.univ.filter (fun i : Fin n ↦ ¬ ∃ l,
      φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b)).card <
      (Finset.univ.filter (fun i ↦ ¬ ∃ l, g l=2 • g i+b)).card := by
  classical
  exact (affine_escape_card_le_erase_of_hom_deletion φ g j k b hkj hpair).trans_lt
    (Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))

/-- Equal doubles have the same actual escape status at every shift. -/
theorem affine_escape_iff_of_equal_double
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (j k : Fin n) (hdouble : 2 • g j=2 • g k) (b : G) :
    (¬ ∃ l, g l=2 • g j+b) ↔ (¬ ∃ l, g l=2 • g k+b) := by rw [hdouble]

/-- Opposite-pair deletion retains an ACTUAL valid half child and its
escape-count bound simultaneously for every projected affine shift. -/
theorem valid_actual_half_and_escape_card_le_of_doubled_collision
    {n M : ℕ} [NeZero M]
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (j k : Fin (n+1)) (hkj : k ≠ j) (hdouble : 2 • g j=2 • g k) :
    let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
    ValidTuple (fun i : Fin n ↦ π (g (j.succAbove i))) ∧
      ∀ b : ZMod (2*M),
        (Finset.univ.filter (fun i : Fin n ↦ ¬ ∃ l,
          π (g (j.succAbove l))=2 • π (g (j.succAbove i))+π b)).card ≤
        ((Finset.univ.filter (fun i ↦ ¬ ∃ l, g l=2 • g i+b)).erase j).card := by
  dsimp only
  refine ⟨validTuple_actual_half_of_doubled_collision g hg j k hkj hdouble,?_⟩
  intro b
  have hpair := castHom_eq_of_two_nsmul_eq (g j) (g k) hdouble
  simpa using affine_escape_card_le_erase_of_hom_deletion
    (ZMod.castHom (dvd_mul_left M 2) (ZMod M)).toAddMonoidHom g j k b hkj hpair

end MinModulus
