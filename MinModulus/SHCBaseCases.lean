/-
# Kernel-checked cyclic SHC base cases

This file proves the three-coordinate instance of the odd cyclic SHC lower
bound.  Dissociation gives cardinality at least eight, so below the Mersenne
threshold 15 only the odd cyclic groups of orders 9, 11, and 13 remain.  A
small Boolean checker eliminates those three cases by kernel reduction.

Combining this base theorem with `SubtupleRigidity.lean` makes deletion
spanning unconditional for four-coordinate SHC families in odd cyclic groups
through the strict-window endpoint 29.
-/
import MinModulus.SubtupleRigidity

namespace MinModulus

open Finset

universe u v

variable {m : ℕ} {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]

/-- SHC is preserved by an additive equivalence of ambient groups. -/
theorem SHC.map_addEquiv (h : Fin m → G) (hs : SHC h) (e : G ≃+ H) :
    SHC (e ∘ h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply e.symm.injective
    apply hs.inj2
    simpa using congrArg e.symm hxy
  · intro S T hST
    apply hs.dis
    simpa [Function.comp_apply] using congrArg e.symm hST
  · intro x P M hxP hxM hPM hcard heq
    apply hs.sh2 x P M hxP hxM hPM hcard
    simpa [Function.comp_apply] using congrArg e.symm heq
  · intro x P M hxP hxM hPM hcard heq
    apply hs.sh3 x P M hxP hxM hPM hcard
    simpa [Function.comp_apply] using congrArg e.symm heq

/-- SHC is preserved by a permutation of its coordinate set. -/
theorem SHC.reindex_equiv (h : Fin m → G) (hs : SHC h) (e : Fin m ≃ Fin m) :
    SHC (h ∘ e) := by
  exact hs.comp_embedding h e.toEmbedding

/-- A family has a generator coordinate when one coordinate generates the
whole ambient additive group. -/
def HasGeneratorCoordinate (h : Fin m → G) : Prop :=
  ∃ x, ∀ y, y ∈ AddSubgroup.zmultiples (h x)

/-- The normalized finite exclusion target: no SHC family with first
coordinate equal to `1` exists in `ZMod N`. -/
def NormalizedSHCExcluded (m N : ℕ) : Prop :=
  ∀ h : Fin (m + 1) → ZMod N, h 0 = 1 → ¬ SHC h

/-- The four-coordinate specialization used by the first open strict window. -/
abbrev NormalizedSHCFourExcluded (N : ℕ) : Prop := NormalizedSHCExcluded 3 N

/-- Any generator coordinate can be moved to coordinate zero and identified
with `1` in the canonical cyclic model `ZMod (Nat.card G)`, preserving SHC. -/
theorem SHC.normalize_generator [Fintype G] (h : Fin (m + 1) → G) (hs : SHC h)
    (x : Fin (m + 1)) (hx : ∀ y, y ∈ AddSubgroup.zmultiples (h x)) :
    ∃ h' : Fin (m + 1) → ZMod (Nat.card G), SHC h' ∧ h' 0 = 1 := by
  let p : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 x
  let e : ZMod (Nat.card G) ≃+ G := zmodAddEquivOfGenerator hx rfl
  let h' : Fin (m + 1) → ZMod (Nat.card G) := e.symm ∘ h ∘ p
  have hsp : SHC (h ∘ p) := hs.reindex_equiv h p
  have hsh' : SHC h' := hsp.map_addEquiv (h ∘ p) e.symm
  refine ⟨h', hsh', ?_⟩
  change e.symm (h (p 0)) = 1
  rw [show p 0 = x by simp [p, Equiv.swap_apply_left]]
  exact zmodAddEquivOfGenerator_symm_apply_generator hx rfl

/-- If every SHC family has a generator coordinate, it suffices to exclude
the normalized `h 0 = 1` families in the corresponding `ZMod`. -/
theorem not_exists_shc_of_normalized [Fintype G]
    (hgen : ∀ h : Fin (m + 1) → G, SHC h → HasGeneratorCoordinate h)
    (hexcl : NormalizedSHCExcluded m (Nat.card G)) :
    ¬ ∃ h : Fin (m + 1) → G, SHC h := by
  rintro ⟨h, hs⟩
  obtain ⟨x, hx⟩ := hgen h hs
  obtain ⟨h', hsh', h'0⟩ := hs.normalize_generator h x hx
  exact hexcl h' h'0 hsh'

/-- Executable form of the three-coordinate dissociation and shell clauses.
Injective doubling is omitted because it is supplied uniformly by odd order. -/
private def checkSHC3 {N : ℕ} [NeZero N] (h : Fin 3 → ZMod N) : Bool :=
  decide (∀ S T : Finset (Fin 3), (∑ j ∈ S, h j) = ∑ j ∈ T, h j → S = T) &&
  decide (∀ (x : Fin 3) (P M : Finset (Fin 3)), x ∉ P → x ∉ M → Disjoint P M →
    P.card + 1 ≤ M.card → 2 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j) &&
  decide (∀ (x : Fin 3) (P M : Finset (Fin 3)), x ∉ P → x ∉ M → Disjoint P M →
    P.card + 2 ≤ M.card → 3 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j)

private theorem checkSHC3_eq_true_of_shc {N : ℕ} [NeZero N]
    (h : Fin 3 → ZMod N) (hs : SHC h) : checkSHC3 h = true := by
  simp only [checkSHC3, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hs.dis, hs.sh2⟩, hs.sh3⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem no_checkSHC3_nine : ¬ ∃ h : Fin 3 → ZMod 9, checkSHC3 h = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem no_checkSHC3_eleven : ¬ ∃ h : Fin 3 → ZMod 11, checkSHC3 h = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem no_checkSHC3_thirteen : ¬ ∃ h : Fin 3 → ZMod 13, checkSHC3 h = true := by
  decide

/-- There is no three-coordinate SHC family in `ZMod 9`. -/
theorem not_exists_shc_fin_three_zmod_nine : ¬ ∃ h : Fin 3 → ZMod 9, SHC h := by
  rintro ⟨h, hs⟩
  exact no_checkSHC3_nine ⟨h, checkSHC3_eq_true_of_shc h hs⟩

/-- There is no three-coordinate SHC family in `ZMod 11`. -/
theorem not_exists_shc_fin_three_zmod_eleven : ¬ ∃ h : Fin 3 → ZMod 11, SHC h := by
  rintro ⟨h, hs⟩
  exact no_checkSHC3_eleven ⟨h, checkSHC3_eq_true_of_shc h hs⟩

/-- There is no three-coordinate SHC family in `ZMod 13`. -/
theorem not_exists_shc_fin_three_zmod_thirteen : ¬ ∃ h : Fin 3 → ZMod 13, SHC h := by
  rintro ⟨h, hs⟩
  exact no_checkSHC3_thirteen ⟨h, checkSHC3_eq_true_of_shc h hs⟩

private theorem no_shc_of_cyclic_card_eq {K : Type u} [AddCommGroup K]
    [Fintype K] [IsAddCyclic K] {N : ℕ} (hcard : Nat.card K = N)
    (hno : ¬ ∃ z : Fin 3 → ZMod N, SHC z) (h : Fin 3 → K) (hs : SHC h) : False := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := K)
  let e : ZMod N ≃+ K := zmodAddEquivOfGenerator hg hcard
  apply hno
  exact ⟨e.symm ∘ h, hs.map_addEquiv h e.symm⟩

/-- **Three-coordinate cyclic SHC base case.** Every SHC family with three
coordinates in a finite odd cyclic group forces the Mersenne lower bound 15. -/
theorem cyclicSHCOddLowerBound_three : CyclicSHCOddLowerBound.{u} 3 := by
  intro K _ _ _ hodd h hs
  by_contra hnot
  have hlt : Fintype.card K < 15 := Nat.lt_of_not_ge hnot
  have h8 : 8 ≤ Fintype.card K := by
    have hc := Fintype.card_le_of_injective
      (fun S : Finset (Fin 3) ↦ ∑ j ∈ S, h j) hs.dis
    simpa using hc
  obtain ⟨q, hq⟩ := hodd
  have hcases : Fintype.card K = 9 ∨ Fintype.card K = 11 ∨ Fintype.card K = 13 := by
    omega
  rcases hcases with h9 | h11 | h13
  · exact no_shc_of_cyclic_card_eq
      (by simpa [Nat.card_eq_fintype_card] using h9)
      not_exists_shc_fin_three_zmod_nine h hs
  · exact no_shc_of_cyclic_card_eq
      (by simpa [Nat.card_eq_fintype_card] using h11)
      not_exists_shc_fin_three_zmod_eleven h hs
  · exact no_shc_of_cyclic_card_eq
      (by simpa [Nat.card_eq_fintype_card] using h13)
      not_exists_shc_fin_three_zmod_thirteen h hs

/-- **Unconditional four-coordinate saturation through the strict window.**
In an odd cyclic group of order at most 29, deleting any coordinate of a
four-coordinate SHC family leaves a tuple that still spans the whole group. -/
theorem shc_four_deleted_span_eq_top {K : Type u} [AddCommGroup K]
    [Fintype K] [IsAddCyclic K] (hodd : Odd (Fintype.card K))
    (hupper : Fintype.card K ≤ 29) (h : Fin 4 → K) (hs : SHC h) (x : Fin 4) :
    AddSubgroup.closure (Set.range fun i : Fin 3 ↦ h (x.succAbove i)) = ⊤ := by
  apply shc_deleted_span_eq_top cyclicSHCOddLowerBound_three hodd ?_ h hs x
  norm_num
  exact hupper

end MinModulus
