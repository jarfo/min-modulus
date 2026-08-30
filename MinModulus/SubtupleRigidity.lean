/-
# Subtuple rigidity in the odd top window

This file formalizes the induction step used in the lattice/SHC program.  If
the odd cyclic SHC lower bound is known in one lower dimension, then deleting
any coordinate from a strict-window SHC family still generates the whole
ambient cyclic group.
-/
import MinModulus.QuadraticWedge

namespace MinModulus

open Finset

universe u

variable {k m : ℕ} {G : Type u} [AddCommGroup G]

/-- SHC is inherited by restriction along an embedding of coordinate sets. -/
theorem SHC.comp_embedding (h : Fin m → G) (hs : SHC h) (e : Fin k ↪ Fin m) :
    SHC (h ∘ e) := by
  refine ⟨hs.inj2, ?_, ?_, ?_⟩
  · intro S T hST
    apply Finset.map_injective e
    apply hs.dis
    simpa [Function.comp_apply] using hST
  · intro x P M hxP hxM hPM hcard
    have hxP' : e x ∉ P.map e := by simpa using hxP
    have hxM' : e x ∉ M.map e := by simpa using hxM
    have hPM' : Disjoint (P.map e) (M.map e) := (Finset.disjoint_map e).2 hPM
    have hcard' : (P.map e).card + 1 ≤ (M.map e).card := by simpa using hcard
    simpa [Function.comp_apply] using hs.sh2 (e x) (P.map e) (M.map e)
      hxP' hxM' hPM' hcard'
  · intro x P M hxP hxM hPM hcard
    have hxP' : e x ∉ P.map e := by simpa using hxP
    have hxM' : e x ∉ M.map e := by simpa using hxM
    have hPM' : Disjoint (P.map e) (M.map e) := (Finset.disjoint_map e).2 hPM
    have hcard' : (P.map e).card + 2 ≤ (M.map e).card := by simpa using hcard
    simpa [Function.comp_apply] using hs.sh3 (e x) (P.map e) (M.map e)
      hxP' hxM' hPM' hcard'

/-- Deleting one coordinate preserves SHC. -/
theorem SHC.delete (h : Fin (m + 1) → G) (hs : SHC h) (x : Fin (m + 1)) :
    SHC (fun i : Fin m ↦ h (x.succAbove i)) := by
  have heq : (fun i : Fin m ↦ h (x.succAbove i)) = h ∘ x.succAboveEmb := by
    funext i
    rfl
  rw [heq]
  exact hs.comp_embedding h x.succAboveEmb

/-- SHC lifts from an ambient group to any additive subgroup containing every
coordinate. -/
theorem SHC.subtype (K : AddSubgroup G) (h : Fin m → G) (hs : SHC h)
    (hmem : ∀ i, h i ∈ K) :
    SHC (fun i ↦ (⟨h i, hmem i⟩ : K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply hs.inj2 x y
    exact congrArg Subtype.val hxy
  · intro S T hST
    apply hs.dis
    simpa using congrArg Subtype.val hST
  · intro x P M hxP hxM hPM hcard heq
    apply hs.sh2 x P M hxP hxM hPM hcard
    simpa using congrArg Subtype.val heq
  · intro x P M hxP hxM hPM hcard heq
    apply hs.sh3 x P M hxP hxM hPM hcard
    simpa using congrArg Subtype.val heq

/-- The conjectural odd cyclic SHC lower bound at `m` coordinates, isolated
as an induction hypothesis. -/
def CyclicSHCOddLowerBound (m : ℕ) : Prop :=
  ∀ (K : Type u) [AddCommGroup K] [Fintype K] [IsAddCyclic K],
    Odd (Fintype.card K) → ∀ h : Fin m → K, SHC h →
      2 ^ (m + 1) - 1 ≤ Fintype.card K

/-- A subgroup already above the lower-dimensional Mersenne threshold cannot
be proper inside the next strict window.  This is the arithmetic core of
subtuple rigidity. -/
theorem addSubgroup_eq_top_of_mersenne_window [Fintype G]
    (H : AddSubgroup G)
    (hlower : 2 ^ (m + 1) - 1 ≤ Nat.card H)
    (hupper : Nat.card G ≤ 2 ^ (m + 2) - 3) : H = ⊤ := by
  by_contra hne
  have hcard : Nat.card G = Nat.card (G ⧸ H) * Nat.card H :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hqpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  have hqne : Nat.card (G ⧸ H) ≠ 1 := by
    intro hq
    apply hne
    apply AddSubgroup.eq_top_of_card_eq H
    rw [hcard, hq, one_mul]
  have hq : 2 ≤ Nat.card (G ⧸ H) := by omega
  have hmul : 2 * (2 ^ (m + 1) - 1) ≤ Nat.card (G ⧸ H) * Nat.card H :=
    Nat.mul_le_mul hq hlower
  have hp : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hsucc : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  omega

/-- **Conditional subtuple rigidity.** Assume the odd cyclic SHC lower bound
for `m` coordinates.  In an odd cyclic group inside the next strict window,
every one-coordinate deletion of an SHC family of size `m+1` spans the whole
group. -/
theorem shc_deleted_span_eq_top [Fintype G] [IsAddCyclic G]
    (hind : CyclicSHCOddLowerBound.{u} m)
    (hodd : Odd (Fintype.card G))
    (hupper : Fintype.card G ≤ 2 ^ (m + 2) - 3)
    (h : Fin (m + 1) → G) (hs : SHC h) (x : Fin (m + 1)) :
    AddSubgroup.closure (Set.range fun i : Fin m ↦ h (x.succAbove i)) = ⊤ := by
  let e : Fin m ↪ Fin (m + 1) := x.succAboveEmb
  let hd : Fin m → G := h ∘ e
  let H : AddSubgroup G := AddSubgroup.closure (Set.range hd)
  have hsd : SHC hd := hs.comp_embedding h e
  have hdmem : ∀ i, hd i ∈ H := by
    intro i
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  let hH : Fin m → H := fun i ↦ ⟨hd i, hdmem i⟩
  have hsH : SHC hH := hsd.subtype H hd hdmem
  letI : Fintype H := Fintype.ofFinite H
  have hHodd : Odd (Fintype.card H) := by
    have hdiv : Nat.card H ∣ Nat.card G := AddSubgroup.card_addSubgroup_dvd_card H
    have hodd' : Odd (Nat.card G) := by
      simpa [Nat.card_eq_fintype_card] using hodd
    have := Odd.of_dvd_nat hodd' hdiv
    simpa [Nat.card_eq_fintype_card] using this
  have hlower : 2 ^ (m + 1) - 1 ≤ Nat.card H := by
    simpa [Nat.card_eq_fintype_card] using hind H hHodd hH hsH
  have hupper' : Nat.card G ≤ 2 ^ (m + 2) - 3 := by
    simpa [Nat.card_eq_fintype_card] using hupper
  have htop : H = ⊤ := addSubgroup_eq_top_of_mersenne_window H hlower hupper'
  change H = ⊤
  exact htop

end MinModulus
