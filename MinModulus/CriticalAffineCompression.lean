import MinModulus.DeletedOutsideSpan

/-!
# Arbitrary critical-tuple affine compression

Restricting a retained actual tuple to a proper cyclic coset constructs
either the required half-modulus child or a strictly smaller-dimensional
global counterexample in the critical numerical window. The construction
has no induction hypothesis. Consuming its counterexample arm uses the
explicit lower-dimensional bound, and yields full affine generation after
every deletion unless half descent already holds. The binary window and
every exact even-stratum consumer cover arbitrary tuples of length >= 4.

No cycle, full-cover fibre, or unit-pair assumption is made. The primitive
residual and the three unrestricted global gates are not proved here.
-/

namespace MinModulus
open Finset

/-- Restrict an ACTUAL translated embedded subtuple to a cyclic subgroup.
The resulting tuple has the subgroup's order as its modulus. -/
theorem admitsValidTuple_card_subgroup_of_valid_coset_embedding
    {n k N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (e : Fin k ↪ Fin n) (b : ZMod N) (H : AddSubgroup (ZMod N))
    (hmem : ∀ i, g (e i)-b ∈ H) : AdmitsValidTuple k (Nat.card H) := by
  let v : Fin k → H := fun i ↦ ⟨g (e i)-b,hmem i⟩
  have hv : ValidTuple v := by
    apply validTuple_of_comp H.subtype
    exact validTuple_sub_const _ (validTuple_embedding e g hg) b
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  let E : H ≃+ ZMod (Nat.card H) := (zmodAddCyclicAddEquiv (G := H) inferInstance).symm
  exact ⟨fun i ↦ E (v i),validTuple_comp hv E.toAddMonoidHom E.injective⟩

/-- In the strict three-times-child-bound window, a proper coset containing
all but one coordinate gives either the actual G1 half child or an actual
strict smaller-dimensional global counterexample. No useful fibre,
cycle, parity hypothesis, or induction premise is used in this extraction. -/
theorem half_child_or_smaller_counterexample_of_proper_coset_embedding
    {n N : ℕ} [NeZero N]
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (hcritical : N < 3*globalBound n)
    (e : Fin n ↪ Fin (n+1)) (b : ZMod N) (H : AddSubgroup (ZMod N))
    (hproper : H ≠ ⊤) (hmem : ∀ i, g (e i)-b ∈ H) :
    (Even N ∧ AdmitsValidTuple n (N/2)) ∨
      (0 < Nat.card H ∧ AdmitsValidTuple n (Nat.card H) ∧ Nat.card H < globalBound n) := by
  have hv := admitsValidTuple_card_subgroup_of_valid_coset_embedding g hg e b H hmem
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  rw [Nat.card_zmod] at hcard
  have hpos : 0 < Nat.card (ZMod N ⧸ H) := Nat.card_pos
  have hne : Nat.card (ZMod N ⧸ H) ≠ 1 := by
    intro h
    apply hproper
    apply AddSubgroup.eq_top_of_card_eq H
    rw [Nat.card_zmod]
    rw [h,one_mul] at hcard
    exact hcard.symm
  by_cases htwo : Nat.card (ZMod N ⧸ H)=2
  · left
    have hhalf : Nat.card H=N/2 := by rw [htwo] at hcard; omega
    refine ⟨⟨Nat.card H,by rw [htwo] at hcard; omega⟩,?_⟩
    rwa [← hhalf]
  · right
    refine ⟨Nat.card_pos,hv,?_⟩
    have hindex : 3 ≤ Nat.card (ZMod N ⧸ H) := by omega
    have hmul := Nat.mul_le_mul_right (Nat.card H) hindex
    nlinarith

/-- Under the explicit lower-dimensional induction hypothesis, ANY proper
affine span after deleting a coordinate forces the actual half child.
This applies to arbitrary critical tuples, not just full-cover fibres. -/
theorem admitsValidTuple_half_of_critical_proper_deleted_affine_span
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (hcritical : N < globalBound (n+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L)
    (j : Fin (n+1)) (a : Fin n)
    (hproper : AddSubgroup.closure
      (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a))) ≠ ⊤) :
    AdmitsValidTuple n (N/2) := by
  let H := AddSubgroup.closure
    (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))
  rcases half_child_or_smaller_counterexample_of_proper_coset_embedding g hg
    (hcritical.trans_le (globalBound_succ_le_three_mul hn))
    j.succAboveEmb (g (j.succAbove a)) H hproper (fun i ↦ AddSubgroup.subset_closure ⟨i,rfl⟩)
      with ⟨_,hhalf⟩ | ⟨hpos,hvalid,hsmall⟩
  · exact hhalf
  · have hle := hbound hpos hvalid
    omega

/-- Arbitrary critical-tuple frontier under smaller-dimensional induction:
actual half descent, or full affine generation after EVERY deletion and
from EVERY retained anchor. No cycle/fibre extraction is assumed. -/
theorem half_descent_or_all_deleted_affine_spans_top_of_critical_tuple
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (hcritical : N < globalBound (n+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L) :
    AdmitsValidTuple n (N/2) ∨
      ∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤ := by
  by_cases h : AdmitsValidTuple n (N/2)
  · exact Or.inl h
  · right
    intro j a
    by_contra hproper
    exact h (admitsValidTuple_half_of_critical_proper_deleted_affine_span
      hn g hg hcritical hbound j a hproper)

/-- No-cycle, no-fibre extraction in the ENTIRE subbinary range. A
proper coset containing all but one coordinate supplies actual half
descent or an actual smaller counterexample, without induction. -/
theorem half_child_or_smaller_counterexample_of_subbinary_proper_coset_embedding
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^(n+1))
    (e : Fin n ↪ Fin (n+1)) (b : ZMod N) (H : AddSubgroup (ZMod N))
    (hproper : H ≠ ⊤) (hmem : ∀ i, g (e i)-b ∈ H) :
    (Even N ∧ AdmitsValidTuple n (N/2)) ∨
      (0 < Nat.card H ∧ AdmitsValidTuple n (Nat.card H) ∧ Nat.card H < globalBound n) :=
  half_child_or_smaller_counterexample_of_proper_coset_embedding g hg
    (hsmall.trans_le (two_pow_succ_le_three_mul_globalBound hn)) e b H hproper hmem

/-- Under the explicitly stated child bound, arbitrary subbinary tuples
have actual half descent or full deleted affine spans at EVERY anchor.
This includes all even critical strata, not just the global envelope. -/
theorem half_descent_or_all_deleted_affine_spans_top_of_subbinary_tuple
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^(n+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L) :
    (Even N ∧ AdmitsValidTuple n (N/2)) ∨
      ∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤ := by
  by_cases h : Even N ∧ AdmitsValidTuple n (N/2)
  · exact Or.inl h
  · right
    intro j a
    by_contra hproper
    let H := AddSubgroup.closure
      (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))
    rcases half_child_or_smaller_counterexample_of_subbinary_proper_coset_embedding
      hn g hg hsmall j.succAboveEmb (g (j.succAbove a)) H hproper
      (fun i ↦ AddSubgroup.subset_closure ⟨i,rfl⟩) with hhalf | ⟨hpos,hvalid,hsmall'⟩
    · exact h hhalf
    · have hle := hbound hpos hvalid
      omega

/-- At odd modulus the half branch is impossible. Hence lower-dimensional
induction forces every deleted affine span to be full for arbitrary
subbinary tuples; no odd-stratum theorem is assumed here. -/
theorem all_deleted_affine_spans_top_of_odd_subbinary_tuple
    {n N : ℕ} [NeZero N] (hn : 3 ≤ n) (hodd : Odd N)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^(n+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L) :
    ∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
      (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤ := by
  rcases half_descent_or_all_deleted_affine_spans_top_of_subbinary_tuple
    hn g hg hsmall hbound with ⟨heven,_⟩ | hfull
  · obtain ⟨a,ha⟩ := hodd
    obtain ⟨b,hb⟩ := heven
    omega
  · exact hfull

/-- Direct G1 consumer at every exact even stratum. The child bound is
explicit; the retained full affine-span condition is extracted unless
the required one-coordinate HALF-modulus descent already holds. -/
theorem half_descent_or_all_deleted_affine_spans_top_of_critical_stratum
    {n s q : ℕ} (hn : 3 ≤ n) (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hbound : ∀ {L : ℕ}, 0 < L → AdmitsValidTuple n L → globalBound n ≤ L) :
    AdmitsValidTuple n (2^s*q) ∨
      ∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤ := by
  have hNpos : 0 < 2^(s+1)*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨ne_of_gt hNpos⟩
  have hsmall : 2^(s+1)*q < 2^(n+1) := hcritical.trans_le (Nat.sub_le _ _)
  rcases half_descent_or_all_deleted_affine_spans_top_of_subbinary_tuple
    hn g hg hsmall hbound with ⟨_,hhalf⟩ | hfull
  · left
    have hdiv : (2^(s+1)*q)/2=2^s*q := by rw [pow_succ',mul_assoc]; omega
    rwa [hdiv] at hhalf
  · exact Or.inr hfull

end MinModulus
