/-
# The exact minimum order for unique multiset sums in finite abelian groups

Formalization of M. Inal, *The Exact Minimum Order for Unique Multiset Sums in
Finite Abelian Groups* (2026), which settles the fourth open problem of
J. A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*
(arXiv:2607.08366): the least order `m_ab(n)` of a finite abelian group
carrying a *valid* `n`-tuple is exactly `2^(n-1)`.

A tuple `g : Fin n → G` is **valid** (`ValidTuple`) when the all-ones vector is
the unique nonnegative multiplicity vector `k` of total weight `n` with
`∑ k_i • g_i = ∑ g_i`.  Writing `n = m + 1` and `h_j = g_{j+1} - g_0`, the key
lemma is that validity forces the `h_j` to be **dissociated** — their `2^m`
subset sums are distinct (`ssum_injective`).  This gives:

* `card_ge`      — lower bound: a valid tuple forces `2^(n-1) ≤ |G|`;
* `elem_valid` / `elem_card` — sharpness: the standard-basis tuple in
  `(ZMod 2)^(n-1)` is valid and its group has order `2^(n-1)`;
* `equality_classification` — equality: if `|G| = 2^(n-1)`, then `G` has
  exponent two and the subset-sum map is a bijection, so the differences form
  an `𝔽₂`-basis.

Every result is proved in full (no proof holes); the axiom audit in
`scripts/check_axioms.lean` confirms only `propext`, `Classical.choice`,
`Quot.sound` are used.
-/
import Mathlib

namespace MinModulus

open Finset
open scoped BigOperators

/-- A tuple `g : Fin n → G` in an additive abelian group is *valid* if the
all-ones vector is the unique `k : Fin n → ℕ` with `∑ i, k i = n` and
`∑ i, k i • g i = ∑ i, g i`. -/
def ValidTuple {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) : Prop :=
  ∀ k : Fin n → ℕ, (∑ i, k i = n) → (∑ i, k i • g i = ∑ i, g i) → ∀ i, k i = 1

section Differences

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The `j`-th translated difference `g_{j+1} - g_0`. -/
def diff (g : Fin (m + 1) → G) (j : Fin m) : G := g j.succ - g 0

/-- Subset-sum map of the differences: `ssum g S = ∑_{j ∈ S} (g_{j+1} - g_0)`. -/
def ssum (g : Fin (m + 1) → G) (S : Finset (Fin m)) : G := ∑ j ∈ S, diff g j

/-- `ssum g S = (∑_{j ∈ S} g_{j+1}) - |S| • g_0`. -/
lemma ssum_eq (g : Fin (m + 1) → G) (S : Finset (Fin m)) :
    ssum g S = (∑ j ∈ S, g j.succ) - S.card • g 0 := by
  unfold ssum diff
  rw [Finset.sum_sub_distrib, Finset.sum_const]

/-- **Dissociation, disjoint core.**  If two *disjoint* index sets with
`|S| ≤ |T|` have equal subset sums and are distinct, the resulting multiplicity
vector rivals the all-ones vector, contradicting validity. -/
lemma not_collision_disjoint (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {S T : Finset (Fin m)} (hdisj : Disjoint S T) (hcard : S.card ≤ T.card)
    (hne : S ≠ T) (hcol : ssum g S = ssum g T) : False := by
  -- The rival multiplicities: head `k0`, tail `kk`.
  set k0 : ℕ := 1 + (T.card - S.card) with hk0
  set kk : Fin m → ℕ := fun j => if j ∈ S then 2 else if j ∈ T then 0 else 1 with hkk
  -- Indicator sums.
  have hsumS : (∑ j, (if j ∈ S then (1 : ℕ) else 0)) = S.card := by simp
  have hsumT : (∑ j, (if j ∈ T then (1 : ℕ) else 0)) = T.card := by simp
  -- Pointwise `ℕ` identity giving the total weight.
  have hkkid : ∀ j : Fin m, kk j + (if j ∈ T then 1 else 0) = 1 + (if j ∈ S then 1 else 0) := by
    intro j
    by_cases hs : j ∈ S
    · have hnt : j ∉ T := Finset.disjoint_left.mp hdisj hs
      simp [hkk, hs, hnt]
    · by_cases ht : j ∈ T <;> simp [hkk, hs, ht]
  have hAsum : (∑ j, kk j) + T.card = m + S.card := by
    have h2 : (∑ j, (kk j + (if j ∈ T then 1 else 0)))
        = ∑ j, (1 + (if j ∈ S then (1 : ℕ) else 0)) :=
      Finset.sum_congr rfl (fun j _ => hkkid j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumS, hsumT,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
    exact h2
  have hcount : (∑ i, (Fin.cons k0 kk : Fin (m + 1) → ℕ) i) = m + 1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  -- Pointwise group identity turning each tail scalar into an indicator difference.
  have htail : ∀ j : Fin m, ((kk j : ℤ) - 1) • g j.succ
      = (if j ∈ S then g j.succ else 0) - (if j ∈ T then g j.succ else 0) := by
    intro j
    by_cases hs : j ∈ S
    · have hnt : j ∉ T := Finset.disjoint_left.mp hdisj hs
      have hval : kk j = 2 := by simp [hkk, hs]
      rw [hval, if_pos hs, if_neg hnt]; simp
    · by_cases ht : j ∈ T
      · have hval : kk j = 0 := by simp [hkk, hs, ht]
        rw [hval, if_neg hs, if_pos ht]; simp
      · have hval : kk j = 1 := by simp [hkk, hs, ht]
        rw [hval, if_neg hs, if_neg ht]; simp
  -- Turn the collision into a relation on the group.
  rw [ssum_eq, ssum_eq] at hcol
  have hPQ : (∑ j ∈ S, g j.succ) - ∑ j ∈ T, g j.succ = S.card • g 0 - T.card • g 0 := by
    rw [sub_eq_iff_eq_add] at hcol
    rw [hcol]; abel
  -- The rival satisfies the sum condition, via `ℤ`-scalars.
  have hsum : (∑ i, (Fin.cons k0 kk : Fin (m + 1) → ℕ) i • g i) = ∑ i, g i := by
    have hcast : ∀ i, (Fin.cons k0 kk : Fin (m + 1) → ℕ) i • g i
        = (((Fin.cons k0 kk : Fin (m + 1) → ℕ) i : ℤ)) • g i :=
      fun i => (natCast_zsmul (g i) _).symm
    have key : (∑ i, (((Fin.cons k0 kk : Fin (m + 1) → ℕ) i : ℤ) - 1) • g i) = 0 := by
      rw [Fin.sum_univ_succ]
      have head : (((Fin.cons k0 kk : Fin (m + 1) → ℕ) 0 : ℤ) - 1) • g 0
          = ((T.card : ℤ) - S.card) • g 0 := by
        have hc : ((k0 : ℤ) - 1) = (T.card : ℤ) - S.card := by
          rw [hk0]; push_cast [Nat.cast_sub hcard]; ring
        rw [Fin.cons_zero, hc]
      have tailrw : (∑ j : Fin m, (((Fin.cons k0 kk : Fin (m + 1) → ℕ) j.succ : ℤ) - 1) • g j.succ)
          = (∑ j ∈ S, g j.succ) - ∑ j ∈ T, g j.succ := by
        have hstep : ∀ j : Fin m, (((Fin.cons k0 kk : Fin (m + 1) → ℕ) j.succ : ℤ) - 1) • g j.succ
            = (if j ∈ S then g j.succ else 0) - (if j ∈ T then g j.succ else 0) := by
          intro j; rw [Fin.cons_succ]; exact htail j
        rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_sub_distrib,
          Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
      rw [head, tailrw, hPQ, ← natCast_zsmul (g 0) S.card, ← natCast_zsmul (g 0) T.card]
      module
    calc (∑ i, (Fin.cons k0 kk : Fin (m + 1) → ℕ) i • g i)
        = ∑ i, (((Fin.cons k0 kk : Fin (m + 1) → ℕ) i : ℤ)) • g i :=
          Finset.sum_congr rfl (fun i _ => hcast i)
      _ = ∑ i, g i := by
          have hz : ∀ i, (((Fin.cons k0 kk : Fin (m + 1) → ℕ) i : ℤ)) • g i
              = (((Fin.cons k0 kk : Fin (m + 1) → ℕ) i : ℤ) - 1) • g i + g i := by
            intro i; rw [sub_smul, one_smul]; abel
          rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_add_distrib, key, zero_add]
  -- Validity forces the rival to be all-ones; a witness of `S ≠ T` contradicts this.
  have hall := hg (Fin.cons k0 kk) hcount hsum
  rw [ne_eq, Finset.ext_iff] at hne
  obtain ⟨j, hj⟩ := not_forall.mp hne
  have hj1 := hall j.succ
  rw [Fin.cons_succ] at hj1
  by_cases hs : j ∈ S
  · have hval : kk j = 2 := by simp [hkk, hs]
    rw [hval] at hj1; exact absurd hj1 (by decide)
  · have ht : j ∈ T := by tauto
    have hval : kk j = 0 := by simp [hkk, hs, ht]
    rw [hval] at hj1; exact absurd hj1 (by decide)

/-- **Dissociation.**  For a valid tuple, the subset-sum map of the `m`
differences is injective. -/
lemma ssum_injective (g : Fin (m + 1) → G) (hg : ValidTuple g) :
    Function.Injective (ssum g) := by
  intro S T hcol
  by_contra hne
  have hcol' : ssum g (S \ T) = ssum g (T \ S) := by
    unfold ssum at hcol ⊢
    exact Finset.sum_sdiff_eq_sum_sdiff_iff.mpr hcol
  have hdisj : Disjoint (S \ T) (T \ S) :=
    Finset.disjoint_left.2 (fun a ha hb =>
      (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1)
  have hne' : S \ T ≠ T \ S := by
    intro h
    apply hne
    have h1 : S \ T = ∅ := by
      have hd := hdisj
      rw [← h] at hd
      exact (Finset.disjoint_self_iff_empty _).mp hd
    have h2 : T \ S = ∅ := h ▸ h1
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
      (Finset.sdiff_eq_empty_iff_subset.mp h2)
  rcases le_total (S \ T).card (T \ S).card with hle | hle
  · exact not_collision_disjoint g hg hdisj hle hne' hcol'
  · exact not_collision_disjoint g hg hdisj.symm hle (Ne.symm hne') hcol'.symm

end Differences

/-! ### The sharp lower bound -/

/-- **Lower bound.**  A finite abelian group carrying a valid `(m+1)`-tuple has
order at least `2^m`.  Equivalently, `m_ab(n) ≥ 2^(n-1)`. -/
theorem card_ge {G : Type*} [AddCommGroup G] [Fintype G] {m : ℕ}
    (g : Fin (m + 1) → G) (hg : ValidTuple g) : 2 ^ m ≤ Fintype.card G := by
  have hinj := ssum_injective g hg
  have h := Fintype.card_le_of_injective (ssum g) hinj
  rwa [Fintype.card_finset, Fintype.card_fin] at h

/-! ### Sharpness: the elementary abelian construction attains the bound -/

/-- The standard-basis tuple `(0, e_1, …, e_m)` in `(ZMod 2)^m`. -/
def elemTuple (m : ℕ) : Fin (m + 1) → (Fin m → ZMod 2) :=
  Fin.cons 0 (fun j => Pi.single j 1)

/-- The elementary abelian group `(ZMod 2)^m` has order `2^m`. -/
theorem elem_card (m : ℕ) : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Sharpness.**  The standard-basis tuple is valid, so the lower bound
`2^m` is attained. -/
theorem elem_valid (m : ℕ) : ValidTuple (elemTuple m) := by
  intro k hsum hval
  -- Reading off coordinate `j0` shows each tail multiplicity is odd.
  have hcoord : ∀ j0 : Fin m, ((k j0.succ : ℕ) : ZMod 2) = 1 := by
    intro j0
    have hR : (∑ i, elemTuple m i) j0 = 1 := by
      rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_eq_single j0]
      · simp only [elemTuple, Fin.cons_zero, Fin.cons_succ]
        rw [Pi.zero_apply, Pi.single_eq_same, zero_add]
      · intro l _ hl
        simp only [elemTuple, Fin.cons_succ]
        rw [Pi.single_eq_of_ne (Ne.symm hl)]
      · intro hj0; exact absurd (mem_univ j0) hj0
    have hL : (∑ i, k i • elemTuple m i) j0 = ((k j0.succ : ℕ) : ZMod 2) := by
      rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_eq_single j0]
      · simp only [Pi.smul_apply, elemTuple, Fin.cons_zero, Fin.cons_succ]
        rw [Pi.zero_apply, smul_zero, zero_add, Pi.single_eq_same, nsmul_eq_mul, mul_one]
      · intro l _ hl
        simp only [Pi.smul_apply, elemTuple, Fin.cons_succ]
        rw [Pi.single_eq_of_ne (Ne.symm hl), smul_zero]
      · intro hj0; exact absurd (mem_univ j0) hj0
    have h := congrFun hval j0
    rw [hL, hR] at h
    exact h
  have hodd : ∀ j0 : Fin m, k j0.succ % 2 = 1 := by
    intro j0
    have h := hcoord j0
    rcases Nat.even_or_odd (k j0.succ) with ⟨c, hc⟩ | ho
    · exfalso
      rw [hc, Nat.cast_add] at h
      rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul] at h
      exact absurd h (by decide)
    · exact Nat.odd_iff.mp ho
  have hpos : ∀ l : Fin m, 1 ≤ k l.succ := fun l => by have := hodd l; omega
  -- Total weight identity `k 0 + ∑ tail = m + 1`.
  have hsplit : k 0 + ∑ l : Fin m, k l.succ = m + 1 := by rw [← Fin.sum_univ_succ]; exact hsum
  have htot : (∑ l : Fin m, k l.succ) ≤ m + 1 := by omega
  -- No tail multiplicity exceeds `1` (odd and `≥ 3` would overshoot the total).
  have htail1 : ∀ l : Fin m, k l.succ = 1 := by
    intro l0
    by_contra hne1
    have hge3 : 3 ≤ k l0.succ := by have := hodd l0; omega
    have herase : k l0.succ + ∑ l ∈ univ.erase l0, k l.succ = ∑ l : Fin m, k l.succ :=
      Finset.add_sum_erase univ (fun l => k l.succ) (mem_univ l0)
    have hlb : m - 1 ≤ ∑ l ∈ univ.erase l0, k l.succ := by
      have hcard : (univ.erase l0).card = m - 1 := by
        rw [Finset.card_erase_of_mem (mem_univ l0), Finset.card_univ, Fintype.card_fin]
      calc m - 1 = ∑ _l ∈ univ.erase l0, 1 := by
              rw [Finset.sum_const, hcard, smul_eq_mul, mul_one]
        _ ≤ ∑ l ∈ univ.erase l0, k l.succ := Finset.sum_le_sum (fun l _ => hpos l)
    omega
  -- Hence the head multiplicity is `1` too, and every multiplicity is `1`.
  have hk0 : k 0 = 1 := by
    have : (∑ l : Fin m, k l.succ) = m := by
      rw [Finset.sum_congr rfl (fun l _ => htail1 l), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  exact fun i => Fin.cases hk0 htail1 i

/-! ### Classification of the equality case -/

section Equality

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- **Second use of validity.**  If the subset-sum map is onto (which happens at
equality), then every difference has order two: `2 • (g_{i+1} - g_0) = 0`.
Represent `2 • diff i` as a subset sum; if the index set were nonempty, the
`k_i = 3` multiplicity vector would rival the all-ones vector. -/
lemma diff_order_two (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hsurj : Function.Surjective (ssum g)) (i : Fin m) : 2 • diff g i = 0 := by
  obtain ⟨S, hS⟩ := hsurj (2 • diff g i)
  by_cases hSempty : S = ∅
  · rw [hSempty] at hS
    simpa [ssum] using hS.symm
  · exfalso
    -- `i ∉ S`, else a collision contradicts injectivity.
    have hiS : i ∉ S := by
      intro hi
      have h1 : ssum g S = diff g i + ssum g (S.erase i) := by
        rw [ssum, ssum, ← Finset.add_sum_erase S (diff g) hi]
      rw [hS, two_nsmul] at h1
      have h2 : diff g i = ssum g (S.erase i) := add_left_cancel h1
      have h3 : ssum g {i} = diff g i := by rw [ssum, Finset.sum_singleton]
      have h4 : S.erase i = {i} := ssum_injective g hg (by rw [h3]; exact h2.symm)
      have hmem : i ∈ S.erase i := by rw [h4]; exact Finset.mem_singleton_self i
      exact Finset.notMem_erase i S hmem
    have hScard : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hSempty)
    -- The rival: head `S.card - 1`, tail `kk`.
    set kk : Fin m → ℕ := fun j => if j = i then 3 else if j ∈ S then 0 else 1 with hkk
    -- Total-weight bookkeeping.
    have hkkid : ∀ j : Fin m, kk j + (if j ∈ S then 1 else 0) = 1 + (if j = i then 2 else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji; simp [hkk, hiS]
      · by_cases hjS : j ∈ S <;> simp [hkk, hji, hjS]
    have hAsum : (∑ j, kk j) + S.card = m + 2 := by
      have h2 : (∑ j, (kk j + (if j ∈ S then 1 else 0)))
          = ∑ j, (1 + (if j = i then (2 : ℕ) else 0)) :=
        Finset.sum_congr rfl (fun j _ => hkkid j)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        show (∑ j, (if j ∈ S then (1 : ℕ) else 0)) = S.card from by simp,
        show (∑ _j : Fin m, (1 : ℕ)) = m from by simp,
        show (∑ j, (if j = i then (2 : ℕ) else 0)) = 2 from by simp] at h2
      omega
    have hcount : (∑ l, (Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l) = m + 1 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
    -- Turn the subset-sum relation into a group equation.
    have hrel : (g i.succ + g i.succ) - ∑ j ∈ S, g j.succ
        = (g 0 + g 0) - (S.card : ℤ) • g 0 := by
      have hS' := hS
      rw [ssum_eq, diff, two_nsmul, ← natCast_zsmul (g 0) S.card] at hS'
      rw [sub_eq_iff_eq_add] at hS'
      rw [hS']; abel
    -- The rival satisfies the sum condition, through `ℤ`-scalars.
    have hsum : (∑ l, (Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l • g l) = ∑ l, g l := by
      have hcast : ∀ l, (Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l • g l
          = (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l : ℤ)) • g l :=
        fun l => (natCast_zsmul (g l) _).symm
      have key : (∑ l, (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l : ℤ) - 1) • g l) = 0 := by
        rw [Fin.sum_univ_succ]
        have head : (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) 0 : ℤ) - 1) • g 0
            = ((S.card : ℤ) - 2) • g 0 := by
          have hc : (((S.card - 1 : ℕ)) : ℤ) - 1 = (S.card : ℤ) - 2 := by
            push_cast [Nat.cast_sub hScard]; ring
          rw [Fin.cons_zero, hc]
        have tailrw : (∑ j : Fin m,
              (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) j.succ : ℤ) - 1) • g j.succ)
            = (g i.succ + g i.succ) - ∑ j ∈ S, g j.succ := by
          have hstep : ∀ j : Fin m,
              (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) j.succ : ℤ) - 1) • g j.succ
              = (if j = i then g j.succ + g j.succ else 0) - (if j ∈ S then g j.succ else 0) := by
            intro j
            rw [Fin.cons_succ]
            by_cases hji : j = i
            · subst hji; simp [hkk, hiS, two_zsmul]
            · by_cases hjS : j ∈ S <;> simp [hkk, hji, hjS]
          rw [Finset.sum_congr rfl (fun j _ => hstep j)]
          simp
        rw [head, tailrw.trans hrel]
        module
      calc (∑ l, (Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l • g l)
          = ∑ l, (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l : ℤ)) • g l :=
            Finset.sum_congr rfl (fun l _ => hcast l)
        _ = ∑ l, g l := by
            have hz : ∀ l, (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l : ℤ)) • g l
                = (((Fin.cons (S.card - 1) kk : Fin (m + 1) → ℕ) l : ℤ) - 1) • g l + g l := by
              intro l; rw [sub_smul, one_smul]; abel
            rw [Finset.sum_congr rfl (fun l _ => hz l), Finset.sum_add_distrib, key, zero_add]
    -- Validity says the rival is all-ones, but its `i`-th tail entry is `3`.
    have h31 := hg (Fin.cons (S.card - 1) kk) hcount hsum i.succ
    rw [Fin.cons_succ] at h31
    simp [hkk] at h31

/-- At equality the subset-sum map is a bijection. -/
theorem ssum_bijective [Fintype G] (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G = 2 ^ m) : Function.Bijective (ssum g) :=
  (Fintype.bijective_iff_injective_and_card (ssum g)).mpr
    ⟨ssum_injective g hg, by rw [Fintype.card_finset, Fintype.card_fin, hcard]⟩

/-- **Equality forces exponent two.**  If `|G| = 2^m` and `g` is valid, then every
element of `G` has order dividing two: `G` is an elementary abelian `2`-group. -/
theorem equality_order_two [Fintype G] (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G = 2 ^ m) (x : G) : 2 • x = 0 := by
  have hbij := ssum_bijective g hg hcard
  obtain ⟨S, hSx⟩ := hbij.surjective x
  rw [← hSx, ssum, Finset.smul_sum,
    Finset.sum_congr rfl (fun j _ => diff_order_two g hg hbij.surjective j),
    Finset.sum_const_zero]

/-- **Equality classification (Inal, Theorem 4.1).**  Let `g` be valid in a finite
abelian group `G` with `|G| = 2^m`.  Then:
* every element of `G` has order dividing two (`G` is elementary abelian), and
* the subset-sum map of the differences `g_{j+1} - g_0` is a bijection
  `Finset (Fin m) ≃ G`.

Equivalently, the `m` differences are dissociated (`ssum_injective`, hence
`𝔽₂`-linearly independent by the previous point) and generate `G` (surjectivity):
they form an `𝔽₂`-basis of `G`. -/
theorem equality_classification [Fintype G] (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G = 2 ^ m) :
    (∀ x : G, 2 • x = 0) ∧ Function.Bijective (ssum g) :=
  ⟨equality_order_two g hg hcard, ssum_bijective g hg hcard⟩

end Equality

end MinModulus
