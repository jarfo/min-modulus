/-
# Two-adic descent lemmas for unique multiset sums

Toward the paper's first open problem (global optimality: no size-`n` residue
set is valid mod `N < 2^n - 2^⌊log₂ n⌋`), this file proves the set-free descent
steps of the proposed proof program.  Everything is stated over an arbitrary
additive abelian group `G` and an element `h` with `h + h = 0`; the intended
instance is `G = ZMod N` with `N` even and `h = N/2`, where the quotient
`G ⧸ ⟨h⟩` is `ZMod (N/2)`.

Writing `c = k - 1` for a multiplicity vector `k`, a **witness at `h`**
(`Witness g h c`) is a nonzero integer vector `c ≥ -1` with `∑ c = 0` and
`∑ cᵢ • gᵢ = h`.  Validity of `g` says exactly that there is no witness at `0`
(`validTuple_iff_no_zero_witness`).

* `witness_combination` (Lemma A): two witnesses at `h` with no common `-1`
  coordinate are negatives of each other — otherwise their sum would be a
  witness at `2h = 0`.  So the witnesses at `h` pairwise negate or share an
  omitted element.
* `quotient_valid_of_no_witness` (halving branch): with no witness at `h`, the
  tuple stays valid in `G ⧸ ⟨h⟩`.
* `deletion_descent` (Lemma B): if some coordinate `j` is touched (`c j ≠ 0`)
  by every witness at `h`, then deleting `g j` leaves a valid tuple of size
  one less in `G ⧸ ⟨h⟩`.
* `pair_descent`: if two entries differ by `h ≠ 0`, deletion applies at the
  smaller one — the clean rung `N ≥ 2 · N_min(n-1)` of the descent.
* `nat_card_quotient_two_smul`: `|G ⧸ ⟨h⟩| * 2 = |G|` for `h ≠ 0`, `h + h = 0`.

The final section instantiates the descent at `G = ZMod (2*M)`, `h = M`:
validity transports along injective additive maps (`validTuple_comp`), the
quotient is identified with `ZMod M` (`quotZMultiplesEquivZMod`), and the three
branches become `exists_validTuple_half_of_no_witness` / `_of_delete` /
`_of_pair` — each producing a valid tuple in `ZMod M` from one in `ZMod (2*M)`.
-/
import MinModulus.AbelianMin

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- An integer-coefficient **witness at target `h`** for the tuple `g`: a
nonzero `c ≥ -1` with `∑ c = 0` and `∑ cᵢ • gᵢ = h`.  Via `k = c + 1` these
are the rival multiplicity vectors whose weighted sum misses `∑ g` by `h`. -/
def Witness (g : Fin n → G) (h : G) (c : Fin n → ℤ) : Prop :=
  c ≠ 0 ∧ (∀ i, -1 ≤ c i) ∧ (∑ i, c i) = 0 ∧ (∑ i, c i • g i) = h

/-- Validity is precisely the absence of witnesses at `0`. -/
theorem validTuple_iff_no_zero_witness (g : Fin n → G) :
    ValidTuple g ↔ ∀ c : Fin n → ℤ, ¬ Witness g 0 c := by
  constructor
  · rintro hg c ⟨hne, hge, hsum, hval⟩
    set k : Fin n → ℕ := fun i => (c i + 1).toNat with hk
    have hcast : ∀ i, (k i : ℤ) = c i + 1 := by
      intro i
      have h1 : (0 : ℤ) ≤ c i + 1 := by have := hge i; omega
      simp [hk, Int.toNat_of_nonneg h1]
    have hksum : (∑ i, k i) = n := by
      have h1 : ((∑ i, k i : ℕ) : ℤ) = ∑ i, ((k i : ℕ) : ℤ) := Nat.cast_sum _ _
      have h2 : (∑ i, ((k i : ℕ) : ℤ)) = ∑ i, (c i + 1) :=
        Finset.sum_congr rfl fun i _ => hcast i
      have h3 : (∑ i, (c i + 1)) = (∑ i, c i) + n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      have h4 : ((∑ i, k i : ℕ) : ℤ) = (n : ℤ) := by rw [h1, h2, h3, hsum, zero_add]
      exact_mod_cast h4
    have hkval : (∑ i, k i • g i) = ∑ i, g i := by
      have h1 : ∀ i, k i • g i = c i • g i + g i := by
        intro i
        rw [← natCast_zsmul, hcast, add_smul, one_smul]
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, hval, zero_add]
    have hall := hg k hksum hkval
    apply hne
    funext i
    have h1 := hcast i
    rw [hall i, Nat.cast_one] at h1
    have : c i = 0 := by omega
    simpa using this
  · intro hno k hksum hkval
    by_contra hknot
    obtain ⟨i0, hi0⟩ := not_forall.mp hknot
    apply hno (fun i => (k i : ℤ) - 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hc0
      have h1 : ((k i0 : ℤ) - 1) = 0 := congrFun hc0 i0
      have : k i0 = 1 := by omega
      exact hi0 this
    · intro i
      show (-1 : ℤ) ≤ (k i : ℤ) - 1
      have : (0 : ℤ) ≤ (k i : ℤ) := Int.natCast_nonneg _
      omega
    · have h1 : (∑ i, ((k i : ℤ) - 1)) = (∑ i, ((k i : ℕ) : ℤ)) - n := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      have h2 : (∑ i, ((k i : ℕ) : ℤ)) = ((∑ i, k i : ℕ) : ℤ) := (Nat.cast_sum _ _).symm
      rw [h1, h2, hksum, sub_self]
    · have h1 : ∀ i, ((k i : ℤ) - 1) • g i = k i • g i - g i := by
        intro i
        rw [sub_smul, one_smul, natCast_zsmul]
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, hkval, sub_self]

/-- For `h` of order dividing two, every `ℤ`-multiple of `h` is `0` or `h`. -/
private lemma zsmul_eq_zero_or_self {h : G} (hh : h + h = 0) (a : ℤ) :
    a • h = 0 ∨ a • h = h := by
  rcases Int.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    subst hb
    rw [add_smul, ← smul_add, hh, smul_zero]
  · right
    subst hb
    rw [add_smul, one_smul, mul_comm 2 b, mul_smul, two_zsmul, hh, smul_zero, zero_add]

/-- **Combination (Lemma A).**  Two witnesses at `h` (with `h + h = 0`) that
share no `-1` coordinate are negatives of each other: their sum has entries
`≥ -1`, weight `0`, and value `2h = 0`, so validity forces it to vanish.
Consequently the witnesses at `h` pairwise negate or share an omitted
element. -/
theorem witness_combination (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) {c c' : Fin n → ℤ}
    (hc : Witness g h c) (hc' : Witness g h c')
    (hshare : ∀ i, ¬(c i = -1 ∧ c' i = -1)) : c' = -c := by
  obtain ⟨hne, hge, hsum, hval⟩ := hc
  obtain ⟨hne', hge', hsum', hval'⟩ := hc'
  have hno := (validTuple_iff_no_zero_witness g).mp hg
  by_contra hcon
  apply hno (c + c')
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply hcon
    funext i
    have h1 := congrFun h0 i
    simp only [Pi.add_apply, Pi.zero_apply] at h1
    simp only [Pi.neg_apply]
    omega
  · intro i
    simp only [Pi.add_apply]
    by_cases hci : c i = -1
    · have h1 : c' i ≠ -1 := fun hc1 => hshare i ⟨hci, hc1⟩
      have h2 := hge' i
      omega
    · have h1 := hge i
      have h2 := hge' i
      omega
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hsum, hsum', add_zero]
  · have h1 : ∀ i, (c + c') i • g i = c i • g i + c' i • g i := by
      intro i
      rw [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, hval, hval', hh]

/-- If one witness at an involution has a unique `-1` coordinate `b`, then
`b` is touched by every witness at that involution.  Consequently the first
open G1 configuration must have at least two omissions in every witness. -/
theorem common_touched_of_unique_omission (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) {c : Fin n → ℤ} (hc : Witness g h c)
    (b : Fin n) (hcb : c b = -1) (huniq : ∀ i, c i = -1 → i = b) :
    ∀ c' : Fin n → ℤ, Witness g h c' → c' b ≠ 0 := by
  intro c' hc' hcb0
  have hshare : ∀ i, ¬(c i = -1 ∧ c' i = -1) := by
    intro i hi
    have hib : i = b := huniq i hi.1
    subst hib
    rw [hcb0] at hi
    omega
  have hneg := witness_combination g hg hh hc hc' hshare
  have hb := congrFun hneg b
  simp only [Pi.neg_apply, hcb] at hb
  omega

/-- Three witnesses at a nonzero involution cannot sum to the zero coefficient
vector: their values would sum to `3h = h`, not zero.  This rules out the
minimal omission triangle with cyclic coefficient vectors
`(-1,-1,2)`, `(2,-1,-1)`, and `(-1,2,-1)`. -/
theorem three_witnesses_sum_ne_zero (g : Fin n → G) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {c₁ c₂ c₃ : Fin n → ℤ} (hc₁ : Witness g h c₁)
    (hc₂ : Witness g h c₂) (hc₃ : Witness g h c₃) :
    c₁ + c₂ + c₃ ≠ 0 := by
  intro hsum
  have hz : (∑ i, (c₁ + c₂ + c₃) i • g i) = 0 := by
    rw [hsum]
    simp
  have hval : (∑ i, (c₁ + c₂ + c₃) i • g i) = h + h + h := by
    have hterm : ∀ i, (c₁ + c₂ + c₃) i • g i
        = c₁ i • g i + c₂ i • g i + c₃ i • g i := by
      intro i
      simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hc₁.2.2.2, hc₂.2.2.2, hc₃.2.2.2]
  rw [hval, hh, zero_add] at hz
  exact hne hz

section Quotient

variable {h : G}

/-- **Halving branch.**  If there is no witness at `h` (and `h + h = 0`), the
tuple remains valid in the quotient `G ⧸ ⟨h⟩`. -/
theorem quotient_valid_of_no_witness (g : Fin n → G) (hg : ValidTuple g)
    (hh : h + h = 0) (hnow : ∀ c : Fin n → ℤ, ¬ Witness g h c) :
    ValidTuple (fun i =>
      QuotientAddGroup.mk' (AddSubgroup.zmultiples h) (g i)) := by
  rw [validTuple_iff_no_zero_witness]
  rintro c ⟨hne, hge, hsum, hval⟩
  have hker : (∑ i, c i • g i) ∈ (QuotientAddGroup.mk' (AddSubgroup.zmultiples h)).ker := by
    rw [AddMonoidHom.mem_ker, map_sum]
    rw [Finset.sum_congr rfl fun i _ =>
      map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples h)) (c i) (g i)]
    exact hval
  rw [QuotientAddGroup.ker_mk'] at hker
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hker
  rcases zsmul_eq_zero_or_self hh a with h0 | h1
  · exact (validTuple_iff_no_zero_witness g).mp hg c
      ⟨hne, hge, hsum, by rw [← ha, h0]⟩
  · exact hnow c ⟨hne, hge, hsum, by rw [← ha, h1]⟩

/-- **Deletion descent (Lemma B).**  If some coordinate `j` is touched by every
witness at `h` (`c j ≠ 0`), then deleting `g j` and passing to `G ⧸ ⟨h⟩` leaves
a valid tuple of size one less: a rival of the deleted problem lifts, with
multiplicity `1` at `j`, to a witness of `g` at `0` (impossible by validity) or
at `h` (impossible since its `j`-coordinate vanishes). -/
theorem deletion_descent (g : Fin (n + 1) → G) (hg : ValidTuple g)
    (hh : h + h = 0) (j : Fin (n + 1))
    (hj : ∀ c : Fin (n + 1) → ℤ, Witness g h c → c j ≠ 0) :
    ValidTuple (fun i : Fin n =>
      QuotientAddGroup.mk' (AddSubgroup.zmultiples h) (g (j.succAbove i))) := by
  rw [validTuple_iff_no_zero_witness]
  rintro c ⟨hne, hge, hsum, hval⟩
  set C : Fin (n + 1) → ℤ := j.insertNth 0 c with hC
  have hCj : C j = 0 := by simp [hC]
  have hCsucc : ∀ i, C (j.succAbove i) = c i := by
    intro i
    simp [hC]
  have hCne : C ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    intro h0
    apply hi
    have h1 := congrFun h0 (j.succAbove i)
    rwa [hCsucc, Pi.zero_apply] at h1
  have hCge : ∀ l, -1 ≤ C l := by
    intro l
    by_cases hl : l = j
    · subst hl
      rw [hCj]
      omega
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hl
      rw [← hi, hCsucc]
      exact hge i
  have hCsum : (∑ l, C l) = 0 := by
    rw [Fin.sum_univ_succAbove C j, hCj,
      Finset.sum_congr rfl fun i _ => hCsucc i, hsum, add_zero]
  have hCval : (∑ l, C l • g l) = ∑ i, c i • g (j.succAbove i) := by
    rw [Fin.sum_univ_succAbove (fun l => C l • g l) j, hCj, zero_smul, zero_add]
    exact Finset.sum_congr rfl fun i _ => by rw [hCsucc]
  have hker : (∑ l, C l • g l) ∈ (QuotientAddGroup.mk' (AddSubgroup.zmultiples h)).ker := by
    rw [AddMonoidHom.mem_ker, hCval, map_sum]
    rw [Finset.sum_congr rfl fun i _ =>
      map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples h)) (c i) (g (j.succAbove i))]
    exact hval
  rw [QuotientAddGroup.ker_mk'] at hker
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hker
  rcases zsmul_eq_zero_or_self hh a with h0 | h1
  · exact (validTuple_iff_no_zero_witness g).mp hg C
      ⟨hCne, hCge, hCsum, by rw [← ha, h0]⟩
  · exact hj C ⟨hCne, hCge, hCsum, by rw [← ha, h1]⟩ hCj

/-- **Pair descent.**  If two entries of a valid tuple differ by `h ≠ 0` (with
`h + h = 0`), then deleting the smaller one leaves a valid tuple in `G ⧸ ⟨h⟩`.
Indeed `e_a - e_b` is a witness at `h` with a single `-1`, so by combination
every witness at `h` touches `b`, and deletion descent applies at `j = b`. -/
theorem pair_descent (g : Fin (n + 1) → G) (hg : ValidTuple g)
    (hh : h + h = 0) (hne0 : h ≠ 0) {a b : Fin (n + 1)} (hab : g a - g b = h) :
    ValidTuple (fun i : Fin n =>
      QuotientAddGroup.mk' (AddSubgroup.zmultiples h) (g (b.succAbove i))) := by
  have hane : a ≠ b := by
    rintro rfl
    rw [sub_self] at hab
    exact hne0 hab.symm
  set cs : Fin (n + 1) → ℤ :=
    fun l => (if l = a then 1 else 0) - (if l = b then 1 else 0) with hcs
  have hcsa : cs a = 1 := by simp [hcs, hane]
  have hcsb : cs b = -1 := by simp [hcs, Ne.symm hane]
  have hcs_ne_b : ∀ l, l ≠ b → cs l ≠ -1 := by
    intro l hl
    by_cases hla : l = a
    · subst hla
      rw [hcsa]
      omega
    · have : cs l = 0 := by simp [hcs, hla, hl]
      rw [this]
      omega
  have hwits : Witness g h cs := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 a
      rw [hcsa, Pi.zero_apply] at h1
      exact one_ne_zero h1
    · intro l
      by_cases hla : l = a
      · subst hla; rw [hcsa]; omega
      · by_cases hlb : l = b
        · subst hlb; rw [hcsb]
        · have : cs l = 0 := by simp [hcs, hla, hlb]
          rw [this]; omega
    · rw [hcs]
      rw [Finset.sum_sub_distrib]
      rw [Finset.sum_ite_eq' univ a fun _ => (1 : ℤ),
        Finset.sum_ite_eq' univ b fun _ => (1 : ℤ)]
      simp
    · have h1 : ∀ l, cs l • g l
          = (if l = a then g l else 0) - (if l = b then g l else 0) := by
        intro l
        rw [hcs]
        simp only
        rw [sub_smul, ite_smul, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' univ a g, Finset.sum_ite_eq' univ b g]
      simpa using hab
  apply deletion_descent g hg hh b
  intro c hc hcb0
  have hshare : ∀ l, ¬(cs l = -1 ∧ c l = -1) := by
    rintro l ⟨h1, h2⟩
    by_cases hlb : l = b
    · subst hlb
      rw [hcb0] at h2
      exact absurd h2 (by norm_num)
    · exact hcs_ne_b l hlb h1
  have hcomb := witness_combination g hg hh hwits hc hshare
  have h1 : c b = 1 := by
    have h2 := congrFun hcomb b
    rw [Pi.neg_apply, hcsb] at h2
    omega
  rw [hcb0] at h1
  exact absurd h1 (by norm_num)

/-- The subgroup `⟨h⟩` generated by an element of order two halves the group:
`|G ⧸ ⟨h⟩| * 2 = |G|`. -/
theorem nat_card_quotient_two_smul (hne0 : h ≠ 0) (hh : h + h = 0) :
    Nat.card (G ⧸ AddSubgroup.zmultiples h) * 2 = Nat.card G := by
  have h2 : (2 : ℕ) • h = 0 := by rw [two_nsmul]; exact hh
  have horder : addOrderOf h = 2 := addOrderOf_eq_prime h2 hne0
  have hcardH : Nat.card (AddSubgroup.zmultiples h) = 2 := by
    rw [Nat.card_zmultiples, horder]
  rw [← hcardH]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

end Quotient

/-! ### Transport of validity along additive maps -/

section Transport

variable {H : Type*} [AddCommGroup H]

/-- Validity is preserved by postcomposition with an injective additive map. -/
theorem validTuple_comp {g : Fin n → G} (hg : ValidTuple g) (φ : G →+ H)
    (hφ : Function.Injective φ) : ValidTuple (fun i => φ (g i)) := by
  intro k hsum hval
  refine hg k hsum (hφ ?_)
  rw [map_sum, map_sum]
  calc (∑ i, φ (k i • g i)) = ∑ i, k i • φ (g i) :=
        Finset.sum_congr rfl fun i _ => map_nsmul φ _ _
    _ = ∑ i, φ (g i) := hval

/-- Validity is reflected by postcomposition with any additive map. -/
theorem validTuple_of_comp {g : Fin n → G} (φ : G →+ H)
    (hφg : ValidTuple (fun i => φ (g i))) : ValidTuple g := by
  intro k hsum hval
  refine hφg k hsum ?_
  calc (∑ i, k i • φ (g i)) = ∑ i, φ (k i • g i) :=
        Finset.sum_congr rfl fun i _ => (map_nsmul φ _ _).symm
    _ = φ (∑ i, k i • g i) := (map_sum φ _ _).symm
    _ = φ (∑ i, g i) := by rw [hval]
    _ = ∑ i, φ (g i) := map_sum φ _ _

end Transport

/-! ### The cyclic instance: `G = ZMod (2*M)`, `h = M` -/

section ZModHalf

variable {N M : ℕ}

/-- In `ZMod (2*M)` the element `M` is an involution. -/
lemma half_add_half (hN : N = 2 * M) : (M : ZMod N) + M = 0 := by
  have h1 : (M : ZMod N) + M = ((M + M : ℕ) : ZMod N) := by push_cast; ring
  rw [h1, show M + M = N by omega, ZMod.natCast_self]

/-- In `ZMod (2*M)` with `M > 0`, the involution `M` is nonzero. -/
lemma half_ne_zero (hN : N = 2 * M) (hM : 0 < M) : (M : ZMod N) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hM h0
  omega

/-- Reduction mod `M` identifies `ZMod N ⧸ ⟨M⟩` with `ZMod M` when `M ∣ N`:
the reduction map `ZMod N →+ ZMod M` is surjective with kernel exactly the
multiples of `M`. -/
noncomputable def quotZMultiplesEquivZMod [NeZero N] [NeZero M] (hdvd : M ∣ N) :
    (ZMod N ⧸ AddSubgroup.zmultiples ((M : ℕ) : ZMod N)) ≃+ ZMod M := by
  refine (QuotientAddGroup.quotientAddEquivOfEq (G := ZMod N) ?_).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (ZMod.castHom hdvd (ZMod M)).toAddMonoidHom ?_)
  · -- `⟨M⟩` is the kernel of the reduction
    apply le_antisymm
    · rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      show ZMod.castHom hdvd (ZMod M) ((M : ℕ) : ZMod N) = 0
      rw [map_natCast, ZMod.natCast_self]
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      have hx0 : ZMod.castHom hdvd (ZMod M) x = 0 := hx
      rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hx0
      obtain ⟨q, hq⟩ := hx0
      rw [AddSubgroup.mem_zmultiples_iff]
      refine ⟨(q : ℤ), ?_⟩
      have h1 : (q : ZMod N) * ((M : ℕ) : ZMod N) = ((M * q : ℕ) : ZMod N) := by
        push_cast; ring
      rw [natCast_zsmul, nsmul_eq_mul, h1, ← hq, ZMod.natCast_zmod_val]
  · -- surjectivity of the reduction
    intro y
    obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨(a : ZMod N), map_natCast (ZMod.castHom hdvd (ZMod M)) a⟩

/-- **Halving, cyclic form.**  A valid `n`-tuple mod `2M` with no witness at
`M` yields a valid `n`-tuple mod `M`. -/
theorem exists_validTuple_half_of_no_witness (hN : N = 2 * M) (hM : 0 < M)
    {g : Fin n → ZMod N} (hg : ValidTuple g)
    (hnow : ∀ c : Fin n → ℤ, ¬ Witness g (M : ZMod N) c) :
    ∃ g' : Fin n → ZMod M, ValidTuple g' := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero M := ⟨by omega⟩
  have hdvd : M ∣ N := ⟨2, by omega⟩
  have hq := quotient_valid_of_no_witness g hg (half_add_half hN) hnow
  exact ⟨_, validTuple_comp hq (quotZMultiplesEquivZMod hdvd).toAddMonoidHom
    (quotZMultiplesEquivZMod hdvd).injective⟩

/-- **Deletion, cyclic form.**  If some coordinate `j` is touched by every
witness at `M`, deleting `g j` yields a valid `n`-tuple mod `M` from a valid
`(n+1)`-tuple mod `2M`. -/
theorem exists_validTuple_half_of_delete (hN : N = 2 * M) (hM : 0 < M)
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g) (j : Fin (n + 1))
    (hj : ∀ c : Fin (n + 1) → ℤ, Witness g (M : ZMod N) c → c j ≠ 0) :
    ∃ g' : Fin n → ZMod M, ValidTuple g' := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero M := ⟨by omega⟩
  have hdvd : M ∣ N := ⟨2, by omega⟩
  have hq := deletion_descent g hg (half_add_half hN) j hj
  exact ⟨_, validTuple_comp hq (quotZMultiplesEquivZMod hdvd).toAddMonoidHom
    (quotZMultiplesEquivZMod hdvd).injective⟩

/-- **Pair descent, cyclic form.**  Two entries of a valid `(n+1)`-tuple mod
`2M` differing by `M` yield a valid `n`-tuple mod `M`: the rung
`N_min(n+1) ≥ 2 · N_min(n)` of the two-adic descent. -/
theorem exists_validTuple_half_of_pair (hN : N = 2 * M) (hM : 0 < M)
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    {a b : Fin (n + 1)} (hab : g a - g b = (M : ZMod N)) :
    ∃ g' : Fin n → ZMod M, ValidTuple g' := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero M := ⟨by omega⟩
  have hdvd : M ∣ N := ⟨2, by omega⟩
  have hq := pair_descent g hg (half_add_half hN) (half_ne_zero hN hM) hab
  exact ⟨_, validTuple_comp hq (quotZMultiplesEquivZMod hdvd).toAddMonoidHom
    (quotZMultiplesEquivZMod hdvd).injective⟩

end ZModHalf

end MinModulus
