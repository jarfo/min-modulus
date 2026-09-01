/-
# Witness-transversal descent

Common touch is a one-point transversal of the half-witness supports and
therefore gives one-coordinate deletion.  More generally, if every
half-witness touches the complement of a retained coordinate embedding, then
the retained tuple is valid after quotienting by the involution.  This file
proves that general descent and applies it to the omission transversal carried
by a critical heavy witness.
-/
import MinModulus.G1FinalDescent

namespace MinModulus

open Finset

variable {n k : ℕ} {G : Type*} [AddCommGroup G]

/-- Extending a family by zero along a finite embedding preserves its total
sum. -/
private theorem sum_function_extend_embedding
    {A Β : Type*} [Fintype A] [Fintype Β] [DecidableEq Β]
    {R : Type*} [AddCommMonoid R] (e : A ↪ Β) (f : A → R) :
    (∑ j, Function.extend e f (fun _ ↦ 0) j) = ∑ i, f i := by
  classical
  let S : Finset Β := Finset.univ.image e
  calc
    (∑ j, Function.extend e f (fun _ ↦ 0) j) =
        ∑ j ∈ S, Function.extend e f (fun _ ↦ 0) j := by
      rw [← Fintype.sum_extend_by_zero S
        (Function.extend e f (fun _ ↦ 0))]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · simp [hj]
      · have hnone : ¬ ∃ i, e i = j := by
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        simp [hj, Function.extend_apply' f (fun _ ↦ 0) j hnone]
    _ = ∑ i, f i := by
      dsimp [S]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _
        exact e.injective.extend_apply f (fun _ ↦ 0) i
      · exact e.injective.injOn

/-- For an involution, every integer multiple is either zero or the
involution itself. -/
private lemma zsmul_eq_zero_or_self_transversal {h : G}
    (hh : h + h = 0) (a : ℤ) : a • h = 0 ∨ a • h = h := by
  rcases Int.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    subst hb
    rw [add_smul, ← smul_add, hh, smul_zero]
  · right
    subst hb
    rw [add_smul, one_smul, mul_comm 2 b, mul_smul, two_zsmul, hh,
      smul_zero, zero_add]

/-- General transversal deletion.  Retain the coordinates in the image of
`e`.  If every witness at the involution touches a coordinate outside that
image, then the retained tuple is valid in the quotient by the involution. -/
theorem quotient_valid_of_witness_transversal
    (g : Fin n → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (e : Fin k ↪ Fin n)
    (hhit : ∀ c : Fin n → ℤ, Witness g h c →
      ∃ j : Fin n, (∀ i : Fin k, e i ≠ j) ∧ c j ≠ 0) :
    ValidTuple (fun i : Fin k ↦
      QuotientAddGroup.mk' (AddSubgroup.zmultiples h) (g (e i))) := by
  rw [validTuple_iff_no_zero_witness]
  rintro c ⟨hne, hge, hsum, hval⟩
  let C : Fin n → ℤ := Function.extend e c (fun _ ↦ 0)
  have hCe : ∀ i : Fin k, C (e i) = c i := by
    intro i
    exact e.injective.extend_apply c (fun _ ↦ 0) i
  have hCne : C ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    intro hzero
    apply hi
    have hz := congrFun hzero (e i)
    simpa [hCe i] using hz
  have hCge : ∀ j, -1 ≤ C j := by
    intro j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hCe i]
      exact hge i
    · have hCzero : C j = 0 := by
        exact Function.extend_apply' c (fun _ ↦ 0) j hj
      rw [hCzero]
      omega
  have hCsum : (∑ j, C j) = 0 := by
    rw [show (∑ j, C j) = ∑ i, c i from
      sum_function_extend_embedding e c, hsum]
  have hCval : (∑ j, C j • g j) = ∑ i, c i • g (e i) := by
    calc
      (∑ j, C j • g j) =
          ∑ j, Function.extend e (fun i ↦ c i • g (e i))
            (fun _ ↦ 0) j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          rw [hCe i, e.injective.extend_apply
            (fun i ↦ c i • g (e i)) (fun _ ↦ 0) i]
        · have hCzero : C j = 0 := by
            exact Function.extend_apply' c (fun _ ↦ 0) j hj
          have hextzero : Function.extend e (fun i ↦ c i • g (e i))
              (fun _ ↦ 0) j = 0 := by
            exact Function.extend_apply'
              (fun i ↦ c i • g (e i)) (fun _ ↦ 0) j hj
          rw [hCzero, hextzero, zero_smul]
      _ = ∑ i, c i • g (e i) :=
        sum_function_extend_embedding e (fun i ↦ c i • g (e i))
  have hker : (∑ j, C j • g j) ∈
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples h)).ker := by
    rw [AddMonoidHom.mem_ker, hCval, map_sum]
    rw [Finset.sum_congr rfl fun i _ ↦
      map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples h))
        (c i) (g (e i))]
    exact hval
  rw [QuotientAddGroup.ker_mk'] at hker
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hker
  rcases zsmul_eq_zero_or_self_transversal hh a with hzero | hhalf
  · exact (validTuple_iff_no_zero_witness g).mp hg C
      ⟨hCne, hCge, hCsum, by rw [← ha, hzero]⟩
  · obtain ⟨j, hjout, hjne⟩ := hhit C
      ⟨hCne, hCge, hCsum, by rw [← ha, hhalf]⟩
    apply hjne
    exact Function.extend_apply' c (fun _ ↦ 0) j (by
      rintro ⟨i, hi⟩
      exact hjout i hi)

/-- Cyclic form of transversal deletion: retaining an arbitrary embedded
`k`-subtuple gives a valid `k`-tuple modulo `M` when every half-witness touches
a deleted coordinate. -/
theorem exists_validTuple_half_of_witness_transversal
    {N M : ℕ} (hN : N = 2 * M) (hM : 0 < M)
    {g : Fin n → ZMod N} (hg : ValidTuple g) (e : Fin k ↪ Fin n)
    (hhit : ∀ c : Fin n → ℤ, Witness g (M : ZMod N) c →
      ∃ j : Fin n, (∀ i : Fin k, e i ≠ j) ∧ c j ≠ 0) :
    AdmitsValidTuple k M := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero M := ⟨by omega⟩
  have hdvd : M ∣ N := ⟨2, by omega⟩
  have hq := quotient_valid_of_witness_transversal
    g hg (half_add_half hN) e hhit
  exact ⟨_, validTuple_comp hq
    (quotZMultiplesEquivZMod hdvd).toAddMonoidHom
    (quotZMultiplesEquivZMod hdvd).injective⟩

/-- The recursive heavy branch always gives a genuine multi-coordinate
descent.  If its root witness has `t` omissions, then `t ≥ 2` and deleting
all of them leaves a valid `(n+1-t)`-tuple modulo half the modulus. -/
theorem criticalHeavyOmissionEscape_multiDelete
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalHeavyOmissionEscape g) :
    ∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      (∃ k : Fin n, 2 ≤ c k.succ) ∧
      let B := Finset.univ.filter (fun i ↦ c i = -1)
      2 ≤ B.card ∧ AdmitsValidTuple (n + 1 - B.card) (2 ^ s * q) := by
  obtain ⟨c, hc, hheavy, htrans, hesc⟩ := hescape
  let B : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i ↦ c i = -1)
  let R : Finset (Fin (n + 1)) := Finset.univ \ B
  obtain ⟨b, hcb, _⟩ := htrans c hc
  obtain ⟨c', _hc', _hcbzero, a, hab, hca, _hca'⟩ := hesc b hcb
  have hbB : b ∈ B := by simp [B, hcb]
  have haB : a ∈ B := by simp [B, hca]
  have hBcard : 2 ≤ B.card := by
    have hone : 1 < B.card :=
      Finset.one_lt_card.mpr ⟨a, haB, b, hbB, hab⟩
    omega
  let e : Fin R.card ↪ Fin (n + 1) := (R.orderEmbOfFin rfl).toEmbedding
  have hhit : ∀ d : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) d →
        ∃ j : Fin (n + 1), (∀ i : Fin R.card, e i ≠ j) ∧ d j ≠ 0 := by
    intro d hd
    obtain ⟨j, hcj, hdj⟩ := htrans d hd
    refine ⟨j, ?_, by omega⟩
    intro i hei
    have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
    have heiNotB := (Finset.mem_sdiff.mp heiR).2
    apply heiNotB
    rw [hei]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hvalidR : AdmitsValidTuple R.card (2 ^ s * q) :=
    exists_validTuple_half_of_witness_transversal hN hM hg e hhit
  have hRcard : R.card = n + 1 - B.card := by
    simp [R, Finset.card_sdiff_of_subset (Finset.subset_univ B)]
  refine ⟨c, hc, hheavy, ?_⟩
  change 2 ≤ B.card ∧ AdmitsValidTuple (n + 1 - B.card) (2 ^ s * q)
  exact ⟨hBcard, by simpa [hRcard] using hvalidR⟩

end MinModulus
