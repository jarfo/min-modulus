import MinModulus.FullCoverExpansionExtraction

/-!
# Terminal outside expansion states

Validity bounds every one-coin outside expansion path beside a zero-sum
thin fibre. A maximal path therefore produces an actual terminal multiset.
Its support cannot be expanded using any of the original outside alphabet.
-/

namespace MinModulus
open Finset

/-- If every length-L path is impossible, some shorter path ends at a
terminal state. No finiteness assumption on the state space is needed. -/
theorem exists_terminal_prefix_of_no_length_path
    {A : Type*} (R : A → A → Prop) (a : A) {L : ℕ}
    (hno : ∀ s : ℕ → A, s 0 = a → (∀ j < L, R (s j) (s (j+1))) → False) :
    ∃ r < L, ∃ s : ℕ → A, s 0 = a ∧
      (∀ j < r, R (s j) (s (j+1))) ∧ ¬ ∃ b, R (s r) b := by
  classical
  let next : A → A := fun x ↦ if h : ∃ y, R x y then Classical.choose h else x
  let s : ℕ → A := fun j ↦ next^[j] a
  have hstart : s 0 = a := rfl
  have hstep (j : ℕ) (h : ∃ y, R (s j) y) : R (s j) (s (j+1)) := by
    have heq : s (j+1) = next (s j) := Function.iterate_succ_apply' next j a
    rw [heq]
    simpa only [next, dif_pos h] using Classical.choose_spec h
  have hex : ∃ r < L, ¬ ∃ b, R (s r) b := by
    by_contra hn
    push Not at hn
    exact hno s hstart (fun j hj ↦ hstep j (hn j hj))
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  refine ⟨r, hr.1, s, hstart, ?_, hr.2⟩
  intro j hj
  apply hstep
  by_contra hn
  exact Nat.find_min hex hj ⟨by omega, hn⟩

/-- A terminal expansion state forbids expansion of every squarefree
subset of its support, with replacements from the entire alphabet. -/
theorem no_expansion_of_subset_of_terminal
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (s : Multiset (Fin k)) (hterminal : ¬ ∃ t, QuotientExpansionStep q s t)
    (S : Finset (Fin k)) (hS : S.val ≤ s)
    (p : Multiset (Fin k)) (hp : p.card = S.card+1) :
    (p.map q).sum ≠ ∑ i ∈ S, q i := by
  intro hv
  apply hterminal
  refine ⟨p+(s-S.val), S, p, s-S.val, ?_, rfl, hp, hv⟩
  symm
  rw [add_comm, Multiset.sub_add_cancel hS]

/-- Every coordinate still present at termination avoids every two-coin
sum of the original alphabet, including repeated summands. -/
theorem terminal_support_avoids_two_coin_sums
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (s : Multiset (Fin k)) (hterminal : ¬ ∃ t, QuotientExpansionStep q s t)
    (i : Fin k) (hi : i ∈ s) (a b : Fin k) : q i ≠ q a+q b := by
  classical
  have hs : ({i} : Finset (Fin k)).val ≤ s := by simpa using Multiset.singleton_le.mpr hi
  have h := no_expansion_of_subset_of_terminal q s hterminal {i} hs ({a,b} : Multiset (Fin k))
    (by simp)
  intro heq
  apply h
  simpa using heq.symm

/-- A terminal state's whole support cannot be the entire alphabet if
the full squarefree total admits a one-coin expansion. -/
theorem exists_missing_coordinate_of_terminal_of_expansion
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (s : Multiset (Fin k)) (hterminal : ¬ ∃ t, QuotientExpansionStep q s t)
    (p : Multiset (Fin k)) (hp : p.card = k+1)
    (hv : (p.map q).sum = ∑ i, q i) : ∃ i, s.count i = 0 := by
  classical
  by_contra hn
  push Not at hn
  have hle : (Finset.univ : Finset (Fin k)).val ≤ s := by
    apply (Multiset.le_iff_subset (Finset.univ : Finset (Fin k)).nodup).mpr
    intro i _
    exact Multiset.count_pos.mp (Nat.pos_of_ne_zero (hn i))
  exact no_expansion_of_subset_of_terminal q s hterminal Finset.univ hle p (by simpa using hp) hv

/-- Any positive-length expansion of a uniquely shortest squarefree
total has some coefficient at least three, regardless of its surplus. -/
theorem exists_three_le_count_of_positive_expansion_of_short_sum_rigidity
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (hmin : ∀ p : Multiset (Fin k), p.card ≤ k → (p.map q).sum = ∑ i, q i →
      p = (Finset.univ : Finset (Fin k)).val)
    (p : Multiset (Fin k)) (hp : k < p.card) (hv : (p.map q).sum = ∑ i, q i) :
    ∃ i, 3 ≤ p.count i := by
  classical
  by_contra hn
  push Not at hn
  let U := (Finset.univ : Finset (Fin k)).val
  have hcount (i : Fin k) : U.count i = 1 :=
    Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin k)).nodup (Finset.mem_univ i)
  have hle : p ≤ U+U := by
    apply Multiset.le_iff_count.mpr
    intro i
    rw [Multiset.count_add, hcount]
    have := hn i
    omega
  let t := U+U-p
  have heq : t+p = U+U := Multiset.sub_add_cancel hle
  have hcard : t.card+p.card = k+k := by
    simpa only [Multiset.card_add, show U.card=k by simp [U]] using congrArg Multiset.card heq
  have hvalue : (t.map q).sum = ∑ i, q i := by
    have h := congrArg (fun s : Multiset (Fin k) ↦ (s.map q).sum) heq
    simp only [Multiset.map_add, Multiset.sum_add, hv] at h
    change (t.map q).sum+(∑ i, q i) = (∑ i, q i)+(∑ i, q i) at h
    exact add_right_cancel h
  have ht := hmin t (by omega) hvalue
  have htc : t.card = k := by simp [ht]
  omega

/-- Adjoining zero to any subtuple of a terminal support gives a valid
smaller tuple when squarefree quotient sums are uniquely shortest. -/
theorem validTuple_zero_cons_of_terminal_support
    {k a : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (hmin : ∀ S : Finset (Fin k), ∀ p : Multiset (Fin k), p.card ≤ S.card →
      (p.map q).sum = ∑ i ∈ S, q i → p = S.val)
    (s : Multiset (Fin k)) (hterminal : ¬ ∃ t, QuotientExpansionStep q s t)
    (e : Fin a ↪ Fin k) (he : ∀ i, e i ∈ s) :
    ValidTuple (Fin.cons 0 (fun i ↦ q (e i))) := by
  classical
  let S : Finset (Fin k) := Finset.univ.map e
  have hScard : S.card = a := by simp [S]
  have hSsum : (∑ i ∈ S, q i) = ∑ j, q (e j) := by simp [S]
  have hSle : S.val ≤ s := by
    apply (Multiset.le_iff_subset S.nodup).mpr
    intro j hj
    change j ∈ Finset.univ.map e at hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact he i
  have hmin' (p : Multiset (Fin a)) (hp : p.card ≤ a)
      (hv : (p.map (fun i ↦ q (e i))).sum = ∑ i, q (e i)) :
      p = (Finset.univ : Finset (Fin a)).val := by
    have h := hmin S (p.map e) (by simpa only [Multiset.card_map, hScard] using hp)
      (by simpa only [Multiset.map_map, Function.comp_def, hSsum] using hv)
    exact Multiset.map_injective e.injective h
  by_contra hn
  obtain ⟨p, hp, hv⟩ := exists_one_coin_expansion_of_not_valid_zero_cons
    (fun i ↦ q (e i)) hmin' hn
  apply no_expansion_of_subset_of_terminal q s hterminal S hSle (p.map e)
    (by simpa only [Multiset.card_map, hScard] using hp)
  simpa only [Multiset.map_map, Function.comp_def, hSsum] using hv

/-- A minimal-dimensional subbinary tuple containing a mapped cycle
forces a positive but short path ending at a terminal outside multiset.
The terminal has a missing coordinate, a triple-used head, and no present
coordinate expressible as a two-coin sum from the original alphabet. -/
theorem exists_terminal_expansion_of_subbinary_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hbound : ∀ {a L : ℕ}, a < m+k → 0 < L → AdmitsValidTuple a L → globalBound a ≤ L)
    (hsmall : d*(2^m-1) < 2^(m+k)) :
    let q : Fin k → ZMod d := fun i ↦
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))
    ∃ r : ℕ, 0 < r ∧ r < m ∧ ∃ s : ℕ → Multiset (Fin k),
      s 0 = (Finset.univ : Finset (Fin k)).val ∧
      (∀ j < r, QuotientExpansionStep q (s j) (s (j+1))) ∧
      (s r).card = k+r ∧
      ((s r).map (fun i ↦ g (Fin.natAdd m i))).sum = ∑ i, g (Fin.natAdd m i) ∧
      (¬ ∃ t, QuotientExpansionStep q (s r) t) ∧
      (∃ i, (s r).count i = 0) ∧ (∃ i, 3 ≤ (s r).count i) ∧
      ∀ i ∈ s r, ∀ a b, q i ≠ q a+q b := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let π := ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
  let q : Fin k → ZMod d := fun i ↦ π (g (Fin.natAdd m i))
  change ∃ r : ℕ, 0 < r ∧ r < m ∧ ∃ s : ℕ → Multiset (Fin k), _
  obtain ⟨r, hr, s, hs0, hsteps, hterminal⟩ := exists_terminal_prefix_of_no_length_path
    (QuotientExpansionStep q) (Finset.univ : Finset (Fin k)).val
    (fun s hs ht ↦ not_expansion_path_of_valid_mapped_cycle hm τ hτ g hg hpref s hs ht)
  have hlift {a b : Multiset (Fin k)} (h : QuotientExpansionStep q a b) :
      (b.map (fun i ↦ g (Fin.natAdd m i))).sum =
      (a.map (fun i ↦ g (Fin.natAdd m i))).sum := by
    obtain ⟨S, p, rest, rfl, rfl, hcard, hq⟩ := h
    simp only [Multiset.map_add, Multiset.sum_add]
    rw [outside_expansion_eq_of_valid_mapped_cycle_quotient hm τ hτ g hg hpref S p hcard hq]
    rfl
  have hinv (j : ℕ) (hj : j ≤ r) : (s j).card = k+j ∧
      ((s j).map (fun i ↦ g (Fin.natAdd m i))).sum = ∑ i, g (Fin.natAdd m i) := by
    induction j with
    | zero => rw [hs0]; exact ⟨by simp, rfl⟩
    | succ j ih =>
      obtain ⟨hc, hv⟩ := ih (by omega)
      have h := hsteps j (by omega)
      exact ⟨by rw [quotientExpansionStep_card h, hc]; omega, (hlift h).trans hv⟩
  obtain ⟨hcard, hvalue⟩ := hinv r le_rfl
  obtain ⟨p, hp, hv, _⟩ := exists_actual_expansion_with_large_head_of_subbinary_mapped_cycle
    hm hk τ hτ g hg hpref hbound hsmall
  have hpq : (p.map q).sum = ∑ i, q i := by
    simpa only [q, map_multiset_sum, Multiset.map_map, Function.comp_def, map_sum]
      using congrArg π hv
  have hmissing := exists_missing_coordinate_of_terminal_of_expansion q (s r) hterminal p hp hpq
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    obtain ⟨i, hi⟩ := hmissing
    rw [hz, hs0] at hi
    have hone : (Finset.univ : Finset (Fin k)).val.count i = 1 :=
      Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin k)).nodup (Finset.mem_univ i)
    omega
  have hmin (p : Multiset (Fin k)) (hp : p.card ≤ k)
      (hv : (p.map q).sum = ∑ i, q i) : p = (Finset.univ : Finset (Fin k)).val :=
    quotient_multiset_eq_of_card_le_of_actual_fibre_cover (by omega) τ hτ g hg
      (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
      (exists_power_multiset_sum_at_mersenne hm) Finset.univ p (by simpa using hp) hv
  have hqvalue : ((s r).map q).sum = ∑ i, q i := by
    simpa only [q, map_multiset_sum, Multiset.map_map, Function.comp_def, map_sum]
      using congrArg π hvalue
  exact ⟨r, hrpos, hr, s, hs0, hsteps, hcard, hvalue, hterminal, hmissing,
    exists_three_le_count_of_positive_expansion_of_short_sum_rigidity q hmin (s r)
      (by omega) hqvalue,
    fun i hi a b ↦ terminal_support_avoids_two_coin_sums q (s r) hterminal i hi a b⟩

end MinModulus
