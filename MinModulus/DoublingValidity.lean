/-
# Valid doubling tuples have a single cycle

A doubling-invariant component sums to zero. Replacing one entry by two
copies of its predecessor preserves that sum and increases multiset size
by one. Starting with a proper component, this constructs a competing
multiset of the full tuple length, contrary to validity.

No odd-stratum bound, cyclic ambient group, or finite ambient group is used.
-/
import MinModulus.AbelianMin

namespace MinModulus

open Finset

/-- Every finite doubling-invariant set of indices has total sum zero. -/
theorem sum_eq_zero_of_doubling_invariant
    {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (R : Equiv.Perm α) (x : α → G) (hdouble : ∀ i, x (R i) = 2 • x i)
    (C : Finset α) (hC : Set.BijOn R C C) :
    ∑ i ∈ C, x i = 0 := by
  have hsum : (∑ i ∈ C, x (R i)) = ∑ i ∈ C, x i :=
    Finset.sum_bij (fun i _ ↦ R i) (fun i hi ↦ hC.mapsTo hi)
      (fun _ _ _ _ hij ↦ R.injective hij)
      (fun j hj ↦ by obtain ⟨i, hi, hij⟩ := hC.surjOn hj; exact ⟨i, hi, hij⟩)
      (fun _ _ ↦ rfl)
  simp_rw [hdouble] at hsum
  rw [← Finset.smul_sum, two_nsmul] at hsum
  have : (∑ i ∈ C, x i) + ∑ i ∈ C, x i = 0 + ∑ i ∈ C, x i := by
    simpa using hsum
  exact add_right_cancel this

/-- Splitting an entry into two predecessors extends a nonempty zero-sum
multiset to every larger cardinality while retaining its support constraint. -/
theorem exists_zero_multiset_of_doubling_closed
    {α G : Type*} [AddCommGroup G]
    (x : α → G) (C : Set α)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, x i = 2 • x j)
    (s : Multiset α) (hspos : 0 < s.card)
    (hsmem : ∀ i ∈ s, i ∈ C) (hsum : (s.map x).sum = 0)
    {k : ℕ} (hk : s.card ≤ k) :
    ∃ t : Multiset α, t.card = k ∧ (t.map x).sum = 0 ∧
      ∀ i ∈ t, i ∈ C := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨s, rfl, hsum, hsmem⟩
  | succ k hk ih =>
    obtain ⟨t, htcard, htsum, htmem⟩ := ih
    have htne : t ≠ 0 := by intro hz; simp [hz] at htcard; omega
    have hdecomp : t = 0 ∨ ∃ i u, t = i ::ₘ u :=
      Multiset.induction_on t (Or.inl rfl) (fun i u _ ↦ Or.inr ⟨i, u, rfl⟩)
    rcases hdecomp with hz | ⟨i, u, rfl⟩
    · exact False.elim (htne hz)
    obtain ⟨j, hjC, hji⟩ := hpred i (htmem i (by simp))
    refine ⟨j ::ₘ j ::ₘ u, by simp_all, ?_, ?_⟩
    · simpa [Multiset.map_cons, Multiset.sum_cons, hji, two_nsmul, add_assoc] using htsum
    · intro a ha
      simp only [Multiset.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact hjC
      · exact hjC
      · exact htmem a (by simp [ha])

/-- Validity excludes every nonempty proper doubling-invariant index set. -/
theorem doubling_invariant_eq_univ_of_valid
    {d : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (hdouble : ∀ i, x (R i) = 2 • x i)
    (C : Finset (Fin d)) (hCne : C.Nonempty) (hC : Set.BijOn R C C) :
    C = Finset.univ := by
  classical
  have hzero : ∑ i ∈ C, x i = 0 := sum_eq_zero_of_doubling_invariant R x hdouble C hC
  have hpred : ∀ i ∈ (C : Set (Fin d)), ∃ j ∈ (C : Set (Fin d)), x i = 2 • x j := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := hC.surjOn hi
    exact ⟨j, hj, by rw [← hji]; exact hdouble j⟩
  obtain ⟨t, htcard, htsum, htmem⟩ := exists_zero_multiset_of_doubling_closed
    x C hpred C.val hCne.card_pos (fun i hi ↦ hi) hzero (Finset.card_le_univ C)
  have htotal : ∑ i, x i = 0 :=
    sum_eq_zero_of_doubling_invariant R x hdouble Finset.univ
      (by simp)
  have hcount : ∑ i : Fin d, t.count i = d := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
    simpa using htcard
  have hweight : ∑ i : Fin d, t.count i • x i = ∑ i, x i := by
    rw [htotal]
    have hsum : ∑ i : Fin d, t.count i • x i = (t.map x).sum := by
      rw [Finset.sum_multiset_map_count]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have : t.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
      simp [this]
    exact hsum.trans htsum
  have hall := hx (fun i ↦ t.count i) hcount hweight
  apply Finset.eq_univ_of_forall
  intro i
  apply htmem i
  exact Multiset.count_pos.mp (by rw [hall i]; omega)

/-- A doubling permutation of a valid tuple of length at least two has
no fixed points; this need not be assumed separately. -/
theorem doubling_apply_ne_of_valid
    {d : ℕ} (hd : 2 ≤ d) {G : Type*} [AddCommGroup G]
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) (i : Fin d) : R i ≠ i := by
  classical
  intro hi
  have hC : Set.BijOn R ({i} : Finset (Fin d)) ({i} : Finset (Fin d)) := by
    simp [hi]
  have hfull := doubling_invariant_eq_univ_of_valid x hx R hdouble
    {i} (Finset.singleton_nonempty i) hC
  have hcard := congrArg Finset.card hfull
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- A doubling permutation of a valid tuple of length at least two is
a single cycle, unconditionally and in an arbitrary abelian group. -/
theorem isCycle_of_valid_doubling
    {d : ℕ} (hd : 2 ≤ d) {G : Type*} [AddCommGroup G]
    (x : Fin d → G) (hx : ValidTuple x) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) : R.IsCycle := by
  classical
  have hRne := doubling_apply_ne_of_valid hd x hx R hdouble
  let a : Fin d := ⟨0, by omega⟩
  let C := (R.cycleOf a).support
  have hcycleOn : R.IsCycleOn C := R.isCycleOn_support_cycleOf a
  have ha : a ∈ C := (Equiv.Perm.mem_support_cycleOf_iff' (hRne a)).2
    (Equiv.Perm.SameCycle.refl R a)
  have hfull : C = Finset.univ :=
    doubling_invariant_eq_univ_of_valid x hx R hdouble C ⟨a, ha⟩ hcycleOn.1
  refine ⟨a, hRne a, ?_⟩
  intro b _hb
  exact hcycleOn.2 ha (by simp [hfull])

end MinModulus
