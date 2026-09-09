import MinModulus.BoundedFamilyContinuation

/-! An actual nonempty affine cycle gives all original bounds once
n >= 5*r+1, where r bounds the escaping coordinates at that shift.
The first growth layer excludes singleton cycles in this range; the
second forces a half-sized cycle directly. This sharpens the earlier
uniform 6*(r+1) condition. Every original counterexample with an actual
cycle therefore satisfies n < 5*r+1. No doubling injectivity or failed
half-descent hypothesis is needed. All unrestricted gates remain open. -/

namespace MinModulus
open Finset

/-- The two-layer budget forces a half-sized actual cycle as soon as
the dimension is at least five times the actual escape count plus one. -/
theorem half_sized_cycle_of_linear_escape_threshold
    {m k N : ℕ} [NeZero N] (hm : 0 < m) (hn : 3 ≤ m+k)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card+1 ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2 ≤ m ∧ k ≤ m+1 := by
  have hout := outside_le_affine_cycle_add_escape_count hm g hg A b hclosed E R hcycle
  have hm2 : 2 ≤ m := by omega
  have h := layer_budget_of_valid_few_escape_affine_cycle hm2 g hg A b hclosed E R hcycle 2
  norm_num at h
  exact ⟨hm2,by omega⟩

/-- The original global bound at the sharper dimension-versus-escape threshold. -/
theorem global_lower_bound_of_linear_cycle_escape_threshold
    {m k N : ℕ} [NeZero N] (hm : 0 < m) (hn : 3 ≤ m+k)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card+1 ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N := by
  obtain ⟨hm2,hhalf⟩ := half_sized_cycle_of_linear_escape_threshold hm hn g hg A b hclosed hcount E R hcycle
  exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm2 hhalf g hg E b R hcycle

/-- Every original exact stratum at the same sharper escape threshold. -/
theorem stratum_lower_bound_of_linear_cycle_escape_threshold
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 3 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card+1 ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hm2,hhalf⟩ := half_sized_cycle_of_linear_escape_threshold hm hn g hg A b hclosed hcount E R hcycle
  exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm2 hhalf hq g hg E b R hcycle

/-- At any shift supporting an actual cycle, an original global counterexample
must have more than the linear threshold number of escaping coordinates. -/
theorem linear_escapes_of_global_counterexample_with_affine_cycle
    {n m N : ℕ} [NeZero N] (hn : 3 ≤ n) (hm : 0 < m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (b : ZMod N) (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) :
    n < 5*(Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card+1 := by
  classical
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra hh
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  by_contra hh
  have hcount : 5*A.card+1 ≤ n := by change ¬ n < 5*A.card+1 at hh; omega
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  have hbound := global_lower_bound_of_linear_cycle_escape_threshold hm hn g hg A b hclosed hcount E R
    (by simpa only [hE] using hcycle)
  omega

/-- At any shift supporting an actual cycle, an original stratum counterexample
must have more than the linear threshold number of escaping coordinates. -/
theorem linear_escapes_of_stratum_counterexample_with_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hn : 3 ≤ n) (hm : 0 < m)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (b : ZMod (2^s*q)) (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) :
    n < 5*(Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card+1 := by
  classical
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra hh
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  by_contra hh
  have hcount : 5*A.card+1 ≤ n := by change ¬ n < 5*A.card+1 at hh; omega
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  have hbound := stratum_lower_bound_of_linear_cycle_escape_threshold hq hm hn g hg A b hclosed hcount E R
    (by simpa only [hE] using hcycle)
  omega

/-- Every original exceptional G3 tuple has the same cycle-conditioned
linear escape lower bound, including the possible doubled collision. -/
theorem linear_escapes_of_exceptional_tuple_with_affine_cycle
    {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (b : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) :
    n < 5*(Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card+1 := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact linear_escapes_of_global_counterexample_with_affine_cycle hn hm g hg hsmall b e R hcycle

/-- Direct original G3 exclusion at the sharper scalar cycle threshold. -/
theorem not_validTuple_exceptional_of_linear_cycle_escape_threshold
    {n m : ℕ} (hn : 3 ≤ n) (hm : 0 < m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b)
    (hcount : 5*(Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card+1 ≤ n) : ¬ ValidTuple g := by
  intro hg
  have h := linear_escapes_of_exceptional_tuple_with_affine_cycle hn hm hnpow g hg b e R hcycle
  omega

end MinModulus
