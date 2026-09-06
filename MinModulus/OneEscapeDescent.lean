import MinModulus.AlmostDoubling
import MinModulus.SIActualDeletion

/-!
# Actual one-escape half descent without an even injectivity hypothesis

An antipodal-pair deletion preserves one-escape affine doubling closure
in the actual half quotient, retaining the exceptional coordinate.
Induction gives 2^n-2^s <= 2^s*q for ALL one-escape tuples. This is the
full exact threshold for s <= floor(log2 n), including every odd and
first-even case; no injectivity hypothesis remains. In EVERY critical
even stratum the same class has actual G1 half deletion.

The uncapped inequality is weaker above the logarithmic cutoff, and
does not exclude the exceptional lift modulus. General G3 extraction
and the three unrestricted global gates remain open.
-/

namespace MinModulus
open Finset

/-- Deleting one of two coordinates identified by an additive map
preserves actual one-escape affine doubling closure, provided the
exception itself is retained. The deleted target is replaced by its
identified partner; no arbitrary smaller tuple is substituted. -/
theorem one_escape_doubling_preserved_by_hom_deletion
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (a j k : Fin (n+1)) (b : G)
    (hja : j ≠ a) (hkj : k ≠ j) (hpair : φ (g j)=φ (g k))
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b) :
    ∃ a' : Fin n, j.succAbove a'=a ∧
      ∀ i, i ≠ a' → ∃ l, φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b := by
  obtain ⟨a',ha'⟩ := Fin.exists_succAbove_eq hja.symm
  refine ⟨a',ha',?_⟩
  intro i hia
  have hi : j.succAbove i ≠ a := by
    intro heq
    exact hia (Fin.succAbove_right_injective (heq.trans ha'.symm))
  obtain ⟨l,hl⟩ := hclosed _ hi
  have hvalue : φ (g l)=2 • φ (g (j.succAbove i))+φ b := by
    rw [hl,map_add,map_nsmul]
  by_cases hlj : l=j
  · obtain ⟨k',hk'⟩ := Fin.exists_succAbove_eq hkj
    refine ⟨k',?_⟩
    rw [hk',← hpair]
    simpa only [hlj] using hvalue
  · obtain ⟨l',hl'⟩ := Fin.exists_succAbove_eq hlj
    exact ⟨l',by rw [hl']; exact hvalue⟩

/-- Either member of an antipodal coordinate pair can be deleted in
the ACTUAL half quotient. The stated orientation deletes j. -/
theorem validTuple_actual_half_of_doubled_collision
    {n M : ℕ} [NeZero M] (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (j k : Fin (n+1)) (hkj : k ≠ j) (hdouble : 2 • g j=2 • g k) :
    ValidTuple (fun i : Fin n ↦ ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))) := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hzero : (g k-g j)+(g k-g j)=0 := by
    simp only [two_nsmul] at hdouble
    calc
      _=(g k+g k)-(g j+g j) := by abel
      _=0 := sub_eq_zero.mpr hdouble.symm
  have hpair : g k-g j=(M : ZMod (2*M)) := by
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero rfl _ hzero with hz | hh
    · exact False.elim (hkj (validTuple_injective g hg (sub_eq_zero.mp hz)))
    · exact hh
  have hq := pair_descent g hg (half_add_half rfl) (half_ne_zero rfl hM) hpair
  have hv := validTuple_comp hq (quotZMultiplesEquivZMod (dvd_mul_left M 2)).toAddMonoidHom
    (quotZMultiplesEquivZMod (dvd_mul_left M 2)).injective
  exact hv

/-- A doubling collision gives a specified actual valid half deletion
which retains the exception and its one-escape closure. -/
theorem exists_actual_one_escape_half_of_doubling_collision
    {n N M : ℕ} [NeZero M] (hNM : N=2*M)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (a : Fin (n+1)) (b : ZMod N)
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b)
    (u v : Fin (n+1)) (huv : u ≠ v) (hdouble : 2 • g u=2 • g v) :
    ∃ j : Fin (n+1), j ≠ a ∧ ∃ a' : Fin n, j.succAbove a'=a ∧
      ValidTuple (fun i : Fin n ↦ ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))) ∧
      ∀ i, i ≠ a' → ∃ l,
        ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove l))=
        2 • ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))+
        ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) b := by
  subst N
  have hchoose : ∃ j k : Fin (n+1), j ≠ a ∧ k ≠ j ∧ 2 • g j=2 • g k := by
    by_cases hua : u=a
    · exact ⟨v,u,by simpa only [← hua] using huv.symm,huv,hdouble.symm⟩
    · exact ⟨u,v,hua,huv.symm,hdouble⟩
  obtain ⟨j,k,hja,hkj,hjk⟩ := hchoose
  let π := (ZMod.castHom (dvd_mul_left M 2) (ZMod M)).toAddMonoidHom
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hzero : (g j-g k)+(g j-g k)=0 := by
    simp only [two_nsmul] at hjk
    calc
      _=(g j+g j)-(g k+g k) := by abel
      _=0 := sub_eq_zero.mpr hjk
  have hpair : π (g j)=π (g k) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero rfl _ hzero with hz | hh
    · simp [hz]
    · simp [hh,π]
  obtain ⟨a',ha',hc⟩ := one_escape_doubling_preserved_by_hom_deletion π g a j k b hja hkj hpair hclosed
  exact ⟨j,hja,a',ha',validTuple_actual_half_of_doubled_collision g hg j k hkj hjk,hc⟩

/-- Iterated ACTUAL half deletion proves the uncapped two-adic bound
for every one-escape tuple. No doubling injectivity hypothesis remains.
Above the logarithmic cutoff this is deliberately weaker than G3. -/
theorem uncapped_stratum_lower_bound_of_valid_one_escape_doubling
    {n s q : ℕ} (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin n) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b) : 2^n-2^s ≤ 2^s*q := by
  induction s generalizing n with
  | zero =>
    have h := odd_lower_bound_of_valid_one_escape_doubling (by simpa using hq : Odd (2^0*q)) g hg a b hclosed
    simpa only [pow_zero] using h
  | succ s ih =>
    have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
    have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
    by_cases hn : 2 ≤ n
    · by_cases hinj : Function.Injective (fun i ↦ 2 • g i)
      · have hbound := stratum_lower_bound_of_valid_one_escape_doubling hn hq g hg a b
          (fun i _ j _ heq ↦ hinj heq) hclosed
        have hp : 2^min (s+1) (Nat.log 2 n) ≤ 2^(s+1) :=
          Nat.pow_le_pow_right (by omega) (min_le_left _ _)
        exact (Nat.sub_le_sub_left hp (2^n)).trans hbound
      · rw [Function.Injective] at hinj
        push Not at hinj
        obtain ⟨u,v,heq,huv⟩ := hinj
        cases n with
        | zero => omega
        | succ n =>
          letI : NeZero (2^s*q) := ⟨hM.ne'⟩
          obtain ⟨j,_,a',_,hv,hc⟩ :=
            exists_actual_one_escape_half_of_doubling_collision hN g hg a b hclosed u v huv heq
          have hb := ih _ hv a' _ hc
          have ht := Nat.mul_le_mul_left 2 hb
          simpa only [pow_succ',Nat.mul_sub_left_distrib,mul_assoc] using ht
    · have hnle : n ≤ 1 := by omega
      have hpow : 2^n ≤ 2 := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hnle
      have hpow2 : 2 ≤ 2^(s+1) := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ s+1)
      omega

/-- Every one-escape tuple satisfies the FULL exact-stratum threshold
up to and including the logarithmic cutoff, without injectivity. -/
theorem stratum_lower_bound_of_valid_one_escape_low_stratum
    {n s q : ℕ} (hq : Odd q) (hs : s ≤ Nat.log 2 n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin n) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b) : stratumBound n s ≤ 2^s*q := by
  simpa only [stratumBound,min_eq_left hs] using
    uncapped_stratum_lower_bound_of_valid_one_escape_doubling hq g hg a b hclosed

/-- The actual G1 deletion conclusion for ALL critical one-escape
tuples, at EVERY even stratum. A collision gives actual half deletion;
without one, the almost-doubling bound contradicts criticality. -/
theorem admitsValidTuple_half_of_critical_one_escape_doubling
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (a : Fin (n+1)) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1)) :
    AdmitsValidTuple n (2^s*q) := by
  by_cases hi : Function.Injective (fun i ↦ 2 • g i)
  · have hbound := stratum_lower_bound_of_valid_one_escape_doubling (by omega) hq g hg a b
      (fun i _ j _ heq ↦ hi heq) hclosed
    exact False.elim ((not_lt_of_ge hbound) hcritical)
  · rw [Function.Injective] at hi
    push Not at hi
    obtain ⟨u,v,heq,huv⟩ := hi
    have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
    letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
    obtain ⟨j,_,a',_,hv,_⟩ :=
      exists_actual_one_escape_half_of_doubling_collision hN g hg a b hclosed u v huv heq
    exact ⟨_,hv⟩

/-- Direct full global bound for ALL one-escape tuples in strata up
to the logarithmic cutoff. Higher-stratum G3 is not assumed away. -/
theorem global_lower_bound_of_valid_one_escape_low_stratum
    {n s q : ℕ} (hq : Odd q) (hs : s ≤ Nat.log 2 n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin n) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ l, g l=2 • g i+b) : globalBound n ≤ 2^s*q := by
  have hp : 2^s ≤ 2^Nat.log 2 n := Nat.pow_le_pow_right (by omega) hs
  exact (Nat.sub_le_sub_left hp (2^n)).trans
    (uncapped_stratum_lower_bound_of_valid_one_escape_doubling hq g hg a b hclosed)

end MinModulus
