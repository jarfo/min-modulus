/-
# Three-witness closure for the G1 common-touch problem

This module isolates reusable triangle-omission arguments from the core
two-adic descent machinery.  Three witnesses at a nonzero involution add to a
witness whenever their coefficientwise sum remains at least `-1`; a unique
omission in that sum then closes the common-touch branch of G1.
-/
import MinModulus.Descent

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- A coefficient vector has exactly the omission set `S` when its `-1`
coordinates are precisely the members of `S`. -/
def ExactOmissions (c : Fin n → ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ i, c i = -1 ↔ i ∈ S

/-- Outside an exact omission set, the witness floor upgrades from `-1` to
nonnegativity. -/
theorem nonneg_of_not_mem_exactOmissions {c : Fin n → ℤ} {S : Finset (Fin n)}
    (hfloor : ∀ i, -1 ≤ c i) (homit : ExactOmissions c S)
    {i : Fin n} (hi : i ∉ S) : 0 ≤ c i := by
  have hne : c i ≠ -1 := fun hci => hi ((homit i).1 hci)
  have := hfloor i
  omega

/-- **Exact positive-mass identity.**  If `S` is the exact omission set of a
witness, then the nonnegative coefficients outside `S` sum to `|S|`.  Thus a
witness with `r` omissions has exactly `r` units of positive coefficient
mass, independently of the ambient group and target. -/
theorem witness_compl_sum_eq_card_exactOmissions
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (S : Finset (Fin n)) (homit : ExactOmissions c S) :
    (∑ i ∈ Sᶜ, c i) = (S.card : ℤ) := by
  have hsumS : (∑ i ∈ S, c i) = -(S.card : ℤ) := by
    calc
      (∑ i ∈ S, c i) = ∑ _i ∈ S, (-1 : ℤ) :=
        Finset.sum_congr rfl fun i hi => (homit i).2 hi
      _ = -(S.card : ℤ) := by simp
  have hpartition : (∑ i ∈ S, c i) + (∑ i ∈ Sᶜ, c i) = ∑ i, c i :=
    S.sum_add_sum_compl c
  rw [hsumS, hc.2.2.1] at hpartition
  omega

/-- Every coefficient outside an exact omission set lies between zero and the
number of omissions. -/
theorem witness_coeff_bounds_of_exactOmissions
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (S : Finset (Fin n)) (homit : ExactOmissions c S)
    {i : Fin n} (hi : i ∉ S) : 0 ≤ c i ∧ c i ≤ (S.card : ℤ) := by
  have hnonneg : ∀ j ∈ Sᶜ, 0 ≤ c j := by
    intro j hj
    exact nonneg_of_not_mem_exactOmissions hc.2.1 homit (by simpa using hj)
  have hic : i ∈ Sᶜ := by simpa using hi
  have hle : c i ≤ ∑ j ∈ Sᶜ, c j := Finset.single_le_sum hnonneg hic
  rw [witness_compl_sum_eq_card_exactOmissions g hc S homit] at hle
  exact ⟨nonneg_of_not_mem_exactOmissions hc.2.1 homit hi, hle⟩

/-- A non-omitted coefficient of a witness with exactly two distinct
omissions is `0`, `1`, or `2`. -/
theorem witness_coeff_eq_zero_or_one_or_two_of_exact_pair
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (a b i : Fin n) (hab : a ≠ b)
    (homit : ∀ j, c j = -1 ↔ j = a ∨ j = b)
    (hia : i ≠ a) (hib : i ≠ b) :
    c i = 0 ∨ c i = 1 ∨ c i = 2 := by
  let S : Finset (Fin n) := {a, b}
  have hS : ExactOmissions c S := by
    intro j
    simpa [S, eq_comm] using homit j
  have hiS : i ∉ S := by simp [S, hia, hib]
  have hbounds := witness_coeff_bounds_of_exactOmissions g hc S hS hiS
  have hcard : S.card = 2 := by simp [S, hab]
  rw [hcard] at hbounds
  omega

/-- If a non-omitted coefficient of a two-omission witness equals `2`, it
uses all available positive mass, so every other non-omitted coefficient is
zero. -/
theorem witness_other_eq_zero_of_exact_pair_and_coeff_eq_two
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (a b i : Fin n) (hab : a ≠ b)
    (homit : ∀ j, c j = -1 ↔ j = a ∨ j = b)
    (hia : i ≠ a) (hib : i ≠ b) (hci : c i = 2)
    (j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) (hji : j ≠ i) :
    c j = 0 := by
  let S : Finset (Fin n) := {a, b}
  have hS : ExactOmissions c S := by
    intro k
    simpa [S, eq_comm] using homit k
  have hiS : i ∈ Sᶜ := by simp [S, hia, hib]
  have hjS : j ∈ Sᶜ := by simp [S, hja, hjb]
  have hjErase : j ∈ Sᶜ.erase i := by simp [hjS, hji]
  have hmass := witness_compl_sum_eq_card_exactOmissions g hc S hS
  have hcard : S.card = 2 := by simp [S, hab]
  rw [hcard] at hmass
  have hsplit := Finset.sum_erase_add Sᶜ c hiS
  rw [hmass, hci] at hsplit
  have hrest : (∑ k ∈ Sᶜ.erase i, c k) = 0 := by omega
  have hnonneg : ∀ k ∈ Sᶜ.erase i, 0 ≤ c k := by
    intro k hk
    have hkS : k ∈ Sᶜ := Finset.mem_of_mem_erase hk
    exact nonneg_of_not_mem_exactOmissions hc.2.1 hS (by simpa using hkS)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hrest j hjErase

/-- In an exact triangle of two-omission witnesses, all three coefficients
opposite their omission edges belong to the finite alphabet `{0,1,2}`. -/
theorem triangle_opposite_coefficients_zero_one_or_two
    (g : Fin n → G) {h : G}
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a) :
    (cAB d = 0 ∨ cAB d = 1 ∨ cAB d = 2) ∧
    (cBD a = 0 ∨ cBD a = 1 ∨ cBD a = 2) ∧
    (cDA b = 0 ∨ cDA b = 1 ∨ cDA b = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hcAB a b d hab hAB hda hbd.symm
  · exact witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hcBD b d a hbd hBD hab hda.symm
  · exact witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hcDA d a b hda hDA hbd hab.symm

/-- The all-heavy exact triangle profile `(2,2,2)` is impossible.  Each
opposite `2` exhausts its witness's two units of positive mass, so the three
coefficient vectors are exactly the cyclic vectors that sum to zero; this
contradicts `three_witnesses_sum_ne_zero`. -/
theorem not_triangle_all_opposites_two
    (g : Fin n → G) {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 2) (hBDa : cBD a = 2) (hDAb : cDA b = 2) : False := by
  apply three_witnesses_sum_ne_zero g hh hne hcAB hcBD hcDA
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  by_cases hia : i = a
  · subst i
    have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
    have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
    omega
  by_cases hib : i = b
  · subst i
    have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
    have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
    omega
  by_cases hid : i = d
  · subst i
    have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
    have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
    omega
  have hABi : cAB i = 0 :=
    witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcAB a b d hab hAB
      hda hbd.symm hABd i hia hib hid
  have hBDi : cBD i = 0 :=
    witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcBD b d a hbd hBD
      hab hda.symm hBDa i hib hid hia
  have hDAi : cDA i = 0 :=
    witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcDA d a b hda hDA
      hbd hab.symm hDAb i hid hia hib
  omega

/-- Three witnesses at a nonzero involution are closed under addition whenever
their coordinatewise sum stays above the witness floor `-1`.  Their total
coefficient sum is still zero, and their values add to `3h = h`. -/
theorem witness_three_sum (g : Fin n → G) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {c₁ c₂ c₃ : Fin n → ℤ} (hc₁ : Witness g h c₁)
    (hc₂ : Witness g h c₂) (hc₃ : Witness g h c₃)
    (hfloor : ∀ i, -1 ≤ (c₁ + c₂ + c₃) i) :
    Witness g h (c₁ + c₂ + c₃) := by
  refine ⟨three_witnesses_sum_ne_zero g hh hne hc₁ hc₂ hc₃, hfloor, ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hc₁.2.2.1, hc₂.2.2.1, hc₃.2.2.1, add_zero]
    norm_num
  · have hterm : ∀ i, (c₁ + c₂ + c₃) i • g i
        = c₁ i • g i + c₂ i • g i + c₃ i • g i := by
      intro i
      simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hc₁.2.2.2, hc₂.2.2.2, hc₃.2.2.2, hh, zero_add]

/-- If the admissible sum of three witnesses has a unique omission, that
omitted coordinate is touched by every witness.  This packages the
three-witness closure directly in the common-touch form needed by G1. -/
theorem common_touched_of_three_sum_unique_omission
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {c₁ c₂ c₃ : Fin n → ℤ} (hc₁ : Witness g h c₁)
    (hc₂ : Witness g h c₂) (hc₃ : Witness g h c₃)
    (hfloor : ∀ i, -1 ≤ (c₁ + c₂ + c₃) i)
    (b : Fin n) (hb : (c₁ + c₂ + c₃) b = -1)
    (huniq : ∀ i, (c₁ + c₂ + c₃) i = -1 → i = b) :
    ∀ c : Fin n → ℤ, Witness g h c → c b ≠ 0 := by
  exact common_touched_of_unique_omission g hg hh
    (witness_three_sum g hh hne hc₁ hc₂ hc₃ hfloor) b hb huniq

/-- **Triangle closure, one light opposite.**  Suppose three witnesses have
exact omission pairs `{a,b}`, `{b,d}`, and `{d,a}`.  If the coefficient
opposite `{a,b}` is exactly `1`, while the other two opposite coefficients
are at least `2`, then their sum is a witness whose unique omission is `d`.
Consequently every witness touches `d`, proving the G1 common-touch conclusion
for this entire triangle coefficient pattern (and its permutations). -/
theorem common_touched_of_triangle_one_light_opposite
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hlight : cAB d = 1) (hheavyA : 2 ≤ cBD a)
    (hheavyB : 2 ≤ cDA b) :
    ∀ c : Fin n → ℤ, Witness g h c → c d ≠ 0 := by
  have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
  have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  have hfloor : ∀ i, -1 ≤ (cAB + cBD + cDA) i := by
    intro i
    by_cases hid : i = d
    · subst i
      simp only [Pi.add_apply]
      omega
    by_cases hia : i = a
    · subst i
      simp only [Pi.add_apply]
      omega
    by_cases hib : i = b
    · subst i
      simp only [Pi.add_apply]
      omega
    have hABi : cAB i ≠ -1 := by
      intro hi
      rcases (hAB i).1 hi with rfl | rfl <;> contradiction
    have hBDi : cBD i ≠ -1 := by
      intro hi
      rcases (hBD i).1 hi with rfl | rfl <;> contradiction
    have hDAi : cDA i ≠ -1 := by
      intro hi
      rcases (hDA i).1 hi with rfl | rfl <;> contradiction
    have hABnonneg : 0 ≤ cAB i := by have := hcAB.2.1 i; omega
    have hBDnonneg : 0 ≤ cBD i := by have := hcBD.2.1 i; omega
    have hDAnonneg : 0 ≤ cDA i := by have := hcDA.2.1 i; omega
    simp only [Pi.add_apply]
    omega
  have hd : (cAB + cBD + cDA) d = -1 := by
    simp only [Pi.add_apply]
    omega
  have huniq : ∀ i, (cAB + cBD + cDA) i = -1 → i = d := by
    intro i hi
    by_contra hid
    by_cases hia : i = a
    · subst i
      simp only [Pi.add_apply] at hi
      omega
    by_cases hib : i = b
    · subst i
      simp only [Pi.add_apply] at hi
      omega
    have hABi : cAB i ≠ -1 := by
      intro hci
      rcases (hAB i).1 hci with rfl | rfl <;> contradiction
    have hBDi : cBD i ≠ -1 := by
      intro hci
      rcases (hBD i).1 hci with rfl | rfl <;> contradiction
    have hDAi : cDA i ≠ -1 := by
      intro hci
      rcases (hDA i).1 hci with rfl | rfl <;> contradiction
    have hABnonneg : 0 ≤ cAB i := by have := hcAB.2.1 i; omega
    have hBDnonneg : 0 ≤ cBD i := by have := hcBD.2.1 i; omega
    have hDAnonneg : 0 ≤ cDA i := by have := hcDA.2.1 i; omega
    simp only [Pi.add_apply] at hi
    omega
  exact common_touched_of_three_sum_unique_omission g hg hh hne
    hcAB hcBD hcDA hfloor d hd huniq

end MinModulus
