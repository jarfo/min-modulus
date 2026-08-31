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

/-- A difference `g a - g b = h` is represented by a witness with the unique
omission `b`.  This is the common algebraic core of pair descent. -/
theorem exists_pair_difference_witness (g : Fin n → G) {h : G}
    {a b : Fin n} (hab : a ≠ b) (hval : g a - g b = h) :
    ∃ c : Fin n → ℤ, Witness g h c ∧ ExactOmissions c {b} := by
  let c : Fin n → ℤ :=
    fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0)
  have hca : c a = 1 := by simp [c, hab]
  have hcb : c b = -1 := by simp [c, Ne.symm hab]
  refine ⟨c, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro hc
      have := congrFun hc a
      rw [hca, Pi.zero_apply] at this
      omega
    · intro i
      by_cases hia : i = a
      · subst i; rw [hca]; omega
      by_cases hib : i = b
      · subst i; rw [hcb]
      · simp [c, hia, hib]
    · rw [show (∑ i, c i) =
          (∑ i, if i = a then (1 : ℤ) else 0) -
            ∑ i, if i = b then (1 : ℤ) else 0 by
        rw [Finset.sum_sub_distrib]]
      rw [Finset.sum_ite_eq' univ a fun _ => (1 : ℤ),
        Finset.sum_ite_eq' univ b fun _ => (1 : ℤ)]
      simp
    · have hterm : ∀ i, c i • g i =
          (if i = a then g i else 0) - (if i = b then g i else 0) := by
        intro i
        simp only [c, sub_smul, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' univ a g, Finset.sum_ite_eq' univ b g]
      simpa using hval
  · intro i
    constructor
    · intro hi
      by_cases hib : i = b
      · simp [hib]
      by_cases hia : i = a
      · subst i
        rw [hca] at hi
        omega
      simp [c, hia, hib] at hi
    · intro hi
      have hib : i = b := by simpa using hi
      subst i
      exact hcb

/-- Validity forces the coordinates of a tuple to be distinct. -/
theorem validTuple_injective (g : Fin n → G) (hg : ValidTuple g) :
    Function.Injective g := by
  intro a b hgab
  by_contra hab
  obtain ⟨c, hc, _⟩ := exists_pair_difference_witness (h := (0 : G))
    g hab (by simp [hgab])
  exact (validTuple_iff_no_zero_witness g).mp hg c hc

/-- A pair difference equal to the distinguished involution gives the G1
common-touch conclusion at the omitted endpoint. -/
theorem common_touched_of_pair_difference (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    {a b : Fin n} (hval : g a - g b = h) :
    ∀ c : Fin n → ℤ, Witness g h c → c b ≠ 0 := by
  have hab : a ≠ b := by
    intro hab
    subst b
    rw [sub_self] at hval
    exact hne hval.symm
  obtain ⟨c, hc, homit⟩ := exists_pair_difference_witness g hab hval
  exact common_touched_of_unique_omission g hg hh hc b
    ((homit b).2 (by simp)) (fun i hi => by simpa using (homit i).1 hi)

/-- In a group with unique nonzero involution `h`, equality of two doubled
tuple coordinates forces their difference to be `h` (equality itself is
excluded by validity), and hence gives the G1 common-touch conclusion. -/
theorem common_touched_of_two_smul_eq
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {b e : Fin n} (hbe : b ≠ e)
    (hdoubles : (2 : ℤ) • g b = (2 : ℤ) • g e) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  let x : G := g b - g e
  have hx : x + x = 0 := by
    calc
      x + x = (2 : ℤ) • g b - (2 : ℤ) • g e := by
        simp only [x, two_zsmul]
        abel
      _ = 0 := by rw [hdoubles, sub_self]
  rcases hunique x hx with hx0 | hxh
  · have hgbe : g b = g e := sub_eq_zero.mp hx0
    exact absurd (validTuple_injective g hg hgbe) hbe
  · exact ⟨e, common_touched_of_pair_difference g hg hh hne hxh⟩

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

/-- If a two-omission witness has coefficient `1` at one non-omitted
coordinate `d`, its remaining unit of positive mass occurs as coefficient
`1` at a second coordinate `e`; all other non-omitted coordinates vanish. -/
theorem exists_companion_one_of_exact_pair_coeff_one
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (a b d : Fin n) (hab : a ≠ b)
    (homit : ∀ j, c j = -1 ↔ j = a ∨ j = b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c d = 1) :
    ∃ e : Fin n, e ≠ a ∧ e ≠ b ∧ e ≠ d ∧ c e = 1 ∧
      ∀ j : Fin n, j ≠ a → j ≠ b → j ≠ d → j ≠ e → c j = 0 := by
  let S : Finset (Fin n) := {a, b}
  have hS : ExactOmissions c S := by
    intro j
    simpa [S, eq_comm] using homit j
  have hdS : d ∈ Sᶜ := by simp [S, hda, hdb]
  have hmass := witness_compl_sum_eq_card_exactOmissions g hc S hS
  have hcard : S.card = 2 := by simp [S, hab]
  rw [hcard] at hmass
  have hsplit := Finset.sum_erase_add Sᶜ c hdS
  rw [hmass, hcd] at hsplit
  have hrest : (∑ i ∈ Sᶜ.erase d, c i) = 1 := by omega
  have hexists : ∃ e ∈ Sᶜ.erase d, c e ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have : (∑ i ∈ Sᶜ.erase d, c i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hnone i hi
    omega
  obtain ⟨e, heRest, heNonzero⟩ := hexists
  have heS : e ∈ Sᶜ := Finset.mem_of_mem_erase heRest
  have hed : e ≠ d := Finset.ne_of_mem_erase heRest
  have heab : e ≠ a ∧ e ≠ b := by simpa [S] using heS
  have hea : e ≠ a := heab.1
  have heb : e ≠ b := heab.2
  have hnonneg : ∀ i ∈ Sᶜ.erase d, 0 ≤ c i := by
    intro i hi
    have hiS : i ∈ Sᶜ := Finset.mem_of_mem_erase hi
    exact nonneg_of_not_mem_exactOmissions hc.2.1 hS (by simpa using hiS)
  have hceLe : c e ≤ ∑ i ∈ Sᶜ.erase d, c i :=
    Finset.single_le_sum hnonneg heRest
  rw [hrest] at hceLe
  have hceNonneg := hnonneg e heRest
  have hce : c e = 1 := by omega
  refine ⟨e, hea, heb, hed, hce, ?_⟩
  intro j hja hjb hjd hje
  have hjS : j ∈ Sᶜ := by simp [S, hja, hjb]
  have hjRest : j ∈ (Sᶜ.erase d).erase e := by simp [hjS, hjd, hje]
  have heRest' : e ∈ Sᶜ.erase d := heRest
  have hsplit' := Finset.sum_erase_add (Sᶜ.erase d) c heRest'
  rw [hrest, hce] at hsplit'
  have htail : (∑ i ∈ (Sᶜ.erase d).erase e, c i) = 0 := by omega
  have hnonneg' : ∀ i ∈ (Sᶜ.erase d).erase e, 0 ≤ c i := by
    intro i hi
    exact hnonneg i (Finset.mem_of_mem_erase hi)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg').1 htail j hjRest

/-- For two witnesses with the same exact omission pair, suppose one has
opposite coefficient `2` at `b` while the other has coefficient `0` there.
Validity forces the latter witness to concentrate its two units of positive
mass at some other coordinate `e`.  Otherwise their difference would be a
forbidden witness at target zero with all coefficients at least `-1`. -/
theorem exists_coeff_two_of_same_exact_pair_zero_two
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    {cZero cTwo : Fin n → ℤ} (hcZero : Witness g h cZero)
    (hcTwo : Witness g h cTwo) (a d b : Fin n)
    (had : a ≠ d) (hba : b ≠ a) (hbd : b ≠ d)
    (hZero : ∀ i, cZero i = -1 ↔ i = a ∨ i = d)
    (hTwo : ∀ i, cTwo i = -1 ↔ i = a ∨ i = d)
    (hZeroB : cZero b = 0) (hTwoB : cTwo b = 2) :
    ∃ e : Fin n, e ≠ a ∧ e ≠ d ∧ cZero e = 2 := by
  by_contra hnone
  have hnotwo : ∀ e : Fin n, e ≠ a → e ≠ d → cZero e ≠ 2 := by
    intro e hea hed heTwo
    exact hnone ⟨e, hea, hed, heTwo⟩
  apply (validTuple_iff_no_zero_witness g).mp hg (cTwo - cZero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hb := congrFun hzero b
    simp only [Pi.sub_apply, Pi.zero_apply, hTwoB, hZeroB] at hb
    omega
  · intro i
    simp only [Pi.sub_apply]
    by_cases hia : i = a
    · subst i
      have hZeroA : cZero a = -1 := (hZero a).2 (Or.inl rfl)
      have hTwoA : cTwo a = -1 := (hTwo a).2 (Or.inl rfl)
      omega
    by_cases hid : i = d
    · subst i
      have hZeroD : cZero d = -1 := (hZero d).2 (Or.inr rfl)
      have hTwoD : cTwo d = -1 := (hTwo d).2 (Or.inr rfl)
      omega
    by_cases hib : i = b
    · subst i
      omega
    have hZeroRange := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hcZero a d i had hZero hia hid
    have hZeroLe : cZero i ≤ 1 := by
      have := hnotwo i hia hid
      rcases hZeroRange with h0 | h1 | h2 <;> omega
    have hTwoI : cTwo i = 0 :=
      witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcTwo a d b had
        hTwo hba hbd hTwoB i hia hid hib
    omega
  · simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hcTwo.2.2.1, hcZero.2.2.1, sub_self]
  · have hterm : ∀ i, (cTwo - cZero) i • g i =
        cTwo i • g i - cZero i • g i := by
      intro i
      simp only [Pi.sub_apply, sub_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      hcTwo.2.2.2, hcZero.2.2.2, sub_self]

/-- Two witnesses with the same exact omission pair and concentrated positive
mass `2` at coordinates `b` and `e` force `2 • g b = 2 • g e`. -/
theorem two_smul_eq_of_same_exact_pair_coeff_two
    (g : Fin n → G) {h : G}
    {cB cE : Fin n → ℤ} (hcB : Witness g h cB)
    (hcE : Witness g h cE) (a d b e : Fin n)
    (had : a ≠ d) (hba : b ≠ a) (hbd : b ≠ d)
    (hea : e ≠ a) (hed : e ≠ d)
    (hB : ∀ i, cB i = -1 ↔ i = a ∨ i = d)
    (hE : ∀ i, cE i = -1 ↔ i = a ∨ i = d)
    (hcBb : cB b = 2) (hcEe : cE e = 2) :
    (2 : ℤ) • g b = (2 : ℤ) • g e := by
  by_cases hbe : b = e
  · subst e
    rfl
  have hcBe : cB e = 0 :=
    witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcB a d b had hB
      hba hbd hcBb e hea hed (Ne.symm hbe)
  have hcEb : cE b = 0 :=
    witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcE a d e had hE
      hea hed hcEe b hba hbd hbe
  have hweighted : (∑ i, (cB - cE) i • g i) = 0 := by
    have hterm : ∀ i, (cB - cE) i • g i = cB i • g i - cE i • g i := by
      intro i
      simp only [Pi.sub_apply, sub_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      hcB.2.2.2, hcE.2.2.2, sub_self]
  have hterm : ∀ i, (cB - cE) i • g i =
      (if i = b then (2 : ℤ) • g i else 0) -
        (if i = e then (2 : ℤ) • g i else 0) := by
    intro i
    by_cases hia : i = a
    · subst i
      have hcBa : cB a = -1 := (hB a).2 (Or.inl rfl)
      have hcEa : cE a = -1 := (hE a).2 (Or.inl rfl)
      simp [hcBa, hcEa, Ne.symm hba, Ne.symm hea]
    by_cases hid : i = d
    · subst i
      have hcBd : cB d = -1 := (hB d).2 (Or.inr rfl)
      have hcEd : cE d = -1 := (hE d).2 (Or.inr rfl)
      simp [hcBd, hcEd, Ne.symm hbd, Ne.symm hed]
    by_cases hib : i = b
    · subst i
      simp only [Pi.sub_apply, hcBb, hcEb, sub_zero, if_neg hbe]
      all_goals simp
    by_cases hie : i = e
    · subst i
      simp only [Pi.sub_apply, hcBe, hcEe, zero_sub, if_neg (Ne.symm hbe)]
      all_goals simp
    have hcBi : cB i = 0 :=
      witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcB a d b had hB
        hba hbd hcBb i hia hid hib
    have hcEi : cE i = 0 :=
      witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcE a d e had hE
        hea hed hcEe i hia hid hie
    simp [hcBi, hcEi, hib, hie]
  have hformula : (∑ i, (cB - cE) i • g i) =
      (2 : ℤ) • g b - (2 : ℤ) • g e := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' univ b fun i => (2 : ℤ) • g i,
      Finset.sum_ite_eq' univ e fun i => (2 : ℤ) • g i]
    simp
  rw [hformula] at hweighted
  exact sub_eq_zero.mp hweighted

/-- Two adjacent all-one triangle witnesses with the same companion
coordinate force equality between the doubles of their common omitted vertex
and that companion. -/
theorem two_smul_eq_of_adjacent_triangle_same_companion
    (g : Fin n → G) {h : G} (hh : h + h = 0)
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r e : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 1) (hQRp : cQR p = 1)
    (hep : e ≠ p) (heq : e ≠ q) (her : e ≠ r)
    (hPQe : cPQ e = 1) (hQRe : cQR e = 1)
    (hPQzero : ∀ i, i ≠ p → i ≠ q → i ≠ r → i ≠ e → cPQ i = 0)
    (hQRzero : ∀ i, i ≠ q → i ≠ r → i ≠ p → i ≠ e → cQR i = 0) :
    (2 : ℤ) • g q = (2 : ℤ) • g e := by
  have hweighted : (∑ i, (cPQ + cQR) i • g i) = 0 := by
    have hterm : ∀ i, (cPQ + cQR) i • g i =
        cPQ i • g i + cQR i • g i := by
      intro i
      simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_add_distrib, hcPQ.2.2.2, hcQR.2.2.2, hh]
  have hterm : ∀ i, (cPQ + cQR) i • g i =
      (if i = e then (2 : ℤ) • g i else 0) -
        (if i = q then (2 : ℤ) • g i else 0) := by
    intro i
    by_cases hip : i = p
    · subst i
      have hPQp : cPQ p = -1 := (hPQ p).2 (Or.inl rfl)
      simp [hPQp, hQRp, hpq, Ne.symm hep]
    by_cases hiq : i = q
    · subst i
      have hPQq : cPQ q = -1 := (hPQ q).2 (Or.inr rfl)
      have hQRq : cQR q = -1 := (hQR q).2 (Or.inl rfl)
      simp [hPQq, hQRq, Ne.symm heq]
    by_cases hir : i = r
    · subst i
      have hQRr : cQR r = -1 := (hQR r).2 (Or.inr rfl)
      simp [hPQr, hQRr, hqr.symm, Ne.symm her]
    by_cases hie : i = e
    · subst i
      simp [hPQe, hQRe, heq]
    have hPQ0 := hPQzero i hip hiq hir hie
    have hQR0 := hQRzero i hiq hir hip hie
    simp [hPQ0, hQR0, hiq, hie]
  have hformula : (∑ i, (cPQ + cQR) i • g i) =
      (2 : ℤ) • g e - (2 : ℤ) • g q := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' univ e fun i => (2 : ℤ) • g i,
      Finset.sum_ite_eq' univ q fun i => (2 : ℤ) • g i]
    simp
  rw [hformula] at hweighted
  exact (sub_eq_zero.mp hweighted).symm

/-- If `h` is the unique nonzero element killed by doubling, a zero-opposite
witness and a coefficient-`2` witness with the same exact omission pair force
a pair difference equal to `h`.  Hence some coordinate is touched by every
witness, closing this G1 obstruction class. -/
theorem common_touched_of_same_exact_pair_zero_two
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {cZero cTwo : Fin n → ℤ} (hcZero : Witness g h cZero)
    (hcTwo : Witness g h cTwo) (a d b : Fin n)
    (had : a ≠ d) (hba : b ≠ a) (hbd : b ≠ d)
    (hZero : ∀ i, cZero i = -1 ↔ i = a ∨ i = d)
    (hTwo : ∀ i, cTwo i = -1 ↔ i = a ∨ i = d)
    (hZeroB : cZero b = 0) (hTwoB : cTwo b = 2) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  obtain ⟨e, hea, hed, hZeroE⟩ :=
    exists_coeff_two_of_same_exact_pair_zero_two g hg hcZero hcTwo a d b
      had hba hbd hZero hTwo hZeroB hTwoB
  have hbe : b ≠ e := by
    intro hbe
    subst e
    rw [hZeroB] at hZeroE
    omega
  have hdoubles : (2 : ℤ) • g b = (2 : ℤ) • g e :=
    two_smul_eq_of_same_exact_pair_coeff_two g hcTwo hcZero a d b e
      had hba hbd hea hed hTwo hZero hTwoB hZeroE
  let x : G := g b - g e
  have hx : x + x = 0 := by
    calc
      x + x = (2 : ℤ) • g b - (2 : ℤ) • g e := by
        simp only [x, two_zsmul]
        abel
      _ = 0 := by rw [hdoubles, sub_self]
  rcases hunique x hx with hx0 | hxh
  · have hgbe : g b = g e := sub_eq_zero.mp hx0
    exact absurd (validTuple_injective g hg hgbe) hbe
  · exact ⟨e, common_touched_of_pair_difference g hg hh hne hxh⟩

/-- The half-modulus element is the unique nonzero involution in an even
cyclic group `ZMod N` with `N = 2*M`. -/
theorem zmod_eq_zero_or_half_of_add_self_eq_zero
    {N M : ℕ} [NeZero N] (hN : N = 2 * M)
    (x : ZMod N) (hx : x + x = 0) : x = 0 ∨ x = (M : ZMod N) := by
  have hneg : -x = x := by
    rw [neg_eq_iff_add_eq_zero]
    exact hx
  rcases (ZMod.neg_eq_self_iff x).mp hneg with hx0 | hxval
  · exact Or.inl hx0
  · right
    have hval : x.val = M := by omega
    calc
      x = (x.val : ZMod N) := x.natCast_zmod_val.symm
      _ = (M : ZMod N) := by rw [hval]

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

/-- A witness at an involution remains a witness after negation provided all
its coefficients are at most `1`.  Together with the witness floor, this is
the symmetric coefficient window `[-1,1]`. -/
theorem witness_neg_of_le_one (g : Fin n → G) {h : G}
    (hh : h + h = 0) {c : Fin n → ℤ} (hc : Witness g h c)
    (hle : ∀ i, c i ≤ 1) : Witness g h (-c) := by
  have hneg : -h = h := by
    rw [neg_eq_iff_add_eq_zero]
    exact hh
  refine ⟨neg_ne_zero.mpr hc.1, ?_, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]
    have := hle i
    omega
  · simp only [Pi.neg_apply]
    rw [Finset.sum_neg_distrib, hc.2.2.1, neg_zero]
  · have hterm : ∀ i, (-c) i • g i = -(c i • g i) := by
      intro i
      simp only [Pi.neg_apply, neg_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_neg_distrib, hc.2.2.2, hneg]

/-- Three exact two-omission witnesses on a triangle have an admissible sum
whenever all three opposite coefficients are positive. -/
theorem witness_triangle_sum_of_positive_opposites
    (g : Fin n → G) {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : 1 ≤ cAB d) (hBDa : 1 ≤ cBD a) (hDAb : 1 ≤ cDA b) :
    Witness g h (cAB + cBD + cDA) := by
  apply witness_three_sum g hh hne hcAB hcBD hcDA
  intro i
  by_cases hid : i = d
  · subst i
    have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
    have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
    simp only [Pi.add_apply]
    omega
  by_cases hia : i = a
  · subst i
    have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
    have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
    simp only [Pi.add_apply]
    omega
  by_cases hib : i = b
  · subst i
    have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
    have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
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

/-- A residual positive triangle with opposite profile `(1,1,2)` sums to a
new witness on the heavy omission edge whose opposite coefficient is zero.
Thus this profile reduces canonically to the zero-opposite obstruction class. -/
theorem triangle_one_one_two_sum_witness_zero_opposite
    (g : Fin n → G) {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 2) :
    ∃ cZero : Fin n → ℤ, Witness g h cZero ∧
      ExactOmissions cZero {d, a} ∧ cZero b = 0 := by
  let cZero := cAB + cBD + cDA
  have hcZero : Witness g h cZero := by
    exact witness_triangle_sum_of_positive_opposites g hh hne hcAB hcBD hcDA
      a b d hAB hBD hDA (by omega) (by omega) (by omega)
  have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
  have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  refine ⟨cZero, hcZero, ?_, ?_⟩
  · intro i
    constructor
    · intro hi
      by_cases hid : i = d
      · subst i
        simp
      by_cases hia : i = a
      · subst i
        simp
      by_cases hib : i = b
      · subst i
        simp only [cZero, Pi.add_apply] at hi
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
      simp only [cZero, Pi.add_apply] at hi
      omega
    · intro hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp only [cZero, Pi.add_apply] <;> omega
  · simp only [cZero, Pi.add_apply]
    omega

/-- In a group with unique nonzero involution `h`, the residual triangle
profile `(1,1,2)` already closes G1.  Its three-witness sum gives a
zero-opposite witness on the heavy edge, and the same-edge zero/two theorem
then forces a pair difference equal to `h`. -/
theorem common_touched_of_triangle_one_one_two
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 2) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  obtain ⟨cZero, hcZero, hZero, hZeroB⟩ :=
    triangle_one_one_two_sum_witness_zero_opposite g hh hne hcAB hcBD hcDA
      a b d hab hbd hda hAB hBD hDA hABd hBDa hDAb
  have hZero' : ∀ i, cZero i = -1 ↔ i = d ∨ i = a := by
    intro i
    simpa using hZero i
  exact common_touched_of_same_exact_pair_zero_two g hg hh hne hunique
    hcZero hcDA d a b hda hbd hab.symm hZero' hDA hZeroB hDAb

/-- Cyclic specialization: in `ZMod (2*M)`, every exact omission triangle
with opposite profile `(1,1,2)` has a coordinate touched by all half-witnesses. -/
theorem common_touched_of_triangle_one_one_two_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 2) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g (M : ZMod N) c → c j ≠ 0 := by
  exact common_touched_of_triangle_one_one_two g hg
    (half_add_half hN) (half_ne_zero hN hM)
    (fun x hx => zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
    hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hABd hBDa hDAb

/-- A residual positive triangle with opposite profile `(1,1,1)` sums to a
witness whose exact omission set is the three triangle vertices. -/
theorem triangle_all_one_sum_witness_exact_triple
    (g : Fin n → G) {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 1) :
    ∃ cTriple : Fin n → ℤ, Witness g h cTriple ∧
      ExactOmissions cTriple {a, b, d} := by
  let cTriple := cAB + cBD + cDA
  have hcTriple : Witness g h cTriple := by
    exact witness_triangle_sum_of_positive_opposites g hh hne hcAB hcBD hcDA
      a b d hAB hBD hDA (by omega) (by omega) (by omega)
  have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
  have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  refine ⟨cTriple, hcTriple, ?_⟩
  intro i
  constructor
  · intro hi
    by_cases hia : i = a
    · subst i
      simp
    by_cases hib : i = b
    · subst i
      simp
    by_cases hid : i = d
    · subst i
      simp
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
    simp only [cTriple, Pi.add_apply] at hi
    omega
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp only [cTriple, Pi.add_apply] <;> omega

/-- In a group with unique nonzero involution, the all-one exact omission
triangle closes G1.  Each edge witness has one companion `+1` coordinate.  A
repeated companion gives equal doubles and hence an involution difference.  If
the three companions are distinct, the summed exact-triple witness lies in
the symmetric window `[-1,1]`; its negative is another witness, and combining
it with an edge witness contradicts validity. -/
theorem common_touched_of_triangle_all_one
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 1) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  obtain ⟨x, hxa, hxb, hxd, hABx, hABzero⟩ :=
    exists_companion_one_of_exact_pair_coeff_one g hcAB a b d hab hAB
      hda hbd.symm hABd
  obtain ⟨y, hyb, hyd, hya, hBDy, hBDzero⟩ :=
    exists_companion_one_of_exact_pair_coeff_one g hcBD b d a hbd hBD
      hab hda.symm hBDa
  obtain ⟨z, hzd, hza, hzb, hDAz, hDAzero⟩ :=
    exists_companion_one_of_exact_pair_coeff_one g hcDA d a b hda hDA
      hbd hab.symm hDAb
  by_cases hxy : x = y
  · have hBDx : cBD x = 1 := by simpa [hxy] using hBDy
    have hBDzeroX : ∀ i, i ≠ b → i ≠ d → i ≠ a → i ≠ x → cBD i = 0 := by
      simpa [hxy] using hBDzero
    have hdoubles : (2 : ℤ) • g b = (2 : ℤ) • g x :=
      two_smul_eq_of_adjacent_triangle_same_companion g hh hcAB hcBD
        a b d x hab hbd hAB hBD hABd hBDa hxa hxb hxd hABx hBDx
        hABzero hBDzeroX
    exact common_touched_of_two_smul_eq g hg hh hne hunique hxb.symm hdoubles
  by_cases hyz : y = z
  · have hDAy : cDA y = 1 := by simpa [hyz] using hDAz
    have hDAzeroY : ∀ i, i ≠ d → i ≠ a → i ≠ b → i ≠ y → cDA i = 0 := by
      simpa [hyz] using hDAzero
    have hdoubles : (2 : ℤ) • g d = (2 : ℤ) • g y :=
      two_smul_eq_of_adjacent_triangle_same_companion g hh hcBD hcDA
        b d a y hbd hda hBD hDA hBDa hDAb hyb hyd hya hBDy hDAy
        hBDzero hDAzeroY
    exact common_touched_of_two_smul_eq g hg hh hne hunique hyd.symm hdoubles
  by_cases hzx : z = x
  · have hABz : cAB z = 1 := by simpa [hzx] using hABx
    have hABzeroZ : ∀ i, i ≠ a → i ≠ b → i ≠ d → i ≠ z → cAB i = 0 := by
      simpa [hzx] using hABzero
    have hdoubles : (2 : ℤ) • g a = (2 : ℤ) • g z :=
      two_smul_eq_of_adjacent_triangle_same_companion g hh hcDA hcAB
        d a b z hda hab hDA hAB hDAb hABd hzd hza hzb hDAz hABz
        hDAzero hABzeroZ
    exact common_touched_of_two_smul_eq g hg hh hne hunique hza.symm hdoubles
  let cTriple := cAB + cBD + cDA
  have hcTriple : Witness g h cTriple :=
    witness_triangle_sum_of_positive_opposites g hh hne hcAB hcBD hcDA
      a b d hAB hBD hDA (by omega) (by omega) (by omega)
  have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
  have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  have hle : ∀ i, cTriple i ≤ 1 := by
    intro i
    by_cases hia : i = a
    · subst i
      simp only [cTriple, Pi.add_apply]
      omega
    by_cases hib : i = b
    · subst i
      simp only [cTriple, Pi.add_apply]
      omega
    by_cases hid : i = d
    · subst i
      simp only [cTriple, Pi.add_apply]
      omega
    by_cases hix : i = x
    · subst i
      have hBDx0 : cBD x = 0 := hBDzero x hxb hxd hxa hxy
      have hDAx0 : cDA x = 0 := hDAzero x hxd hxa hxb (Ne.symm hzx)
      simp only [cTriple, Pi.add_apply]
      omega
    by_cases hiy : i = y
    · subst i
      have hABy0 : cAB y = 0 := hABzero y hya hyb hyd (Ne.symm hxy)
      have hDAy0 : cDA y = 0 := hDAzero y hyd hya hyb hyz
      simp only [cTriple, Pi.add_apply]
      omega
    by_cases hiz : i = z
    · subst i
      have hABz0 : cAB z = 0 := hABzero z hza hzb hzd hzx
      have hBDz0 : cBD z = 0 := hBDzero z hzb hzd hza (Ne.symm hyz)
      simp only [cTriple, Pi.add_apply]
      omega
    have hABi0 : cAB i = 0 := hABzero i hia hib hid hix
    have hBDi0 : cBD i = 0 := hBDzero i hib hid hia hiy
    have hDAi0 : cDA i = 0 := hDAzero i hid hia hib hiz
    simp [cTriple, hABi0, hBDi0, hDAi0]
  have hcNeg : Witness g h (-cTriple) :=
    witness_neg_of_le_one g hh hcTriple hle
  have hshare : ∀ i, ¬(cAB i = -1 ∧ (-cTriple) i = -1) := by
    intro i hi
    rcases (hAB i).1 hi.1 with rfl | rfl
    · simp only [cTriple, Pi.add_apply, Pi.neg_apply] at hi
      omega
    · simp only [cTriple, Pi.add_apply, Pi.neg_apply] at hi
      omega
  have hneg := witness_combination g hg hh hcAB hcNeg hshare
  have hd := congrFun hneg d
  simp only [cTriple, Pi.add_apply, Pi.neg_apply] at hd
  omega

/-- Cyclic specialization: the exact omission-triangle profile `(1,1,1)`
has a G1 common-touch coordinate in `ZMod (2*M)`. -/
theorem common_touched_of_triangle_all_one_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 1) (hBDa : cBD a = 1) (hDAb : cDA b = 1) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g (M : ZMod N) c → c j ≠ 0 := by
  exact common_touched_of_triangle_all_one g hg
    (half_add_half hN) (half_ne_zero hN hM)
    (fun x hx => zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
    hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hABd hBDa hDAb

/-- Two adjacent exact two-omission witnesses with light opposite
coefficients already close G1 in a group with unique nonzero involution.  If
their companion `+1` coordinates agree, the adjacent relations give equal
doubles.  If they differ, negating both light witnesses produces witnesses
with disjoint omission pairs, contradicting witness combination. -/
theorem common_touched_of_two_adjacent_light_opposites
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 1) (hQRp : cQR p = 1) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  obtain ⟨e, hep, heq, her, hPQe, hPQzero⟩ :=
    exists_companion_one_of_exact_pair_coeff_one g hcPQ p q r hpq hPQ
      hrp hqr.symm hPQr
  obtain ⟨f, hfq, hfr, hfp, hQRf, hQRzero⟩ :=
    exists_companion_one_of_exact_pair_coeff_one g hcQR q r p hqr hQR
      hpq hrp.symm hQRp
  by_cases hef : e = f
  · have hQRe : cQR e = 1 := by simpa [hef] using hQRf
    have hQRzeroE : ∀ i, i ≠ q → i ≠ r → i ≠ p → i ≠ e → cQR i = 0 := by
      simpa [hef] using hQRzero
    have hdoubles : (2 : ℤ) • g q = (2 : ℤ) • g e :=
      two_smul_eq_of_adjacent_triangle_same_companion g hh hcPQ hcQR
        p q r e hpq hqr hPQ hQR hPQr hQRp hep heq her hPQe hQRe
        hPQzero hQRzeroE
    exact common_touched_of_two_smul_eq g hg hh hne hunique heq.symm hdoubles
  have hlePQ : ∀ i, cPQ i ≤ 1 := by
    intro i
    by_cases hip : i = p
    · subst i
      have := (hPQ p).2 (Or.inl rfl)
      omega
    by_cases hiq : i = q
    · subst i
      have := (hPQ q).2 (Or.inr rfl)
      omega
    by_cases hir : i = r
    · subst i
      omega
    by_cases hie : i = e
    · subst i
      omega
    rw [hPQzero i hip hiq hir hie]
    norm_num
  have hleQR : ∀ i, cQR i ≤ 1 := by
    intro i
    by_cases hiq : i = q
    · subst i
      have := (hQR q).2 (Or.inl rfl)
      omega
    by_cases hir : i = r
    · subst i
      have := (hQR r).2 (Or.inr rfl)
      omega
    by_cases hip : i = p
    · subst i
      omega
    by_cases hif : i = f
    · subst i
      omega
    rw [hQRzero i hiq hir hip hif]
    norm_num
  have hcNegPQ : Witness g h (-cPQ) := witness_neg_of_le_one g hh hcPQ hlePQ
  have hcNegQR : Witness g h (-cQR) := witness_neg_of_le_one g hh hcQR hleQR
  have hPQone : ∀ i, cPQ i = 1 → i = r ∨ i = e := by
    intro i hi
    by_cases hip : i = p
    · subst i
      have := (hPQ p).2 (Or.inl rfl)
      omega
    by_cases hiq : i = q
    · subst i
      have := (hPQ q).2 (Or.inr rfl)
      omega
    by_cases hir : i = r
    · exact Or.inl hir
    by_cases hie : i = e
    · exact Or.inr hie
    rw [hPQzero i hip hiq hir hie] at hi
    omega
  have hQRone : ∀ i, cQR i = 1 → i = p ∨ i = f := by
    intro i hi
    by_cases hiq : i = q
    · subst i
      have := (hQR q).2 (Or.inl rfl)
      omega
    by_cases hir : i = r
    · subst i
      have := (hQR r).2 (Or.inr rfl)
      omega
    by_cases hip : i = p
    · exact Or.inl hip
    by_cases hif : i = f
    · exact Or.inr hif
    rw [hQRzero i hiq hir hip hif] at hi
    omega
  have hshare : ∀ i, ¬((-cPQ) i = -1 ∧ (-cQR) i = -1) := by
    intro i hi
    have hPQoneI : cPQ i = 1 := by
      have hPQneg := hi.1
      simp only [Pi.neg_apply] at hPQneg
      omega
    have hQRoneI : cQR i = 1 := by
      have hQRneg := hi.2
      simp only [Pi.neg_apply] at hQRneg
      omega
    rcases hPQone i hPQoneI with hir | hie <;>
      rcases hQRone i hQRoneI with hip | hif
    · exact hrp (hir.symm.trans hip)
    · exact hfr (hif.symm.trans hir)
    · exact hep (hie.symm.trans hip)
    · exact hef (hie.symm.trans hif)
  have hneg := witness_combination g hg hh hcNegPQ hcNegQR hshare
  have hq := congrFun hneg q
  have hPQq : cPQ q = -1 := (hPQ q).2 (Or.inr rfl)
  have hQRq : cQR q = -1 := (hQR q).2 (Or.inl rfl)
  simp only [Pi.neg_apply, hPQq, hQRq] at hq
  omega

/-- Cyclic specialization of the adjacent-light closure. -/
theorem common_touched_of_two_adjacent_light_opposites_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cPQ cQR : Fin n → ℤ}
    (hcPQ : Witness g (M : ZMod N) cPQ)
    (hcQR : Witness g (M : ZMod N) cQR)
    (p q r : Fin n) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 1) (hQRp : cQR p = 1) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g (M : ZMod N) c → c j ≠ 0 := by
  exact common_touched_of_two_adjacent_light_opposites g hg
    (half_add_half hN) (half_ne_zero hN hM)
    (fun x hx => zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
    hcPQ hcQR p q r hpq hqr hrp hPQ hQR hPQr hQRp

/-- A zero opposite in an exact omission triangle is necessarily pure: the
two units of positive mass of that edge witness concentrate as coefficient
`2` at one coordinate outside the triangle.  Otherwise all coefficients
would lie in `[-1,1]`; negating the witness would give a half-witness whose
omissions are disjoint from the adjacent edge, contradicting combination. -/
theorem exists_pure_companion_two_of_triangle_zero_opposite
    (g : Fin n → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 0) :
    ∃ e : Fin n, e ≠ p ∧ e ≠ q ∧ e ≠ r ∧ cPQ e = 2 ∧
      ∀ j : Fin n, j ≠ p → j ≠ q → j ≠ r → j ≠ e → cPQ j = 0 := by
  by_contra hnone
  have hnotwo : ∀ e : Fin n, e ≠ p → e ≠ q → e ≠ r → cPQ e ≠ 2 := by
    intro e hep heq her hce
    apply hnone
    refine ⟨e, hep, heq, her, hce, ?_⟩
    intro j hjp hjq _hjr hje
    exact witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hcPQ
      p q e hpq hPQ hep heq hce j hjp hjq hje
  have hlePQ : ∀ i, cPQ i ≤ 1 := by
    intro i
    by_cases hip : i = p
    · subst i
      have := (hPQ p).2 (Or.inl rfl)
      omega
    by_cases hiq : i = q
    · subst i
      have := (hPQ q).2 (Or.inr rfl)
      omega
    by_cases hir : i = r
    · subst i
      omega
    have hclass := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hcPQ p q i hpq hPQ hip hiq
    have hneTwo := hnotwo i hip hiq hir
    rcases hclass with h0 | h1 | h2 <;> omega
  have hcNegPQ : Witness g h (-cPQ) := witness_neg_of_le_one g hh hcPQ hlePQ
  have hshare : ∀ i, ¬((-cPQ) i = -1 ∧ cQR i = -1) := by
    intro i hi
    rcases (hQR i).1 hi.2 with hiq | hir
    · subst i
      have hPQq : cPQ q = -1 := (hPQ q).2 (Or.inr rfl)
      simp only [Pi.neg_apply, hPQq] at hi
      omega
    · subst i
      simp only [Pi.neg_apply, hPQr] at hi
      omega
  have hneg := witness_combination g hg hh hcNegPQ hcQR hshare
  have hp := congrFun hneg p
  have hPQp : cPQ p = -1 := (hPQ p).2 (Or.inl rfl)
  have hQRp : cQR p ≠ -1 := by
    intro hbad
    rcases (hQR p).1 hbad with hpq' | hpr
    · exact hpq hpq'
    · exact hrp hpr.symm
  simp only [Pi.neg_apply, hPQp] at hp
  exact hQRp (by omega)

/-- A pure two-omission witness is the affine doubling relation
`2g_e = h + g_p + g_q`. -/
theorem two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    (g : Fin n → G) {h : G} {c : Fin n → ℤ} (hc : Witness g h c)
    (p q e : Fin n) (hpq : p ≠ q)
    (homit : ∀ i, c i = -1 ↔ i = p ∨ i = q)
    (hep : e ≠ p) (heq : e ≠ q) (hce : c e = 2) :
    (2 : ℤ) • g e = h + g p + g q := by
  have hterm : ∀ i, c i • g i =
      (if i = e then (2 : ℤ) • g i else 0) -
        (if i = p then g i else 0) - (if i = q then g i else 0) := by
    intro i
    by_cases hip : i = p
    · subst i
      have hcp : c p = -1 := (homit p).2 (Or.inl rfl)
      simp [hcp, hpq, Ne.symm hep]
    by_cases hiq : i = q
    · subst i
      have hcq : c q = -1 := (homit q).2 (Or.inr rfl)
      simp [hcq, hpq.symm, Ne.symm heq]
    by_cases hie : i = e
    · subst i
      simp [hce, hep, heq]
    have hci : c i = 0 :=
      witness_other_eq_zero_of_exact_pair_and_coeff_eq_two g hc p q e hpq
        homit hep heq hce i hip hiq hie
    simp [hci, hip, hiq, hie]
  have hformula : (∑ i, c i • g i) =
      (2 : ℤ) • g e - g p - g q := by
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' univ e fun i => (2 : ℤ) • g i,
      Finset.sum_ite_eq' univ p g, Finset.sum_ite_eq' univ q g]
    simp
  have hval : (2 : ℤ) • g e - g p - g q = h := by
    rw [← hformula]
    exact hc.2.2.2
  calc
    (2 : ℤ) • g e = ((2 : ℤ) • g e - g p - g q) + g p + g q := by abel
    _ = h + g p + g q := by rw [hval]

/-- Pure companions of adjacent zero-opposite edges are distinct.  Equality
would make the two affine doubling relations identify the nonshared triangle
vertices, contradicting injectivity of a valid tuple. -/
theorem pure_companions_ne_of_adjacent_zero_opposites
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r e f : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hep : e ≠ p) (heq : e ≠ q) (hfe : f ≠ q) (hfr : f ≠ r)
    (hPQe : cPQ e = 2) (hQRf : cQR f = 2) : e ≠ f := by
  intro hef
  subst f
  have hPQval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcPQ p q e hpq hPQ hep heq hPQe
  have hQRval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcQR q r e hqr hQR hfe hfr hQRf
  have hsums : h + g p + g q = h + g q + g r := hPQval.symm.trans hQRval
  have hdiff : g p - g r = (h + g p + g q) - (h + g q + g r) := by abel
  have hzero : g p - g r = 0 := by rw [hdiff, hsums, sub_self]
  have hpr : p = r := validTuple_injective g hg (sub_eq_zero.mp hzero)
  exact hrp hpr.symm

/-- An all-zero exact omission triangle expands to three pairwise-distinct
pure companion coordinates outside its three vertices.  Thus the residual is
a six-coordinate affine doubling configuration, not an arbitrary coefficient
pattern. -/
theorem exists_six_distinct_pure_centers_of_triangle_all_zero
    (g : Fin n → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 0) (hDAb : cDA b = 0) :
    ∃ x y z : Fin n,
      (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
      (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
      (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      cAB x = 2 ∧ cBD y = 2 ∧ cDA z = 2 := by
  obtain ⟨x, hxa, hxb, hxd, hABx, _hABzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite g hg hh hcAB hcBD
      a b d hab hda hAB hBD hABd
  obtain ⟨y, hyb, hyd, hya, hBDy, _hBDzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite g hg hh hcBD hcDA
      b d a hbd hab hBD hDA hBDa
  obtain ⟨z, hzd, hza, hzb, hDAz, _hDAzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite g hg hh hcDA hcAB
      d a b hda hbd hDA hAB hDAb
  have hxy : x ≠ y := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcAB hcBD a b d x y hab hbd hda hAB hBD
      hxa hxb hyb hyd hABx hBDy
  have hyz : y ≠ z := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcBD hcDA b d a y z hbd hda hab hBD hDA
      hyb hyd hzd hza hBDy hDAz
  have hzx : z ≠ x := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcDA hcAB d a b z x hda hab hbd hDA hAB
      hzd hza hxa hxb hDAz hABx
  exact ⟨x, y, z, ⟨hxa, hxb, hxd⟩, ⟨hyb, hyd, hya⟩,
    ⟨hzd, hza, hzb⟩, hxy, hyz, hzx, hABx, hBDy, hDAz⟩

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

/-- In an exact omission triangle with opposite profile `(0,2,2)`, the zero
edge has a pure companion whose displacement from the opposite vertex is a
"quarter" of the target: doubling that displacement gives `h`.  This is the
group-level algebraic content behind the extra factor `4` in the cyclic
obstruction. -/
theorem exists_double_difference_eq_target_of_triangle_zero_two_two
    (g : Fin n → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 2) (hDAb : cDA b = 2) :
    ∃ x : Fin n, x ≠ a ∧ x ≠ b ∧ x ≠ d ∧ cAB x = 2 ∧
      (g x - g d) + (g x - g d) = h := by
  obtain ⟨x, hxa, hxb, hxd, hABx, _⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite g hg hh hcAB hcBD
      a b d hab hda hAB hBD hABd
  have hABval : (2 : ℤ) • g x = h + g a + g b :=
    two_smul_eq_target_add_pair_of_exact_pair_coeff_two
      g hcAB a b x hab hAB hxa hxb hABx
  have hBDval : (2 : ℤ) • g a = h + g b + g d :=
    two_smul_eq_target_add_pair_of_exact_pair_coeff_two
      g hcBD b d a hbd hBD hab hda.symm hBDa
  have hDAval : (2 : ℤ) • g b = h + g d + g a :=
    two_smul_eq_target_add_pair_of_exact_pair_coeff_two
      g hcDA d a b hda hDA hbd hab.symm hDAb
  have hsum : (2 : ℤ) • g a + (2 : ℤ) • g b =
      g a + g b + (2 : ℤ) • g d := by
    rw [hBDval, hDAval]
    simp only [two_zsmul]
    rw [show h + g b + g d + (h + g d + g a) =
        (h + h) + (g a + g b + (g d + g d)) by abel, hh, zero_add]
  have habd : g a + g b = (2 : ℤ) • g d := by
    calc
      g a + g b =
          ((2 : ℤ) • g a + (2 : ℤ) • g b) - (g a + g b) := by
            simp only [two_zsmul]
            abel
      _ = (g a + g b + (2 : ℤ) • g d) - (g a + g b) := by rw [hsum]
      _ = (2 : ℤ) • g d := by abel
  refine ⟨x, hxa, hxb, hxd, hABx, ?_⟩
  calc
    (g x - g d) + (g x - g d) =
        (2 : ℤ) • g x - (2 : ℤ) • g d := by
          simp only [two_zsmul]
          abel
    _ = (h + g a + g b) - (2 : ℤ) • g d := by rw [hABval]
    _ = h + (g a + g b) - (2 : ℤ) • g d := by abel
    _ = h := by rw [habd]; abel

/-- Two adjacent heavy opposite coefficients force equality after tripling
the two nonshared triangle coordinates. -/
theorem three_smul_eq_of_two_adjacent_heavy_opposites
    (g : Fin n → G) {h : G}
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) :
    (3 : ℤ) • g p = (3 : ℤ) • g r := by
  have hPQval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcPQ p q r hpq hPQ hrp hqr.symm hPQr
  have hQRval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcQR q r p hqr hQR hpq hrp.symm hQRp
  calc
    (3 : ℤ) • g p = (2 : ℤ) • g p + g p := by
      rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul]
    _ = (h + g q + g r) + g p := by rw [hQRval]
    _ = (h + g p + g q) + g r := by abel
    _ = (2 : ℤ) • g r + g r := by rw [← hPQval]
    _ = (3 : ℤ) • g r := by
      rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul]

/-- If tripling is injective on the ambient group, two adjacent heavy
opposites are impossible in a valid tuple. -/
theorem not_two_adjacent_heavy_opposites_of_three_smul_injective
    (g : Fin n → G) (hg : ValidTuple g)
    (hinj3 : Function.Injective (fun x : G => (3 : ℤ) • x)) {h : G}
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) : False := by
  have htrip := three_smul_eq_of_two_adjacent_heavy_opposites g hcPQ hcQR
    p q r hpq hqr hrp hPQ hQR hPQr hQRp
  have hgpr : g p = g r := hinj3 htrip
  exact hrp (validTuple_injective g hg hgpr).symm

/-- Without assuming tripling injective, adjacent heavy opposites exhibit the
precise obstruction: the difference of the two nonshared coordinates is a
nonzero element killed by `3`. -/
theorem nonzero_three_torsion_of_two_adjacent_heavy_opposites
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) :
    g p - g r ≠ 0 ∧ (3 : ℤ) • (g p - g r) = 0 := by
  have htrip := three_smul_eq_of_two_adjacent_heavy_opposites g hcPQ hcQR
    p q r hpq hqr hrp hPQ hQR hPQr hQRp
  constructor
  · intro hzero
    have hgpr : g p = g r := sub_eq_zero.mp hzero
    exact hrp (validTuple_injective g hg hgpr).symm
  · rw [smul_sub, htrip, sub_self]

/-- If `3` does not divide `N`, tripling is injective on `ZMod N`. -/
theorem zmod_three_zsmul_injective {N : ℕ} [NeZero N] (h3 : ¬3 ∣ N) :
    Function.Injective (fun x : ZMod N => (3 : ℤ) • x) := by
  intro x y hxy
  have hu : IsUnit ((3 : ℕ) : ZMod N) :=
    ZMod.isUnit_prime_of_not_dvd (by norm_num) h3
  have hxy' : (3 : ℕ) • x = (3 : ℕ) • y := by
    change ((3 : ℕ) : ℤ) • x = ((3 : ℕ) : ℤ) • y at hxy
    simpa only [natCast_zsmul] using hxy
  apply hu.mul_left_cancel
  simpa only [nsmul_eq_mul] using hxy'

/-- Cyclic torsion obstruction: at a modulus not divisible by `3`, two
adjacent heavy opposite coefficients are impossible.  In particular this
eliminates the residual profile `(0,2,2)` up to rotation. -/
theorem not_two_adjacent_heavy_opposites_zmod
    {N : ℕ} [NeZero N] (h3 : ¬3 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) {h : ZMod N}
    {cPQ cQR : Fin n → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin n)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) : False := by
  exact not_two_adjacent_heavy_opposites_of_three_smul_injective g hg
    (zmod_three_zsmul_injective h3) hcPQ hcQR p q r hpq hqr hrp
      hPQ hQR hPQr hQRp

/-- Equivalently, the existence of two adjacent heavy opposites in a valid
tuple modulo `N` forces `3 ∣ N`. -/
theorem three_dvd_of_two_adjacent_heavy_opposites_zmod
    {N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {cPQ cQR : Fin n → ℤ}
    (hcPQ : Witness g h cPQ) (hcQR : Witness g h cQR)
    (p q r : Fin n) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) : 3 ∣ N := by
  by_contra h3
  exact not_two_adjacent_heavy_opposites_zmod h3 g hg hcPQ hcQR
    p q r hpq hqr hrp hPQ hQR hPQr hQRp

/-- If an element modulo `2M` doubles to the distinguished half `M`, then
`M` is even and hence the modulus is divisible by `4`.  Reduction modulo `2`
makes the parity obstruction explicit. -/
theorem four_dvd_of_double_eq_half
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (x : ZMod N)
    (hx : x + x = (M : ZMod N)) : 4 ∣ N := by
  have h2N : 2 ∣ N := ⟨M, hN⟩
  let f : ZMod N →+* ZMod 2 := ZMod.castHom h2N (ZMod 2)
  have hMzero : (M : ZMod 2) = 0 := by
    calc
      (M : ZMod 2) = f (M : ZMod N) := by
        symm
        exact map_natCast f M
      _ = f (x + x) := by rw [hx]
      _ = f x + f x := map_add f x x
      _ = (2 : ℕ) • f x := (two_nsmul (f x)).symm
      _ = ((2 : ℕ) : ZMod 2) * f x := by rw [nsmul_eq_mul]
      _ = 0 := by rw [ZMod.natCast_self, zero_mul]
  rw [ZMod.natCast_eq_zero_iff] at hMzero
  obtain ⟨k, hk⟩ := hMzero
  refine ⟨k, ?_⟩
  omega

/-- The full cyclic obstruction for an exact `(0,2,2)` omission triangle.
The adjacent heavy edges force `3 ∣ N`, while the pure companion of the zero
edge gives an element doubling to the half and forces `4 ∣ N`; coprimality
therefore yields `12 ∣ N`. -/
theorem twelve_dvd_of_triangle_zero_two_two_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 2) (hDAb : cDA b = 2) :
    12 ∣ N := by
  obtain ⟨x, _hxa, _hxb, _hxd, _hABx, hx⟩ :=
    exists_double_difference_eq_target_of_triangle_zero_two_two
      g hg (half_add_half hN) hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  have h4 : 4 ∣ N := four_dvd_of_double_eq_half hN (g x - g d) hx
  have h3 : 3 ∣ N :=
    three_dvd_of_two_adjacent_heavy_opposites_zmod g hg hcBD hcDA
      b d a hbd hda hab hBD hDA hBDa hDAb
  have hcop : Nat.Coprime 3 4 := by norm_num
  simpa using hcop.mul_dvd_of_dvd_of_dvd h3 h4

/-- Every strictly positive exact omission triangle closes G1 in a group with
a unique nonzero involution.  The positive-mass identity reduces the profile
to `{1,2}³`; the cases are the all-one theorem, the zero/`2` reduction for
one heavy opposite, the unique-omission sum for two heavy opposites, and the
impossibility of the all-heavy profile. -/
theorem common_touched_of_triangle_positive
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABpos : 1 ≤ cAB d) (hBDpos : 1 ≤ cBD a) (hDApos : 1 ≤ cDA b) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0 := by
  obtain ⟨hABclass, hBDclass, hDAclass⟩ :=
    triangle_opposite_coefficients_zero_one_or_two g hcAB hcBD hcDA
      a b d hab hbd hda hAB hBD hDA
  have hAB12 : cAB d = 1 ∨ cAB d = 2 := by
    rcases hABclass with h0 | h1 | h2
    · omega
    · exact Or.inl h1
    · exact Or.inr h2
  have hBD12 : cBD a = 1 ∨ cBD a = 2 := by
    rcases hBDclass with h0 | h1 | h2
    · omega
    · exact Or.inl h1
    · exact Or.inr h2
  have hDA12 : cDA b = 1 ∨ cDA b = 2 := by
    rcases hDAclass with h0 | h1 | h2
    · omega
    · exact Or.inl h1
    · exact Or.inr h2
  rcases hAB12 with hAB1 | hAB2 <;>
    rcases hBD12 with hBD1 | hBD2 <;>
    rcases hDA12 with hDA1 | hDA2
  · exact common_touched_of_triangle_all_one g hg hh hne hunique
      hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hAB1 hBD1 hDA1
  · exact common_touched_of_triangle_one_one_two g hg hh hne hunique
      hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hAB1 hBD1 hDA2
  · exact common_touched_of_triangle_one_one_two g hg hh hne hunique
      hcDA hcAB hcBD d a b hda hab hbd hDA hAB hBD hDA1 hAB1 hBD2
  · exact ⟨d, common_touched_of_triangle_one_light_opposite g hg hh hne
      hcAB hcBD hcDA a b d hAB hBD hDA hAB1 (by omega) (by omega)⟩
  · exact common_touched_of_triangle_one_one_two g hg hh hne hunique
      hcBD hcDA hcAB b d a hbd hda hab hBD hDA hAB hBD1 hDA1 hAB2
  · exact ⟨a, common_touched_of_triangle_one_light_opposite g hg hh hne
      hcBD hcDA hcAB b d a hBD hDA hAB hBD1 (by omega) (by omega)⟩
  · exact ⟨b, common_touched_of_triangle_one_light_opposite g hg hh hne
      hcDA hcAB hcBD d a b hDA hAB hBD hDA1 (by omega) (by omega)⟩
  · exact (not_triangle_all_opposites_two g hh hne hcAB hcBD hcDA
      a b d hab hbd hda hAB hBD hDA hAB2 hBD2 hDA2).elim

/-- Cyclic specialization: every exact omission triangle with all three
opposite coefficients positive has a G1 common-touch coordinate. -/
theorem common_touched_of_triangle_positive_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABpos : 1 ≤ cAB d) (hBDpos : 1 ≤ cBD a) (hDApos : 1 ≤ cDA b) :
    ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g (M : ZMod N) c → c j ≠ 0 := by
  exact common_touched_of_triangle_positive g hg
    (half_add_half hN) (half_ne_zero hN hM)
    (fun x hx => zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
    hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hABpos hBDpos hDApos

end MinModulus
