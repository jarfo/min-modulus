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
