/-
# The global pure-edge omission family is a star or a triangle

Witness combination makes the exact omission pairs of any two pure
coefficient-two half-witnesses intersect.  The elementary classification of
pairwise-intersecting two-sets can therefore be made exact: either one
coordinate belongs to every pair, or three actual pairs are the three edges
of a triangle and every pair lies among them.

For the witness family, the triangle alternative immediately supplies the
existing exact-omission-triangle frontier.  Thus the pure transition graph
has no unrestricted long-path branch: outside that established frontier all
pure half-witnesses lie in one omission star.
-/
import MinModulus.G1PrivateHeavyTargetPureTransitionFresh

namespace MinModulus

open Finset

/-- Explicit star-or-triangle classification of a nonempty
pairwise-intersecting finite family of two-element sets. -/
theorem pairwiseInter_cardTwo_common_or_triangle
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hF : F.Nonempty)
    (hcard : ∀ A ∈ F, A.card = 2)
    (hinter : ∀ A ∈ F, ∀ P ∈ F, (A ∩ P).Nonempty) :
    (∃ z : α, ∀ A ∈ F, z ∈ A) ∨
      ∃ a b d : α,
        a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
        {a, b} ∈ F ∧ {b, d} ∈ F ∧ {d, a} ∈ F ∧
        F ⊆ {{a, b}, {b, d}, {d, a}} := by
  classical
  obtain ⟨A, hAF⟩ := hF
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp (hcard A hAF)
  by_cases haCommon : ∀ P ∈ F, a ∈ P
  · exact Or.inl ⟨a, haCommon⟩
  by_cases hbCommon : ∀ P ∈ F, b ∈ P
  · exact Or.inl ⟨b, hbCommon⟩
  right
  push Not at haCommon hbCommon
  obtain ⟨P, hPF, haP⟩ := haCommon
  obtain ⟨Q, hQF, hbQ⟩ := hbCommon
  have hbP : b ∈ P := by
    obtain ⟨x, hx⟩ := hinter A hAF P hPF
    have hxA := (Finset.mem_inter.mp hx).1
    have hxP := (Finset.mem_inter.mp hx).2
    have hx : x = a ∨ x = b := by simpa [hA] using hxA
    rcases hx with rfl | rfl
    · exact False.elim (haP hxP)
    · exact hxP
  have haQ : a ∈ Q := by
    obtain ⟨x, hx⟩ := hinter A hAF Q hQF
    have hxA := (Finset.mem_inter.mp hx).1
    have hxQ := (Finset.mem_inter.mp hx).2
    have hx : x = a ∨ x = b := by simpa [hA] using hxA
    rcases hx with rfl | rfl
    · exact hxQ
    · exact False.elim (hbQ hxQ)
  have hPcard := hcard P hPF
  have hEraseCard : (P.erase b).card = 1 := by
    have herase := Finset.card_erase_add_one hbP
    omega
  obtain ⟨d, hdErase⟩ : (P.erase b).Nonempty :=
    Finset.card_pos.mp (by rw [hEraseCard]; decide)
  have hdP : d ∈ P := Finset.mem_of_mem_erase hdErase
  have hdb : d ≠ b := (Finset.mem_erase.mp hdErase).1
  have hP : P = {b, d} :=
    finset_eq_pair_of_card_eq_two_of_mem hPcard hbP hdP hdb.symm
  have had : a ≠ d := by
    intro had
    subst d
    exact haP hdP
  have hdQ : d ∈ Q := by
    obtain ⟨x, hx⟩ := hinter P hPF Q hQF
    have hxP := (Finset.mem_inter.mp hx).1
    have hxQ := (Finset.mem_inter.mp hx).2
    have hx : x = b ∨ x = d := by simpa [hP] using hxP
    rcases hx with rfl | rfl
    · exact False.elim (hbQ hxQ)
    · exact hxQ
  have hQ : Q = {a, d} :=
    finset_eq_pair_of_card_eq_two_of_mem
      (hcard Q hQF) haQ hdQ had
  have hclassify : ∀ R ∈ F, R = A ∨ R = P ∨ R = Q := by
    intro R hRF
    obtain ⟨x, hx⟩ := hinter A hAF R hRF
    have hxA := (Finset.mem_inter.mp hx).1
    have hxR := (Finset.mem_inter.mp hx).2
    have hx : x = a ∨ x = b := by simpa [hA] using hxA
    rcases hx with hxa | hxb
    · subst x
      obtain ⟨y, hy⟩ := hinter P hPF R hRF
      have hyP := (Finset.mem_inter.mp hy).1
      have hyR := (Finset.mem_inter.mp hy).2
      have hy : y = b ∨ y = d := by simpa [hP] using hyP
      rcases hy with hyb | hyd
      · subst y
        left
        calc
          R = {a, b} := finset_eq_pair_of_card_eq_two_of_mem
            (hcard R hRF) hxR hyR hab
          _ = A := hA.symm
      · subst y
        right; right
        calc
          R = {a, d} := finset_eq_pair_of_card_eq_two_of_mem
            (hcard R hRF) hxR hyR had
          _ = Q := hQ.symm
    · subst x
      by_cases haR : a ∈ R
      · left
        calc
          R = {a, b} := finset_eq_pair_of_card_eq_two_of_mem
            (hcard R hRF) haR hxR hab
          _ = A := hA.symm
      · obtain ⟨y, hy⟩ := hinter Q hQF R hRF
        have hyQ := (Finset.mem_inter.mp hy).1
        have hyR := (Finset.mem_inter.mp hy).2
        have hy : y = a ∨ y = d := by simpa [hQ] using hyQ
        rcases hy with hya | hyd
        · subst y
          exact False.elim (haR hyR)
        · subst y
          right; left
          calc
            R = {b, d} := finset_eq_pair_of_card_eq_two_of_mem
              (hcard R hRF) hxR hyR hdb.symm
            _ = P := hP.symm
  have hAB : {a, b} ∈ F := by rw [← hA]; exact hAF
  have hBD : {b, d} ∈ F := by rw [← hP]; exact hPF
  have hDA : {d, a} ∈ F := by
    rw [pair_comm, ← hQ]
    exact hQF
  refine ⟨a, b, d, hab, hdb.symm, had.symm,
    hAB, hBD, hDA, ?_⟩
  intro R hRF
  rcases hclassify R hRF with hRA | hRP | hRQ
  · rw [hRA, hA]
    simp
  · rw [hRP, hP]
    simp
  · rw [hRQ, hQ, pair_comm a d]
    simp

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The finite family of exact omission pairs realized by coefficient-two
witnesses at `h`. -/
noncomputable def witnessPureEdgeOmissionPairs
    (g : Fin (m + 1) → G) (h : G) : Finset (Finset (Fin (m + 1))) := by
  classical
  exact Finset.univ.filter (fun P ↦
    P.card = 2 ∧ ∃ c : Fin (m + 1) → ℤ, ∃ e : Fin (m + 1),
      Witness g h c ∧ ExactOmissions c P ∧ c e = 2)

omit [DecidableEq G] in
@[simp] theorem mem_witnessPureEdgeOmissionPairs_iff
    (g : Fin (m + 1) → G) (h : G) (P : Finset (Fin (m + 1))) :
    P ∈ witnessPureEdgeOmissionPairs g h ↔
      P.card = 2 ∧ ∃ c : Fin (m + 1) → ℤ, ∃ e : Fin (m + 1),
        Witness g h c ∧ ExactOmissions c P ∧ c e = 2 := by
  classical
  simp [witnessPureEdgeOmissionPairs]

omit [DecidableEq G] in
/-- One displayed pure witness makes the pure-edge omission family
nonempty. -/
theorem witnessPureEdgeOmissionPairs_nonempty_of_exactPairTwo
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (a b e : Fin (m + 1)) (hab : a ≠ b)
    (homit : ∀ i, c i = -1 ↔ i = a ∨ i = b)
    (heTwo : c e = 2) :
    (witnessPureEdgeOmissionPairs g h).Nonempty := by
  classical
  refine ⟨{a, b}, (mem_witnessPureEdgeOmissionPairs_iff
    g h {a, b}).2 ⟨Finset.card_pair hab, c, e, hc, ?_, heTwo⟩⟩
  intro i
  simpa using homit i

omit [DecidableEq G] in
/-- Exact omission pairs of coefficient-two witnesses intersect pairwise. -/
theorem witnessPureEdgeOmissionPairs_pairwise_inter
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {P Q : Finset (Fin (m + 1))}
    (hP : P ∈ witnessPureEdgeOmissionPairs g h)
    (hQ : Q ∈ witnessPureEdgeOmissionPairs g h) :
    (P ∩ Q).Nonempty := by
  classical
  obtain ⟨_hPcard, c, e, hc, homitP, heTwo⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h P).1 hP
  obtain ⟨hQcard, d, f, hd, homitQ, hfTwo⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h Q).1 hQ
  obtain ⟨a, b, hab, hQpair⟩ := Finset.card_eq_two.mp hQcard
  have homitQ' : ∀ i, d i = -1 ↔ i = a ∨ i = b := by
    intro i
    rw [homitQ i, hQpair]
    simp
  obtain ⟨y, _hyEndpoint, hcy, hdy⟩ :=
    witness_exists_shared_pureEdge_endpoint
      g hg hh hc hd a b f homitQ' hfTwo
  exact ⟨y, Finset.mem_inter.mpr
    ⟨(homitP y).mp hcy, (homitQ y).mp hdy⟩⟩

omit [DecidableEq G] in
/-- The global family of pure half-witness omission pairs is either a star,
or three actual pure witnesses supply an exact omission triangle. -/
theorem witnessPureEdgeOmissionPairs_common_or_exactTriangle
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hF : (witnessPureEdgeOmissionPairs g h).Nonempty) :
    (∃ z : Fin (m + 1), ∀ P ∈ witnessPureEdgeOmissionPairs g h, z ∈ P) ∨
      WitnessExactOmissionTriangle g h := by
  classical
  let F := witnessPureEdgeOmissionPairs g h
  have hcard : ∀ P ∈ F, P.card = 2 := by
    intro P hP
    exact (mem_witnessPureEdgeOmissionPairs_iff g h P).1 hP |>.1
  have hinter : ∀ P ∈ F, ∀ Q ∈ F, (P ∩ Q).Nonempty := by
    intro P hP Q hQ
    exact witnessPureEdgeOmissionPairs_pairwise_inter g hg hh hP hQ
  rcases pairwiseInter_cardTwo_common_or_triangle F hF hcard hinter with
    ⟨z, hz⟩ | ⟨a, b, d, hab, hbd, hda, hAB, hBD, hDA, _hsubset⟩
  · exact Or.inl ⟨z, hz⟩
  · obtain ⟨_hABcard, cAB, _eAB, hcAB, hABomit, _hABTwo⟩ :=
      (mem_witnessPureEdgeOmissionPairs_iff g h {a, b}).1 hAB
    obtain ⟨_hBDcard, cBD, _eBD, hcBD, hBDomit, _hBDTwo⟩ :=
      (mem_witnessPureEdgeOmissionPairs_iff g h {b, d}).1 hBD
    obtain ⟨_hDAcard, cDA, _eDA, hcDA, hDAomit, _hDATwo⟩ :=
      (mem_witnessPureEdgeOmissionPairs_iff g h {d, a}).1 hDA
    exact Or.inr ⟨cAB, cBD, cDA, a, b, d,
      hcAB, hcBD, hcDA, hab, hbd, hda,
      fun i ↦ by simpa using hABomit i,
      fun i ↦ by simpa using hBDomit i,
      fun i ↦ by simpa using hDAomit i⟩

end MinModulus
