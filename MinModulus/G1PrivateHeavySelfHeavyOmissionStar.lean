/-
# Star-or-triangle structure of exact-two self-heavy omissions

A pairwise-intersecting family of distinct two-element sets is either a star
or has at most three members.  We prove this elementary set-system theorem in
a reusable form and apply it to the exact-two self-heavy omission pairs.

Under no common touch, the owner-to-pair map is injective.  Thus either at
most three self-heavy owners have exactly two omissions, or one external
coordinate is omitted by every witness in that layer.
-/
import MinModulus.G1PrivateHeavySelfHeavyOmissionPairs

namespace MinModulus

open Finset

/-- A two-element finset containing two distinct specified elements is their
pair. -/
theorem finset_eq_pair_of_card_eq_two_of_mem
    {α : Type*} [DecidableEq α]
    {S : Finset α} {a b : α}
    (hcard : S.card = 2) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    S = {a, b} := by
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxab
    have hxa : x ≠ a := by
      intro hxa
      subst x
      exact hxab (by simp)
    have hxb : x ≠ b := by
      intro hxb
      subst x
      exact hxab (by simp)
    have hthree : ({a, b, x} : Finset α) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hx
    have hcardThree : ({a, b, x} : Finset α).card = 3 := by
      simp [hab, Ne.symm hxa, Ne.symm hxb]
    have := Finset.card_le_card hthree
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

/-- Every pairwise-intersecting finite family of two-element sets is either
of cardinality at most three or has a common center. -/
theorem pairwiseInter_cardTwo_card_le_three_or_common
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hcard : ∀ A ∈ F, A.card = 2)
    (hinter : ∀ A ∈ F, ∀ P ∈ F, (A ∩ P).Nonempty) :
    F.card ≤ 3 ∨
      ∃ z : α, F.Nonempty ∧ ∀ A ∈ F, z ∈ A := by
  classical
  by_cases hsmall : F.card ≤ 3
  · exact Or.inl hsmall
  · right
    have hF : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨A, hAF⟩ := hF
    obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp (hcard A hAF)
    by_cases haCommon : ∀ P ∈ F, a ∈ P
    · exact ⟨a, ⟨A, hAF⟩, haCommon⟩
    by_cases hbCommon : ∀ P ∈ F, b ∈ P
    · exact ⟨b, ⟨A, hAF⟩, hbCommon⟩
    push Not at haCommon hbCommon
    obtain ⟨P, hPF, haP⟩ := haCommon
    obtain ⟨Q, hQF, hbQ⟩ := hbCommon
    have hbP : b ∈ P := by
      obtain ⟨x, hx⟩ := hinter A hAF P hPF
      have hxA := (Finset.mem_inter.mp hx).1
      have hxP := (Finset.mem_inter.mp hx).2
      have hx : x = a ∨ x = b := by
        simpa [hA] using hxA
      rcases hx with hxa | hxb
      · subst x
        exact False.elim (haP hxP)
      · subst x
        exact hxP
    have haQ : a ∈ Q := by
      obtain ⟨x, hx⟩ := hinter A hAF Q hQF
      have hxA := (Finset.mem_inter.mp hx).1
      have hxQ := (Finset.mem_inter.mp hx).2
      have hx : x = a ∨ x = b := by
        simpa [hA] using hxA
      rcases hx with hxa | hxb
      · subst x
        exact hxQ
      · subst x
        exact False.elim (hbQ hxQ)
    have hPcard := hcard P hPF
    have hEraseCard : (P.erase b).card = 1 := by
      have herase := Finset.card_erase_add_one hbP
      omega
    obtain ⟨c, hcErase⟩ : (P.erase b).Nonempty :=
      Finset.card_pos.mp (by rw [hEraseCard]; decide)
    have hcP : c ∈ P := Finset.mem_of_mem_erase hcErase
    have hcb : c ≠ b := (Finset.mem_erase.mp hcErase).1
    have hP : P = {b, c} :=
      finset_eq_pair_of_card_eq_two_of_mem hPcard hbP hcP hcb.symm
    have haC : a ≠ c := by
      intro hac
      subst c
      exact haP hcP
    have hcQ : c ∈ Q := by
      obtain ⟨x, hx⟩ := hinter P hPF Q hQF
      have hxP := (Finset.mem_inter.mp hx).1
      have hxQ := (Finset.mem_inter.mp hx).2
      have hx : x = b ∨ x = c := by
        simpa [hP] using hxP
      rcases hx with hxb | hxc
      · subst x
        exact False.elim (hbQ hxQ)
      · subst x
        exact hxQ
    have hQ : Q = {a, c} :=
      finset_eq_pair_of_card_eq_two_of_mem
        (hcard Q hQF) haQ hcQ haC
    have hclassify : ∀ R ∈ F, R = A ∨ R = P ∨ R = Q := by
      intro R hRF
      obtain ⟨x, hx⟩ := hinter A hAF R hRF
      have hxA := (Finset.mem_inter.mp hx).1
      have hxR := (Finset.mem_inter.mp hx).2
      have hx : x = a ∨ x = b := by
        simpa [hA] using hxA
      rcases hx with hxa | hxb
      · subst x
        obtain ⟨y, hy⟩ := hinter P hPF R hRF
        have hyP := (Finset.mem_inter.mp hy).1
        have hyR := (Finset.mem_inter.mp hy).2
        have hy : y = b ∨ y = c := by
          simpa [hP] using hyP
        rcases hy with hyb | hyc
        · subst y
          left
          calc
            R = {a, b} := finset_eq_pair_of_card_eq_two_of_mem
              (hcard R hRF) hxR hyR hab
            _ = A := hA.symm
        · subst y
          right; right
          calc
            R = {a, c} := finset_eq_pair_of_card_eq_two_of_mem
              (hcard R hRF) hxR hyR haC
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
          have hy : y = a ∨ y = c := by
            simpa [hQ] using hyQ
          rcases hy with hya | hyc
          · subst y
            exact False.elim (haR hyR)
          · subst y
            right; left
            calc
              R = {b, c} := finset_eq_pair_of_card_eq_two_of_mem
                (hcard R hRF) hxR hyR hcb.symm
              _ = P := hP.symm
    have hsubset : F ⊆ {A, P, Q} := by
      intro R hRF
      rcases hclassify R hRF with rfl | rfl | rfl <;> simp
    have hle : F.card ≤ 3 := by
      have hAPQ : ({A, P, Q} : Finset (Finset α)).card ≤
          ({P, Q} : Finset (Finset α)).card + 1 :=
        Finset.card_insert_le A {P, Q}
      have hPQ : ({P, Q} : Finset (Finset α)).card ≤
          ({Q} : Finset (Finset α)).card + 1 :=
        Finset.card_insert_le P {Q}
      calc
        F.card ≤ ({A, P, Q} : Finset (Finset α)).card :=
          Finset.card_le_card hsubset
        _ ≤ 3 := by simp at hAPQ hPQ ⊢; omega
    exact False.elim (hsmall hle)

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The exact-two self-heavy layer either has at most three owners or all of
its private witnesses omit one common external coordinate. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_commonOmission
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
          minimalSupportPrivateWitness g h hmin b.val z = -1 := by
  classical
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  let F := minimalSupportPrivateSelfHeavyOmissionPairs g h hmin
  have hFcard : F.card = E.card :=
    card_minimalSupportPrivateSelfHeavyOmissionPairs
      g hg h hh hne hunique hmin hno
  change F.card = E.card at hFcard
  have htwo : ∀ P ∈ F, P.card = 2 := by
    intro P hP
    exact (minimalSupportPrivateSelfHeavyOmissionPairs_card_eq_two_and_disjoint
      g h hmin hP).1
  have hinter : ∀ P ∈ F, ∀ Q ∈ F, (P ∩ Q).Nonempty := by
    intro P hP Q hQ
    exact minimalSupportPrivateSelfHeavyOmissionPairs_pairwise_inter
      g hg h hh hmin hP hQ
  rcases pairwiseInter_cardTwo_card_le_three_or_common F htwo hinter with
    hsmall | ⟨z, hFnonempty, hz⟩
  · left
    change E.card ≤ 3
    omega
  · right
    obtain ⟨P, hPF⟩ := hFnonempty
    have hPdata :=
      minimalSupportPrivateSelfHeavyOmissionPairs_card_eq_two_and_disjoint
        g h hmin hPF
    have hzP := hz P hPF
    refine ⟨z, Finset.disjoint_left.mp hPdata.2 hzP, ?_⟩
    intro b hb
    let b' : ↥E := ⟨b, hb⟩
    have hbF : minimalSupportPrivateSelfHeavyOmissionPair g h hmin b' ∈ F := by
      exact (mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
        g h hmin _).mpr ⟨b', rfl⟩
    have hzb := hz _ hbF
    exact (witnessOmissionCoordinates_exact
      (minimalSupportPrivateWitness g h hmin b.val) z).mpr (by
        simpa [minimalSupportPrivateSelfHeavyOmissionPair, b'] using hzb)

end MinModulus
