/-
# Fixed-layer capacity of three complete primitive residue classes

Validity injects prescribed-cardinality subset choices from any three
pairwise disjoint translates of one cyclic subgroup into that subgroup.  The
windowed primitive middle endpoint has exactly this form after the exhaustive
three-residue partition: the third class may be empty, but no fourth class is
possible.  This module turns that structural statement into all triple-layer
capacity inequalities over the deleted transversal.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeThreeResiduePartition

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Prescribed-cardinality subset layers from three pairwise disjoint
translated coordinate families inject jointly into their common cyclic
subgroup. -/
theorem choose_mul_choose_mul_choose_le_addOrderOf_of_three_kernelCosets
    [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (A C D : Finset (Fin n))
    (hA : A.Nonempty) (hC : C.Nonempty) (hD : D.Nonempty)
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hCD : Disjoint C D)
    (hAcoset : ∀ b ∈ A, ∀ c ∈ A,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hCcoset : ∀ b ∈ C, ∀ c ∈ C,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hDcoset : ∀ b ∈ D, ∀ c ∈ D,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (i j k : ℕ) :
    A.card.choose i * C.card.choose j * D.card.choose k ≤ addOrderOf y := by
  classical
  obtain ⟨a, haA⟩ := hA
  obtain ⟨c, hcC⟩ := hC
  obtain ⟨d, hdD⟩ := hD
  let LA := A.powersetCard i
  let LC := C.powersetCard j
  let LD := D.powersetCard k
  let Domain := (↥LA × ↥LC) × ↥LD
  let combined : Domain → Finset (Fin n) := fun P ↦
    (P.1.1.1 ∪ P.1.2.1) ∪ P.2.1
  have hsubsetA : ∀ P : Domain, P.1.1.1 ⊆ A := by
    intro P
    exact (Finset.mem_powersetCard.mp P.1.1.property).1
  have hsubsetC : ∀ P : Domain, P.1.2.1 ⊆ C := by
    intro P
    exact (Finset.mem_powersetCard.mp P.1.2.property).1
  have hsubsetD : ∀ P : Domain, P.2.1 ⊆ D := by
    intro P
    exact (Finset.mem_powersetCard.mp P.2.property).1
  have hdisjointAC : ∀ P : Domain, Disjoint P.1.1.1 P.1.2.1 := by
    intro P
    rw [Finset.disjoint_left]
    intro x hxA hxC
    exact Finset.disjoint_left.mp hAC (hsubsetA P hxA) (hsubsetC P hxC)
  have hdisjointACD : ∀ P : Domain,
      Disjoint (P.1.1.1 ∪ P.1.2.1) P.2.1 := by
    intro P
    rw [Finset.disjoint_left]
    intro x hxAC hxD
    rcases Finset.mem_union.mp hxAC with hxA | hxC
    · exact Finset.disjoint_left.mp hAD (hsubsetA P hxA) (hsubsetD P hxD)
    · exact Finset.disjoint_left.mp hCD (hsubsetC P hxC) (hsubsetD P hxD)
  have hcardA : ∀ P : Domain, P.1.1.1.card = i := by
    intro P
    exact (Finset.mem_powersetCard.mp P.1.1.property).2
  have hcardC : ∀ P : Domain, P.1.2.1.card = j := by
    intro P
    exact (Finset.mem_powersetCard.mp P.1.2.property).2
  have hcardD : ∀ P : Domain, P.2.1.card = k := by
    intro P
    exact (Finset.mem_powersetCard.mp P.2.property).2
  have hcombinedCard : ∀ P : Domain, (combined P).card = i + j + k := by
    intro P
    dsimp only [combined]
    rw [Finset.card_union_of_disjoint (hdisjointACD P),
      Finset.card_union_of_disjoint (hdisjointAC P),
      hcardA P, hcardC P, hcardD P]
  have hcombinedSum : ∀ P : Domain,
      (∑ x ∈ combined P, g x) =
        (∑ x ∈ P.1.1.1, g x) +
          (∑ x ∈ P.1.2.1, g x) +
            ∑ x ∈ P.2.1, g x := by
    intro P
    dsimp only [combined]
    rw [Finset.sum_union (hdisjointACD P),
      Finset.sum_union (hdisjointAC P)]
  have hrecoverA : ∀ P : Domain, combined P ∩ A = P.1.1.1 := by
    intro P
    ext x
    constructor
    · intro hx
      have hxCombined := (Finset.mem_inter.mp hx).1
      have hxA := (Finset.mem_inter.mp hx).2
      rcases Finset.mem_union.mp hxCombined with hxAC | hxD
      · rcases Finset.mem_union.mp hxAC with hxPA | hxPC
        · exact hxPA
        · exact (Finset.disjoint_left.mp hAC hxA (hsubsetC P hxPC)).elim
      · exact (Finset.disjoint_left.mp hAD hxA (hsubsetD P hxD)).elim
    · intro hxPA
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hxPA),
          hsubsetA P hxPA⟩
  have hrecoverC : ∀ P : Domain, combined P ∩ C = P.1.2.1 := by
    intro P
    ext x
    constructor
    · intro hx
      have hxCombined := (Finset.mem_inter.mp hx).1
      have hxC := (Finset.mem_inter.mp hx).2
      rcases Finset.mem_union.mp hxCombined with hxAC | hxD
      · rcases Finset.mem_union.mp hxAC with hxPA | hxPC
        · exact (Finset.disjoint_left.mp hAC (hsubsetA P hxPA) hxC).elim
        · exact hxPC
      · exact (Finset.disjoint_left.mp hCD hxC (hsubsetD P hxD)).elim
    · intro hxPC
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hxPC),
          hsubsetC P hxPC⟩
  have hrecoverD : ∀ P : Domain, combined P ∩ D = P.2.1 := by
    intro P
    ext x
    constructor
    · intro hx
      have hxCombined := (Finset.mem_inter.mp hx).1
      have hxD := (Finset.mem_inter.mp hx).2
      rcases Finset.mem_union.mp hxCombined with hxAC | hxPD
      · rcases Finset.mem_union.mp hxAC with hxPA | hxPC
        · exact (Finset.disjoint_left.mp hAD (hsubsetA P hxPA) hxD).elim
        · exact (Finset.disjoint_left.mp hCD (hsubsetC P hxPC) hxD).elim
      · exact hxPD
    · intro hxPD
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ hxPD, hsubsetD P hxPD⟩
  let encode : Domain → AddSubgroup.zmultiples y := fun P ↦
    ⟨((∑ x ∈ P.1.1.1, (g x - g a)) +
        ∑ x ∈ P.1.2.1, (g x - g c)) +
        ∑ x ∈ P.2.1, (g x - g d),
      AddSubgroup.add_mem _
        (AddSubgroup.add_mem _
          (AddSubgroup.sum_mem _ fun x hx ↦
            hAcoset x (hsubsetA P hx) a haA)
          (AddSubgroup.sum_mem _ fun x hx ↦
            hCcoset x (hsubsetC P hx) c hcC))
        (AddSubgroup.sum_mem _ fun x hx ↦
          hDcoset x (hsubsetD P hx) d hdD)⟩
  have hencode : Function.Injective encode := by
    intro P Q hPQ
    have hvalue := congrArg Subtype.val hPQ
    dsimp only [encode] at hvalue
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const] at hvalue
    rw [hcardA P, hcardC P, hcardD P,
      hcardA Q, hcardC Q, hcardD Q] at hvalue
    have hsum :
        (∑ x ∈ P.1.1.1, g x) +
            (∑ x ∈ P.1.2.1, g x) + ∑ x ∈ P.2.1, g x =
          (∑ x ∈ Q.1.1.1, g x) +
            (∑ x ∈ Q.1.2.1, g x) + ∑ x ∈ Q.2.1, g x := by
      calc
        (∑ x ∈ P.1.1.1, g x) +
              (∑ x ∈ P.1.2.1, g x) + ∑ x ∈ P.2.1, g x =
            ((((∑ x ∈ P.1.1.1, g x) - i • g a) +
                ((∑ x ∈ P.1.2.1, g x) - j • g c)) +
                ((∑ x ∈ P.2.1, g x) - k • g d)) +
              (i • g a + j • g c + k • g d) := by abel
        _ = ((((∑ x ∈ Q.1.1.1, g x) - i • g a) +
                ((∑ x ∈ Q.1.2.1, g x) - j • g c)) +
                ((∑ x ∈ Q.2.1, g x) - k • g d)) +
              (i • g a + j • g c + k • g d) := by rw [hvalue]
        _ = (∑ x ∈ Q.1.1.1, g x) +
              (∑ x ∈ Q.1.2.1, g x) + ∑ x ∈ Q.2.1, g x := by abel
    have hcombined : combined P = combined Q := by
      let e : Fin n ↪ Fin n := Function.Embedding.refl (Fin n)
      apply validTuple_subsetSum_eq_of_card_eq g hg e
      · rw [hcombinedCard P, hcombinedCard Q]
      · change (∑ x ∈ combined P, g x) = ∑ x ∈ combined Q, g x
        rw [hcombinedSum P, hcombinedSum Q]
        exact hsum
    have hPA : P.1.1.1 = Q.1.1.1 := by
      calc
        P.1.1.1 = combined P ∩ A := (hrecoverA P).symm
        _ = combined Q ∩ A := by rw [hcombined]
        _ = Q.1.1.1 := hrecoverA Q
    have hPC : P.1.2.1 = Q.1.2.1 := by
      calc
        P.1.2.1 = combined P ∩ C := (hrecoverC P).symm
        _ = combined Q ∩ C := by rw [hcombined]
        _ = Q.1.2.1 := hrecoverC Q
    have hPD : P.2.1 = Q.2.1 := by
      calc
        P.2.1 = combined P ∩ D := (hrecoverD P).symm
        _ = combined Q ∩ D := by rw [hcombined]
        _ = Q.2.1 := hrecoverD Q
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext hPA
      · exact Subtype.ext hPC
    · exact Subtype.ext hPD
  have hcard := Fintype.card_le_of_injective encode hencode
  dsimp only [Domain, LA, LC, LD] at hcard
  rw [Fintype.card_prod, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_powersetCard,
    ← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hcard
  simpa only [Nat.mul_assoc] using hcard

/-- Exact critical comparison for arbitrary layers of the three exhaustive
deleted-owner residue classes. -/
theorem sixteen_mul_threeResidue_choose_lt_two_pow_transversalCard
    {q : ℕ} (B S T F : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hcap : ∀ i j k : ℕ,
      S.card.choose i * T.card.choose j * F.card.choose k ≤ q)
    (i j k : ℕ) :
    16 * (S.card.choose i * T.card.choose j * F.card.choose k) <
      2 ^ B.card := by
  calc
    16 * (S.card.choose i * T.card.choose j * F.card.choose k) ≤
        16 * q := Nat.mul_le_mul_left 16 (hcap i j k)
    _ < 2 ^ B.card :=
      sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
        B hretained hcritical

/-- The level-one secondary layer contributes its guaranteed factor three
while the primary and possible final classes both retain their central
binomial layers. -/
theorem fortyEight_mul_primaryFinalCentralChoose_lt_two_pow_transversalCard
    {q : ℕ} (B S T F : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hTcard : 3 ≤ T.card)
    (hcap : ∀ i j k : ℕ,
      S.card.choose i * T.card.choose j * F.card.choose k ≤ q) :
    48 * (S.card.choose (S.card / 2) * F.card.choose (F.card / 2)) <
      2 ^ B.card := by
  have hchoose : 3 ≤ T.card.choose 1 := by
    simpa using hTcard
  have hproduct :
      3 * (S.card.choose (S.card / 2) * F.card.choose (F.card / 2)) ≤ q := by
    calc
      3 * (S.card.choose (S.card / 2) * F.card.choose (F.card / 2)) ≤
          T.card.choose 1 *
            (S.card.choose (S.card / 2) * F.card.choose (F.card / 2)) :=
        Nat.mul_le_mul_right _ hchoose
      _ = S.card.choose (S.card / 2) * T.card.choose 1 *
            F.card.choose (F.card / 2) := by ring
      _ ≤ q := hcap (S.card / 2) 1 (F.card / 2)
  calc
    48 * (S.card.choose (S.card / 2) * F.card.choose (F.card / 2)) =
        16 *
          (3 * (S.card.choose (S.card / 2) * F.card.choose (F.card / 2))) :=
      by ring
    _ ≤ 16 * q := Nat.mul_le_mul_left 16 hproduct
    _ < 2 ^ B.card :=
      sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
        B hretained hcritical

/-- Lossless specialization to the exhaustive primitive partition.  The
secondary capacity data and every canonical row are retained, while every
fixed triple of layer sizes in the primary, secondary, and final deleted-owner
classes is bounded by the full odd factor.  If the final class is empty, its
only nonzero layer is level zero and the assertion reduces to the two-class
capacity theorem. -/
theorem PrimitiveThreeResidueCapacityPartition.exists_fullLayerCapacity
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B U S : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hScard : 16 ≤ S.card) (hSsubB : S ⊆ B) (hSsubU : S ⊆ U)
    (hScomplete : ∀ b : ↥B,
      ((b : Fin n) ∈ S ↔
        g (b : Fin n) - g (primitiveMiddleInsertedCoordinate p k₀) ∈
          AddSubgroup.zmultiples y))
    (hthree : PrimitiveThreeResidueCapacityPartition g y B U S p k₀) :
    ∃ T : Finset (Fin n), ∃ k₁ : ℤ, ∃ t : Fin n,
      ∃ F : Finset (Fin n),
      3 ≤ T.card ∧ T ⊆ B \ U ∧ t ∈ T ∧
      k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧ k₁ ≠ k₀ ∧
      (∀ b : ↥B, (b : Fin n) ∈ T →
        (p.coeff b (b : Fin n) = -1 ∨
          p.coeff b (b : Fin n) = 1) ∧
        p.weight b = 2 * k₁ ∧
        g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p.z) =
          -(k₁ •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p.x - g p.z))) ∧
      (∀ b : ↥B,
        ((b : Fin n) ∈ T ↔
          g (b : Fin n) - g t ∈ AddSubgroup.zmultiples y)) ∧
      (∀ b ∈ T, ∀ c ∈ U,
        g b - g c ∉ AddSubgroup.zmultiples y) ∧
      (∀ i j : ℕ, U.card.choose i * T.card.choose j ≤ q) ∧
      B = (S ∪ T) ∪ F ∧
      F ⊆ B \ (S ∪ T) ∧
      (F = ∅ ∨
        ∃ k₂ : ℤ, ∃ f : Fin n,
          f ∈ F ∧
          k₂ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
          k₂ ≠ k₀ ∧ k₂ ≠ k₁ ∧
          (∀ b : ↥B, (b : Fin n) ∈ F →
            (p.coeff b (b : Fin n) = -1 ∨
              p.coeff b (b : Fin n) = 1) ∧
            p.weight b = 2 * k₂ ∧
            g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) ∈
              AddSubgroup.zmultiples y ∧
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.z) =
              -(k₂ •
                (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g p.x - g p.z))) ∧
          ∀ b : ↥B,
            ((b : Fin n) ∈ F ↔
              g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y)) ∧
      ∀ i j k : ℕ,
        S.card.choose i * T.card.choose j * F.card.choose k ≤ q := by
  classical
  rcases hthree with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hTrows,
      hTcomplete, hTseparated, hUTcap, hfinal⟩
  rcases hfinal with ⟨F, hpartition, hFsub, hFcase⟩
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  have hSTdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro b hbS hbT
    exact (Finset.mem_sdiff.mp (hTsub hbT)).2 (hSsubU hbS)
  have hSFdisjoint : Disjoint S F := by
    rw [Finset.disjoint_left]
    intro b hbS hbF
    exact (Finset.mem_sdiff.mp (hFsub hbF)).2
      (Finset.mem_union_left T hbS)
  have hTFdisjoint : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro b hbT hbF
    exact (Finset.mem_sdiff.mp (hFsub hbF)).2
      (Finset.mem_union_right S hbT)
  have hScoset : ∀ b ∈ S, ∀ c ∈ S,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbS c hcS
    have hbParallel := (hScomplete ⟨b, hSsubB hbS⟩).1 hbS
    have hcParallel := (hScomplete ⟨c, hSsubB hcS⟩).1 hcS
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
    convert hsub using 1
    module
  have hTcoset : ∀ b ∈ T, ∀ c ∈ T,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbT c hcT
    have hbB := (Finset.mem_sdiff.mp (hTsub hbT)).1
    have hcB := (Finset.mem_sdiff.mp (hTsub hcT)).1
    have hbParallel := (hTcomplete ⟨b, hbB⟩).1 hbT
    have hcParallel := (hTcomplete ⟨c, hcB⟩).1 hcT
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
    convert hsub using 1
    module
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  rcases hFcase with hFempty | hFfull
  · subst F
    have hSTcap : ∀ i j : ℕ,
        S.card.choose i * T.card.choose j ≤ q := by
      intro i j
      have h := choose_mul_choose_le_addOrderOf_of_disjoint_kernelCosets
        g hg y S T hSnonempty hTnonempty hSTdisjoint
          hScoset hTcoset i j
      simpa only [horder] using h
    have hfullCap : ∀ i j k : ℕ,
        S.card.choose i * T.card.choose j *
          (∅ : Finset (Fin n)).card.choose k ≤ q := by
      intro i j k
      cases k with
      | zero => simpa using hSTcap i j
      | succ k => simp
    exact ⟨T, k₁, t, ∅, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hUTcap, hpartition,
      hFsub, Or.inl rfl, hfullCap⟩
  · rcases hFfull with
      ⟨k₂, f, hfF, hk₂Mem, hk₂Ne₀, hk₂Ne₁, hFrows, hFcomplete⟩
    have hFnonempty : F.Nonempty := ⟨f, hfF⟩
    have hFcoset : ∀ b ∈ F, ∀ c ∈ F,
        g b - g c ∈ AddSubgroup.zmultiples y := by
      intro b hbF c hcF
      have hbB := (Finset.mem_sdiff.mp (hFsub hbF)).1
      have hcB := (Finset.mem_sdiff.mp (hFsub hcF)).1
      have hbParallel := (hFcomplete ⟨b, hbB⟩).1 hbF
      have hcParallel := (hFcomplete ⟨c, hcB⟩).1 hcF
      have hsub :=
        (AddSubgroup.zmultiples y).sub_mem hbParallel hcParallel
      convert hsub using 1
      module
    have hfullCap : ∀ i j k : ℕ,
        S.card.choose i * T.card.choose j * F.card.choose k ≤ q := by
      intro i j k
      have h :=
        choose_mul_choose_mul_choose_le_addOrderOf_of_three_kernelCosets
          g hg y S T F hSnonempty hTnonempty hFnonempty
            hSTdisjoint hSFdisjoint hTFdisjoint hScoset hTcoset hFcoset
              i j k
      simpa only [horder] using h
    exact ⟨T, k₁, t, F, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hUTcap, hpartition, hFsub,
      Or.inr ⟨k₂, f, hfF, hk₂Mem, hk₂Ne₀, hk₂Ne₁, hFrows, hFcomplete⟩,
      hfullCap⟩

end MinModulus
