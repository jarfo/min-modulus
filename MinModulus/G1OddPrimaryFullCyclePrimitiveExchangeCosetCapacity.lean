/-
# Two-coset capacity for the primitive middle family

Two disjoint coordinate families lying in translates of one cyclic subgroup
have a multiplicative fixed-layer bound.  Choose fixed cardinalities in both
families.  Translation terms then cancel between any two pairs of subsets,
so validity injects the product of the two subset layers into the subgroup.

For the primitive middle family, the fixed leaf range is one odd-kernel coset
and the selected owners together with the exchanged-in retained coordinate
are another.  If these cosets meet, their union is one coset and gives the
usual exponential subgroup bound.  If they do not, every product of their
binomial layers is bounded by the odd factor.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeLeafLocation

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Fixed-cardinality subset layers from two disjoint translated coordinate
families inject jointly into their common cyclic subgroup. -/
theorem choose_mul_choose_le_addOrderOf_of_two_kernelCosets
    [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g)
    {ell₁ ell₂ : ℕ}
    (e₁ : Fin ell₁ ↪ Fin n) (e₂ : Fin ell₂ ↪ Fin n)
    (hcross : ∀ i j, e₁ i ≠ e₂ j)
    (a₁ a₂ y : G)
    (hmem₁ : ∀ i, g (e₁ i) - a₁ ∈ AddSubgroup.zmultiples y)
    (hmem₂ : ∀ j, g (e₂ j) - a₂ ∈ AddSubgroup.zmultiples y)
    (k₁ k₂ : ℕ) :
    ell₁.choose k₁ * ell₂.choose k₂ ≤ addOrderOf y := by
  classical
  let L₁ := (Finset.univ : Finset (Fin ell₁)).powersetCard k₁
  let L₂ := (Finset.univ : Finset (Fin ell₂)).powersetCard k₂
  let inlEmb : Fin ell₁ ↪ Sum (Fin ell₁) (Fin ell₂) :=
    ⟨Sum.inl, Sum.inl_injective⟩
  let inrEmb : Fin ell₂ ↪ Sum (Fin ell₁) (Fin ell₂) :=
    ⟨Sum.inr, Sum.inr_injective⟩
  let e : Sum (Fin ell₁) (Fin ell₂) ↪ Fin n :=
    ⟨(fun u ↦ match u with
      | Sum.inl i => e₁ i
      | Sum.inr j => e₂ j), by
      intro u v huv
      cases u with
      | inl i =>
          cases v with
          | inl j =>
              change e₁ i = e₁ j at huv
              exact congrArg Sum.inl (e₁.injective huv)
          | inr j =>
              change e₁ i = e₂ j at huv
              exact (hcross i j huv).elim
      | inr i =>
          cases v with
          | inl j =>
              change e₂ i = e₁ j at huv
              exact (hcross j i huv.symm).elim
          | inr j =>
              change e₂ i = e₂ j at huv
              exact congrArg Sum.inr (e₂.injective huv)⟩
  let combined : ↥L₁ × ↥L₂ → Finset (Sum (Fin ell₁) (Fin ell₂)) :=
    fun P ↦ P.1.1.map inlEmb ∪ P.2.1.map inrEmb
  have hmapDisjoint : ∀ (A : Finset (Fin ell₁))
      (B : Finset (Fin ell₂)),
      Disjoint (A.map inlEmb) (B.map inrEmb) := by
    intro A B
    rw [Finset.disjoint_left]
    intro u huA huB
    obtain ⟨i, _hiA, hiu⟩ := Finset.mem_map.mp huA
    obtain ⟨j, _hjB, hju⟩ := Finset.mem_map.mp huB
    have hij := hiu.trans hju.symm
    change Sum.inl i = Sum.inr j at hij
    cases hij
  have hmemInl : ∀ (P : ↥L₁ × ↥L₂) (i : Fin ell₁),
      Sum.inl i ∈ combined P ↔ i ∈ P.1.1 := by
    intro P i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
        change Sum.inl j = Sum.inl i at hji
        have hji' : j = i := Sum.inl_injective hji
        subst j
        exact hj
      · obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hi
        change Sum.inr j = Sum.inl i at hji
        cases hji
    · intro hi
      exact Finset.mem_union_left _
        (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  have hmemInr : ∀ (P : ↥L₁ × ↥L₂) (j : Fin ell₂),
      Sum.inr j ∈ combined P ↔ j ∈ P.2.1 := by
    intro P j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨i, _hi, hij⟩ := Finset.mem_map.mp hj
        change Sum.inl i = Sum.inr j at hij
        cases hij
      · obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp hj
        change Sum.inr i = Sum.inr j at hij
        have hij' : i = j := Sum.inr_injective hij
        subst i
        exact hi
    · intro hj
      exact Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
  let encode : ↥L₁ × ↥L₂ → AddSubgroup.zmultiples y := fun P ↦
    ⟨(∑ i ∈ P.1.1, (g (e₁ i) - a₁)) +
        ∑ j ∈ P.2.1, (g (e₂ j) - a₂),
      AddSubgroup.add_mem _
        (AddSubgroup.sum_mem _ fun i _ ↦ hmem₁ i)
        (AddSubgroup.sum_mem _ fun j _ ↦ hmem₂ j)⟩
  have hencode : Function.Injective encode := by
    intro P Q hPQ
    have hvalue := congrArg Subtype.val hPQ
    have hP₁card : P.1.1.card = k₁ :=
      (Finset.mem_powersetCard.mp P.1.property).2
    have hP₂card : P.2.1.card = k₂ :=
      (Finset.mem_powersetCard.mp P.2.property).2
    have hQ₁card : Q.1.1.card = k₁ :=
      (Finset.mem_powersetCard.mp Q.1.property).2
    have hQ₂card : Q.2.1.card = k₂ :=
      (Finset.mem_powersetCard.mp Q.2.property).2
    have hsum :
        (∑ i ∈ P.1.1, g (e₁ i)) + ∑ j ∈ P.2.1, g (e₂ j) =
          (∑ i ∈ Q.1.1, g (e₁ i)) +
            ∑ j ∈ Q.2.1, g (e₂ j) := by
      dsimp only [encode] at hvalue
      simp_rw [Finset.sum_sub_distrib, Finset.sum_const] at hvalue
      rw [hP₁card, hP₂card, hQ₁card, hQ₂card] at hvalue
      calc
        (∑ i ∈ P.1.1, g (e₁ i)) + ∑ j ∈ P.2.1, g (e₂ j) =
            (((∑ i ∈ P.1.1, g (e₁ i)) - k₁ • a₁) +
              ((∑ j ∈ P.2.1, g (e₂ j)) - k₂ • a₂)) +
              (k₁ • a₁ + k₂ • a₂) := by abel
        _ = (((∑ i ∈ Q.1.1, g (e₁ i)) - k₁ • a₁) +
              ((∑ j ∈ Q.2.1, g (e₂ j)) - k₂ • a₂)) +
              (k₁ • a₁ + k₂ • a₂) := by rw [hvalue]
        _ = (∑ i ∈ Q.1.1, g (e₁ i)) +
              ∑ j ∈ Q.2.1, g (e₂ j) := by abel
    have hPcard : (combined P).card = k₁ + k₂ := by
      dsimp only [combined]
      rw [Finset.card_union_of_disjoint
          (hmapDisjoint P.1.1 P.2.1),
        Finset.card_map, Finset.card_map, hP₁card, hP₂card]
    have hQcard : (combined Q).card = k₁ + k₂ := by
      dsimp only [combined]
      rw [Finset.card_union_of_disjoint
          (hmapDisjoint Q.1.1 Q.2.1),
        Finset.card_map, Finset.card_map, hQ₁card, hQ₂card]
    have hPsum :
        (∑ u ∈ combined P, g (e u)) =
          (∑ i ∈ P.1.1, g (e₁ i)) +
            ∑ j ∈ P.2.1, g (e₂ j) := by
      dsimp only [combined]
      rw [Finset.sum_union (hmapDisjoint P.1.1 P.2.1),
        Finset.sum_map, Finset.sum_map]
      rfl
    have hQsum :
        (∑ u ∈ combined Q, g (e u)) =
          (∑ i ∈ Q.1.1, g (e₁ i)) +
            ∑ j ∈ Q.2.1, g (e₂ j) := by
      dsimp only [combined]
      rw [Finset.sum_union (hmapDisjoint Q.1.1 Q.2.1),
        Finset.sum_map, Finset.sum_map]
      rfl
    have hcombined :
        combined P = combined Q := by
      apply validTuple_subsetSum_eq_of_card_eq g hg e
      · omega
      · rw [hPsum, hQsum]
        exact hsum
    apply Prod.ext
    · apply Subtype.ext
      ext i
      calc
        i ∈ P.1.1 ↔ Sum.inl i ∈ combined P := (hmemInl P i).symm
        _ ↔ Sum.inl i ∈ combined Q := by rw [hcombined]
        _ ↔ i ∈ Q.1.1 := hmemInl Q i
    · apply Subtype.ext
      ext j
      calc
        j ∈ P.2.1 ↔ Sum.inr j ∈ combined P := (hmemInr P j).symm
        _ ↔ Sum.inr j ∈ combined Q := by rw [hcombined]
        _ ↔ j ∈ Q.2.1 := hmemInr Q j
  have hcard := Fintype.card_le_of_injective encode hencode
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hcard
  exact hcard

/-- Finset form of the two-coset fixed-layer capacity theorem. -/
theorem choose_mul_choose_le_addOrderOf_of_disjoint_kernelCosets
    [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (A C : Finset (Fin n)) (hA : A.Nonempty) (hC : C.Nonempty)
    (hdisjoint : Disjoint A C)
    (hAcoset : ∀ b ∈ A, ∀ c ∈ A,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (hCcoset : ∀ b ∈ C, ∀ c ∈ C,
      g b - g c ∈ AddSubgroup.zmultiples y)
    (k₁ k₂ : ℕ) :
    A.card.choose k₁ * C.card.choose k₂ ≤ addOrderOf y := by
  classical
  obtain ⟨a, haA⟩ := hA
  obtain ⟨c, hcC⟩ := hC
  let eA : Fin A.card ↪ Fin n := (A.orderEmbOfFin rfl).toEmbedding
  let eC : Fin C.card ↪ Fin n := (C.orderEmbOfFin rfl).toEmbedding
  have heA : ∀ i, eA i ∈ A := by
    intro i
    exact A.orderEmbOfFin_mem rfl i
  have heC : ∀ j, eC j ∈ C := by
    intro j
    exact C.orderEmbOfFin_mem rfl j
  have hcross : ∀ i j, eA i ≠ eC j := by
    intro i j hij
    apply Finset.disjoint_left.mp hdisjoint (heA i)
    rw [hij]
    exact heC j
  exact choose_mul_choose_le_addOrderOf_of_two_kernelCosets
    g hg eA eC hcross (g a) (g c) y
      (fun i ↦ hAcoset (eA i) (heA i) a haA)
      (fun j ↦ hCcoset (eC j) (heC j) c hcC) k₁ k₂

/-- The old retained coordinate inserted in every middle exchange. -/
def primitiveMiddleInsertedCoordinate
    {q : ℕ} {g : Fin n → ZMod (2 ^ 6 * q)}
    {y : ZMod (2 ^ 6 * q)} {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Fin n :=
  if k₀ = -1 then p.x else p.z

/-- Lossless capacity endpoint of the middle family.  The leaf coset and the
selected-owner coset either merge, giving an exponential union bound, or
remain disjoint, giving all products of their binomial-layer bounds. -/
def PrimitiveMiddleExchangeCosetCapacity
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      (∀ b : ↥B, (b : Fin n) ∈ S →
        p.weight b = 2 * k₀ ∧
        ((k₀ = -1 ∧
            g (b : Fin n) - g p.x ∈ AddSubgroup.zmultiples y ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.z)) = 64) ∨
          (k₀ = 0 ∧
            g (b : Fin n) - g p.z ∈ AddSubgroup.zmultiples y ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.x)) = 64))) ∧
      let C := insert (primitiveMiddleInsertedCoordinate p k₀) S
      C.card = S.card + 1 ∧
      (2 ^ ((((Finset.univ : Finset (Fin d)).image leaf) ∪ C).card - 1) ≤ q ∨
        ∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q)

/-- The primitive middle geometry itself supplies a two-coset capacity
dichotomy, before any further leaf-terminal case analysis. -/
theorem PrimitiveMiddleExchangeFamily.toCosetCapacity
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleExchangeFamily g y B)
    (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    PrimitiveMiddleExchangeCosetCapacity g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r S
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hrNotB : r ∉ B := by
    rcases hmiddle with hk | hk
    · simp only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
      exact p.x_not_mem
    · have hkNe : k₀ ≠ -1 := by omega
      simp only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
      exact p.z_not_mem
  have hrNotS : r ∉ S := fun hrS ↦ hrNotB (hSsub hrS)
  have hCcard : C.card = S.card + 1 := by
    simp only [C, Finset.card_insert_of_notMem hrNotS]
  have hselected : ∀ b ∈ S,
      g b - g r ∈ AddSubgroup.zmultiples y := by
    intro b hbS
    let bB : ↥B := ⟨b, hSsub hbS⟩
    have hrow := hrows bB hbS
    rcases hmiddle with hk | hk
    · rcases hrow.2 with hminus | hzero
      · simpa only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
          using hminus.2.1
      · omega
    · have hkNe : k₀ ≠ -1 := by omega
      rcases hrow.2 with hminus | hzero
      · omega
      · simpa only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
          using hzero.2.1
  have hCcoset : ∀ b ∈ C, ∀ c ∈ C,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbC c hcC
    rcases Finset.mem_insert.mp hbC with rfl | hbS
    · rcases Finset.mem_insert.mp hcC with rfl | hcS
      · simp
      · have hneg :=
          (AddSubgroup.zmultiples y).neg_mem (hselected c hcS)
        convert hneg using 1
        module
    · rcases Finset.mem_insert.mp hcC with rfl | hcS
      · exact hselected b hbS
      · have hsub :=
          (AddSubgroup.zmultiples y).sub_mem
            (hselected b hbS) (hselected c hcS)
        convert hsub using 1
        module
  have hleafDisp : ∀ i,
      g (leaf i) - base ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hLcoset : ∀ b ∈ L, ∀ c ∈ L,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbL c hcL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hbL
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hcL
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem (hleafDisp i) (hleafDisp j)
    convert hsub using 1
    module
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hLnonempty : L.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hCnonempty : C.Nonempty :=
    ⟨r, Finset.mem_insert_self _ _⟩
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  refine ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows, ?_⟩
  dsimp only
  refine ⟨by simpa only [C, r] using hCcard, ?_⟩
  by_cases hdisjoint : Disjoint L C
  · right
    intro i j
    have hcap :=
      choose_mul_choose_le_addOrderOf_of_disjoint_kernelCosets
        g hg y L C hLnonempty hCnonempty hdisjoint
          hLcoset hCcoset i j
    rw [hLcard, hCcard, horder] at hcap
    exact hcap
  · left
    obtain ⟨z, hzL, hzC⟩ :=
      Finset.not_disjoint_iff.mp hdisjoint
    have hunionCoset : ∀ b ∈ L ∪ C, ∀ c ∈ L ∪ C,
        g b - g c ∈ AddSubgroup.zmultiples y := by
      intro b hb c hc
      rcases Finset.mem_union.mp hb with hbL | hbC
      · rcases Finset.mem_union.mp hc with hcL | hcC
        · exact hLcoset b hbL c hcL
        · have hadd :=
            (AddSubgroup.zmultiples y).add_mem
              (hLcoset b hbL z hzL) (hCcoset z hzC c hcC)
          convert hadd using 1
          module
      · rcases Finset.mem_union.mp hc with hcL | hcC
        · have hadd :=
            (AddSubgroup.zmultiples y).add_mem
              (hCcoset b hbC z hzC) (hLcoset z hzL c hcL)
          convert hadd using 1
          module
        · exact hCcoset b hbC c hcC
    have hunionNonempty : (L ∪ C).Nonempty :=
      hLnonempty.mono (Finset.subset_union_left)
    have hcap :=
      two_pow_pred_le_addOrderOf_of_valid_kernelCoset
        g hg y (L ∪ C) hunionNonempty hunionCoset
    rw [horder] at hcap
    simpa only [L, C, r] using hcap

end MinModulus
