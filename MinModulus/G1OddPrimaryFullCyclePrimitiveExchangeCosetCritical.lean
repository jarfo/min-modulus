/-
# Critical arithmetic of the primitive middle two-coset capacity

At an exact-two sixth-stratum critical modulus, the odd factor satisfies

    16 * q < 2^|B|.

Combining this strict upper bound with the exact coset dichotomy gives a
lossless numerical residual.  If the leaf and selected-owner cosets coincide,
at least five deleted owners lie outside their union and are separated from
that saturated coset.  If the cosets are distinct, every product layer
remains available and the middle layers give

    388960 * choose(d, floor(d/2)) < 2^|B|.

The constant is `16 * choose(17,8)`; it uses only the uniform lower bound of
sixteen selected owners and is therefore independent of dimension.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeCosetCapacity

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The exact critical upper bound after an exact-two transversal deletes
`B.card = n-2` coordinates. -/
theorem sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
    {q : ℕ} (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6) :
    16 * q < 2 ^ B.card := by
  have hBcard : B.card ≤ n := by
    simpa using Finset.card_le_univ B
  have hn : n = B.card + 2 := by omega
  have hcriticalPow : 2 ^ 6 * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  rw [hn, pow_add] at hcriticalPow
  norm_num at hcriticalPow
  omega

/-- A kernel-coset subset in a critical exact-two state leaves at least four
deleted coordinates outside it. -/
theorem card_add_four_le_transversalCard_of_critical_kernelCoset
    {q : ℕ} (B U : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hU : U.Nonempty) (hcap : 2 ^ (U.card - 1) ≤ q) :
    U.card + 4 ≤ B.card := by
  have hcriticalSixteen :=
    sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
      B hretained hcritical
  have hpow : 2 ^ (U.card + 3) < 2 ^ B.card := by
    calc
      2 ^ (U.card + 3) = 16 * 2 ^ (U.card - 1) := by
        have hUcard : 1 ≤ U.card := Finset.one_le_card.mpr hU
        rw [show U.card + 3 = 4 + (U.card - 1) by omega, pow_add]
        norm_num
      _ ≤ 16 * q := Nat.mul_le_mul_left 16 hcap
      _ < 2 ^ B.card := hcriticalSixteen
  have hexponents : U.card + 3 < B.card :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow
  omega

/-- If the critical coset union contains one retained coordinate outside the
transversal, its four-cardinality deficit leaves at least five deleted owners
outside the union. -/
theorem five_le_card_transversal_sdiff_of_card_add_four_le
    (B U : Finset (Fin n)) {r : Fin n}
    (hrU : r ∈ U) (hrB : r ∉ B)
    (hgap : U.card + 4 ≤ B.card) :
    5 ≤ (B \ U).card := by
  have hrInter : r ∉ B ∩ U := by
    intro hr
    exact hrB (Finset.mem_inter.mp hr).1
  have hsubset : insert r (B ∩ U) ⊆ U := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbInter
    · exact hrU
    · exact (Finset.mem_inter.mp hbInter).2
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hrInter] at hcard
  have hpartition := Finset.card_sdiff_add_card_inter B U
  omega

/-- The selected-owner middle layer supplies the explicit factor
`choose(17,8)=24310` in every distinct-coset branch. -/
theorem central_leaf_product_lt_two_pow_transversalCard_of_critical
    {q d s : ℕ} (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hs : 16 ≤ s)
    (hcap : ∀ i j : ℕ, d.choose i * (s + 1).choose j ≤ q) :
    388960 * d.choose (d / 2) < 2 ^ B.card := by
  have hchooseRaw : (17 : ℕ).choose 8 ≤ (s + 1).choose 8 :=
    Nat.choose_le_choose 8 (by omega)
  have hchoose : 24310 ≤ (s + 1).choose 8 := hchooseRaw
  have hproduct : 24310 * d.choose (d / 2) ≤ q := by
    calc
      24310 * d.choose (d / 2) ≤
          (s + 1).choose 8 * d.choose (d / 2) :=
        Nat.mul_le_mul_right _ hchoose
      _ = d.choose (d / 2) * (s + 1).choose 8 := by ac_rfl
      _ ≤ q := hcap (d / 2) 8
  have hcriticalSixteen :=
    sixteen_mul_oddFactor_lt_two_pow_transversalCard_of_critical
      B hretained hcritical
  calc
    388960 * d.choose (d / 2) =
        16 * (24310 * d.choose (d / 2)) := by ring
    _ ≤ 16 * q := Nat.mul_le_mul_left 16 hproduct
    _ < 2 ^ B.card := hcriticalSixteen

/-- Exact critical residual of the primitive middle family.  All geometric
data from the capacity endpoint are retained; criticality only sharpens its
two alternatives by the four-coordinate gap or the explicit middle-layer
inequality. -/
def PrimitiveMiddleExchangeCriticalCosetResidual
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
      let r := primitiveMiddleInsertedCoordinate p k₀
      (∀ b : ↥B,
        ((b : Fin n) ∈ S ↔
          g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) ∧
      let C := insert (primitiveMiddleInsertedCoordinate p k₀) S
      let L := (Finset.univ : Finset (Fin d)).image leaf
      C.card = S.card + 1 ∧
      ((2 ^ ((L ∪ C).card - 1) ≤ q ∧
          (∀ b ∈ L, ∀ c ∈ C,
            g b - g c ∈ AddSubgroup.zmultiples y) ∧
          (L ∪ C).card + 4 ≤ B.card ∧
          5 ≤ (B \ (L ∪ C)).card ∧
          (∀ b ∈ B \ (L ∪ C), ∀ c ∈ L ∪ C,
            g b - g c ∉ AddSubgroup.zmultiples y)) ∨
        ((∀ b ∈ L, ∀ c ∈ C,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          (∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q) ∧
          388960 * d.choose (d / 2) < 2 ^ B.card))

/-- Install the exact critical arithmetic on the same primitive middle
family and the same two kernel cosets. -/
theorem PrimitiveMiddleExchangeFamily.toCriticalCosetResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hfamily : PrimitiveMiddleExchangeFamily g y B)
    (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    PrimitiveMiddleExchangeCriticalCosetResidual g y B leaf := by
  classical
  rcases hfamily.toCosetCapacity
      g hg y hyq hfullOdd B hd leaf hleaf base hspan with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows, hcomplete,
      hCcard, hcase⟩
  refine ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows,
    hcomplete, hCcard, ?_⟩
  let C : Finset (Fin n) :=
    insert (primitiveMiddleInsertedCoordinate p k₀) S
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  change
    ((2 ^ ((L ∪ C).card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∈ AddSubgroup.zmultiples y) ∧
        (L ∪ C).card + 4 ≤ B.card ∧
        5 ≤ (B \ (L ∪ C)).card ∧
        (∀ b ∈ B \ (L ∪ C), ∀ c ∈ L ∪ C,
          g b - g c ∉ AddSubgroup.zmultiples y)) ∨
      ((∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        (∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q) ∧
        388960 * d.choose (d / 2) < 2 ^ B.card))
  change
    ((2 ^ ((L ∪ C).card - 1) ≤ q ∧
        (∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∈ AddSubgroup.zmultiples y)) ∨
      ((∀ b ∈ L, ∀ c ∈ C,
          g b - g c ∉ AddSubgroup.zmultiples y) ∧
        ∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q)) at hcase
  rcases hcase with ⟨hcap, hcross⟩ | ⟨hcross, hcap⟩
  · left
    refine ⟨hcap, hcross, ?_⟩
    have hLnonempty : L.Nonempty := by
      apply Finset.card_pos.mp
      rw [show L.card = d by
        simp only [L]
        rw [Finset.card_image_of_injective _ hleaf]
        simp]
      exact hd
    have hgap := card_add_four_le_transversalCard_of_critical_kernelCoset
      B (L ∪ C) hretained hcritical
        (hLnonempty.mono Finset.subset_union_left) hcap
    refine ⟨hgap, ?_⟩
    let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
    have hrC : r ∈ C := by
      exact Finset.mem_insert_self _ _
    have hrU : r ∈ L ∪ C := Finset.mem_union_right _ hrC
    have hrB : r ∉ B := by
      rcases hmiddle with hk | hk
      · simpa only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
          using p.x_not_mem
      · have hkNe : k₀ ≠ -1 := by omega
        simpa only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
          using p.z_not_mem
    have hfive := five_le_card_transversal_sdiff_of_card_add_four_le
      B (L ∪ C) hrU hrB hgap
    refine ⟨hfive, ?_⟩
    intro b hbOutside c hcUnion hbc
    let bB : ↥B := ⟨b, (Finset.mem_sdiff.mp hbOutside).1⟩
    have hbNotS : b ∉ S := by
      intro hbS
      apply (Finset.mem_sdiff.mp hbOutside).2
      exact Finset.mem_union_right _
        (Finset.mem_insert_of_mem hbS)
    have hbNotParallel :
        g b - g r ∉ AddSubgroup.zmultiples y := by
      intro hbParallel
      apply hbNotS
      exact (hcomplete bB).2 hbParallel
    have hcParallel :
        g c - g r ∈ AddSubgroup.zmultiples y := by
      rcases Finset.mem_union.mp hcUnion with hcL | hcC
      · exact hcross c hcL r hrC
      · rcases Finset.mem_insert.mp hcC with hcr | hcS
        · subst c
          change g r - g r ∈ AddSubgroup.zmultiples y
          simp
        · let cB : ↥B := ⟨c, hSsub hcS⟩
          exact (hcomplete cB).1 hcS
    have hsum :=
      (AddSubgroup.zmultiples y).add_mem hbc hcParallel
    apply hbNotParallel
    convert hsum using 1
    module
  · right
    exact ⟨hcross, hcap,
      central_leaf_product_lt_two_pow_transversalCard_of_critical
        B hretained hcritical hScard hcap⟩

end MinModulus
