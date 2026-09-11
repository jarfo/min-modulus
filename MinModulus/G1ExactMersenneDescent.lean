import MinModulus.G1MersenneCharge

namespace MinModulus

/-- Every coordinate of an embedded valid doubling tuple generates its whole
span and gives the same exact Mersenne divisor of the odd factor. -/
theorem exactMersenne_oddFactor_kernel_of_valid_doubling_subtuple
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (hd : 2 ≤ d)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (leaf : Fin d ↪ Fin n) (base : ZMod (2 ^ t * q))
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j, g (leaf (R j)) - base = 2 • (g (leaf j) - base))
    (i : Fin d) :
    AddSubgroup.closure (Set.range (fun j ↦ g (leaf j) - base)) =
        AddSubgroup.zmultiples (g (leaf i) - base) ∧
      addOrderOf (g (leaf i) - base) = 2 ^ d - 1 ∧
      addOrderOf (g (leaf i) - base) ∣ q := by
  let x : Fin d → ZMod (2 ^ t * q) := fun j ↦ g (leaf j) - base
  have hx : ValidTuple x :=
    validTuple_sub_const (fun j ↦ g (leaf j)) (validTuple_embedding leaf g hg) base
  have hspan := doubling_span_eq_zmultiples_of_valid hd x hx R hdouble i
  have horder := addOrderOf_eq_mersenne_of_valid_doubling hd x hx R hdouble i
  have hodd : Odd (addOrderOf (x i)) := by
    rw [horder]
    exact odd_two_pow_sub_one (by omega)
  have hdiv : addOrderOf (x i) ∣ 2 ^ t * q := by
    simpa using addOrderOf_dvd_card (x := x i)
  exact ⟨hspan, horder, (hodd.coprime_two_right.pow_right t).dvd_of_dvd_mul_left hdiv⟩

/-- An actual valid doubling subtuple supplies its own exact-order generator
and minimal transversal. No order or deletion set is assumed. -/
theorem exists_exactMersenne_minimalTransversal_descent_of_doubling_subtuple
    {m d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t) (hd : 2 ≤ d)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    (leaf : Fin d ↪ Fin (m + 1)) (base : ZMod (2 ^ t * q))
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j, g (leaf (R j)) - base = 2 • (g (leaf j) - base))
    (i : Fin d) :
    ∃ B : Finset (Fin (m + 1)),
      AddSubgroup.closure (Set.range (fun j ↦ g (leaf j) - base)) =
          AddSubgroup.zmultiples (g (leaf i) - base) ∧
        addOrderOf (g (leaf i) - base) = 2 ^ d - 1 ∧
        OddPrimaryFullCycleMinimalTransversalChargeDescent
          g (g (leaf i) - base) B d ∧
        (OddPrimaryRecursiveCounterexample (m + 1) B.card t q
            (addOrderOf (g (leaf i) - base)) ∨ d ≤ B.card) := by
  obtain ⟨hspan, horder, hdiv⟩ :=
    exactMersenne_oddFactor_kernel_of_valid_doubling_subtuple hd g hg leaf base R hdouble i
  have hlower : 2 ^ (d - 1) ≤ addOrderOf (g (leaf i) - base) := by
    rw [horder]
    have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (d - 1) := by rw [pow_succ, Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    omega
  obtain ⟨B, hdescent⟩ := exists_fullCycleMinimalTransversalChargeDescent
    ht hd g hg hcritical hlower hdiv
  exact ⟨B, hspan, horder, hdescent,
    hdescent.recursive_or_cycle_le_card (by omega)⟩

/-- The saturated pure-star algebra constructs an exact Mersenne kernel and
its sharpened transversal descent directly from the original leaf cycle. -/
theorem PureEdgeStarLeafPermutationAlgebra.exists_exactMersenne_minimalTransversal_descent
    {m d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center) :
    ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
      AddSubgroup.closure (Set.range (fun j : Fin d ↦
        g (T^[j.val] a : Fin (m + 1)) - (h + g r))) =
          AddSubgroup.zmultiples y ∧
        addOrderOf y = 2 ^ d - 1 ∧
        OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d ∧
        (OddPrimaryRecursiveCounterexample (m + 1) B.card t q
          (addOrderOf y) ∨ d ≤ B.card) := by
  let leafFun : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  have hleaf : Function.Injective leafFun := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hjk
  let leaf : Fin d ↪ Fin (m + 1) := ⟨leafFun, hleaf⟩
  obtain ⟨P, S, hlocal, _hsum⟩ := halg
  let R : Equiv.Perm (Fin d) := P.symm.trans S
  have hdouble : ∀ j, g (leaf (R j)) - (h + g r) =
      2 • (g (leaf j) - (h + g r)) := by
    intro j
    have hrel : (2 : ℤ) • g (leaf j) =
        h + g r + g (leaf (R j)) := by
      simpa [leaf, leafFun, R] using (hlocal (P.symm j)).2.2.2.2
    rw [two_zsmul] at hrel
    rw [two_nsmul]
    calc
      g (leaf (R j)) - (h + g r) =
          (h + g r + g (leaf (R j))) -
            ((h + g r) + (h + g r)) := by abel
      _ = (g (leaf j) + g (leaf j)) -
            ((h + g r) + (h + g r)) := by rw [← hrel]
      _ = (g (leaf j) - (h + g r)) +
            (g (leaf j) - (h + g r)) := by abel
  let i : Fin d := ⟨0, by have := hcycle.1; omega⟩
  obtain ⟨B, hspan, horder, hdescent, hsplit⟩ :=
    exists_exactMersenne_minimalTransversal_descent_of_doubling_subtuple
      ht hcycle.1 g hg hcritical leaf (h + g r) R hdouble i
  exact ⟨g (leaf i) - (h + g r), B, hspan, horder, hdescent, hsplit⟩

end MinModulus
