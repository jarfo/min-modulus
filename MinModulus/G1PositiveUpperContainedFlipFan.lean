/-
# Flip-exchange fans for contained adjacent nesting

In the contained branch of milestone 2da, `supp(u) ⊆ supp(q)` and

  `B_q \ B_u = (A_u \ A_q) ∪ (supp(q) \ supp(u))`.

The first term is the singleton sign-flip coordinate.  If the supports were
equal, subtracting the two collision equations would make twice that anchored
difference zero.  In the genuine even-cyclic residual this yields common
touch, so support containment is actually strict.

For support depth `d`, exchange the flip coordinate in `supp(u)` with each of
the `d` external coordinates.  Together with the unchanged root support this
gives `d+1` distinct blocked signatures of root cardinality.  Their value
layers have root weight and pairwise half-overlap, producing a normalized
flip fan entirely inside the subset-sum range.
-/
import MinModulus.G1PositiveUpperAdjacentSupportSplit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Equal-support adjacent nesting makes twice the unique flip difference
zero. -/
theorem equalSupport_adjacentPositiveNesting_exists_flip_add_self_eq_zero
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1)
    (hsupportEq : reducedCollisionSupport u = reducedCollisionSupport q) :
    ∃ x ∈ u.val.1 \ q.val.1, diff g x + diff g x = 0 := by
  have hdrop : ¬(reducedCollisionDroppedSupport u q).Nonempty := by
    rw [reducedCollisionDroppedSupport, hsupportEq, Finset.sdiff_self]
    exact Finset.not_nonempty_empty
  have hcontained := containedAdjacentPositiveNesting_negative_sSubset
    hg hh hh0 q u hq hu hnest hadj hdrop
  have hdecomp :=
    containedAdjacentPositiveNesting_negativeDiff_eq_flip_union_external
      hg hh hh0 q u hq hu hnest hadj hdrop
  have hexternal : reducedCollisionExternalSupport u q = ∅ := by
    rw [reducedCollisionExternalSupport, ← hsupportEq, Finset.sdiff_self]
  have hBdiff : q.val.2 \ u.val.2 = u.val.1 \ q.val.1 := by
    simpa [hexternal] using hdecomp
  let D := u.val.1 \ q.val.1
  have hDcard : D.card = 1 :=
    (adjacentPositiveNesting_uniqueFlip
      hg hh hh0 q u hq hu hnest hadj).1
  have hAunion : q.val.1 ∪ D = u.val.1 := by
    exact Finset.union_sdiff_of_subset hnest.1
  have hBunion : u.val.2 ∪ D = q.val.2 := by
    dsimp [D]
    rw [← hBdiff]
    exact Finset.union_sdiff_of_subset hcontained.2.1
  have hAD : Disjoint q.val.1 D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    exact (Finset.mem_sdiff.mp hxD).2 hxA
  have hBD : Disjoint u.val.2 D := by
    rw [Finset.disjoint_left]
    intro x hxB hxD
    exact Finset.disjoint_left.mp u.property.1
      (Finset.mem_sdiff.mp hxD).1 hxB
  have hsumA : ssum g u.val.1 = ssum g q.val.1 + ssum g D := by
    rw [← hAunion, ssum_union_of_disjoint g hAD]
  have hsumB : ssum g q.val.2 = ssum g u.val.2 + ssum g D := by
    rw [← hBunion, ssum_union_of_disjoint g hBD]
  have huEq := u.property.2
  have hqEq := q.property.2
  rw [hsumA] at huEq
  rw [hsumB] at hqEq
  have hDzero : ssum g D + ssum g D = 0 := by
    calc
      ssum g D + ssum g D =
          (ssum g q.val.1 + ssum g D) -
            (ssum g u.val.2 + h) := by rw [hqEq]; abel
      _ = 0 := by rw [huEq, sub_self]
  rcases Finset.card_eq_one.mp hDcard with ⟨x, hx⟩
  refine ⟨x, by simp [D, hx], ?_⟩
  simpa [D, hx, ssum] using hDzero

/-- In a group with a unique nonzero involution, equal-support adjacent
nesting already gives common touch. -/
theorem commonTouched_of_equalSupport_adjacentPositiveNesting
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1)
    (hsupportEq : reducedCollisionSupport u = reducedCollisionSupport q) :
    ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0 := by
  rcases equalSupport_adjacentPositiveNesting_exists_flip_add_self_eq_zero
    hg hh hh0 q u hq hu hnest hadj hsupportEq with ⟨x, hx, hdouble⟩
  have hcoords : (2 : ℤ) • g x.succ = (2 : ℤ) • g 0 := by
    have hsub : (g x.succ + g x.succ) - (g 0 + g 0) = 0 := by
      calc
        (g x.succ + g x.succ) - (g 0 + g 0) =
            diff g x + diff g x := by simp [diff]; abel
        _ = 0 := hdouble
    have heq := sub_eq_zero.mp hsub
    simpa [two_zsmul] using heq
  exact common_touched_of_two_smul_eq g hg hh hh0 hunique
    (Fin.succ_ne_zero x) hcoords

/-- Indices of the flip-exchange fan: the unchanged root signature and one
exchange for every pair consisting of the unique flip and an external
coordinate. -/
noncomputable def containedAdjacentFlipFanIndices
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    Finset (Option (Fin m × Fin m)) := by
  classical
  exact insert none
    (((u.val.1 \ q.val.1) ×ˢ reducedCollisionExternalSupport u q).image some)

/-- Replace one root-support coordinate by one coordinate external to the
root support. -/
def containedAdjacentFlipExchangeSupport
    {g : Fin (m + 1) → G} {h : G}
    (u : ReducedSubsetSumCollision g h) (p : Fin m × Fin m) :
    Finset (Fin m) :=
  insert p.2 ((reducedCollisionSupport u).erase p.1)

/-- Value layer indexed by a flip-exchange fan signature. -/
noncomputable def containedAdjacentFlipFanLayer
    {g : Fin (m + 1) → G} {h : G}
    (_q u : ReducedSubsetSumCollision g h) :
    Option (Fin m × Fin m) → Finset G
  | none => blockedSignatureValueLayer g (reducedCollisionSupport u)
  | some p => blockedSignatureValueLayer g
      (containedAdjacentFlipExchangeSupport u p)

omit [DecidableEq G] in
@[simp] theorem none_mem_containedAdjacentFlipFanIndices
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    none ∈ containedAdjacentFlipFanIndices q u := by
  classical
  simp [containedAdjacentFlipFanIndices]

omit [DecidableEq G] in
@[simp] theorem some_mem_containedAdjacentFlipFanIndices_iff
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) {p : Fin m × Fin m} :
    some p ∈ containedAdjacentFlipFanIndices q u ↔
      p.1 ∈ u.val.1 \ q.val.1 ∧
        p.2 ∈ reducedCollisionExternalSupport u q := by
  classical
  simp [containedAdjacentFlipFanIndices]

omit [DecidableEq G] in
/-- The flip-exchange fan has one root layer plus one layer per external
coordinate. -/
theorem card_containedAdjacentFlipFanIndices
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hflipCard : (u.val.1 \ q.val.1).card = 1) :
    (containedAdjacentFlipFanIndices q u).card =
      (reducedCollisionExternalSupport u q).card + 1 := by
  classical
  have hnone : none ∉
      (((u.val.1 \ q.val.1) ×ˢ
        reducedCollisionExternalSupport u q).image some) := by simp
  have himage :
      ((((u.val.1 \ q.val.1) ×ˢ
        reducedCollisionExternalSupport u q).image some).card) =
      ((u.val.1 \ q.val.1) ×ˢ
        reducedCollisionExternalSupport u q).card := by
    apply Finset.card_image_of_injective
    intro p z hpz
    exact Option.some.inj hpz
  rw [containedAdjacentFlipFanIndices,
    Finset.card_insert_of_notMem hnone, himage, Finset.card_product,
    hflipCard]
  omega

omit [DecidableEq G] in
/-- Under support containment, the external-support cardinality is exactly
the support depth. -/
theorem card_externalSupport_eq_depth_of_support_subset
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hsupport : reducedCollisionSupport u ⊆ reducedCollisionSupport q) :
    (reducedCollisionExternalSupport u q).card =
      reducedCollisionSupportDepth u q := by
  rw [reducedCollisionExternalSupport,
    Finset.card_sdiff_of_subset hsupport, reducedCollisionSupportDepth]

omit [DecidableEq G] in
/-- Every exchange signature has the root support cardinality. -/
theorem card_containedAdjacentFlipExchangeSupport
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) {p : Fin m × Fin m}
    (hp : p.1 ∈ u.val.1 \ q.val.1 ∧
      p.2 ∈ reducedCollisionExternalSupport u q) :
    (containedAdjacentFlipExchangeSupport u p).card =
      (reducedCollisionSupport u).card := by
  have hxSupp : p.1 ∈ reducedCollisionSupport u := by
    simp [reducedCollisionSupport, (Finset.mem_sdiff.mp hp.1).1]
  have heNotSupp : p.2 ∉ reducedCollisionSupport u :=
    (Finset.mem_sdiff.mp hp.2).2
  have heNotErase : p.2 ∉ (reducedCollisionSupport u).erase p.1 := by
    intro he
    exact heNotSupp (Finset.mem_of_mem_erase he)
  have hsupportPos : 0 < (reducedCollisionSupport u).card :=
    Finset.card_pos.mpr ⟨p.1, hxSupp⟩
  rw [containedAdjacentFlipExchangeSupport,
    Finset.card_insert_of_notMem heNotErase,
    Finset.card_erase_of_mem hxSupp]
  omega

omit [DecidableEq G] in
/-- A genuine exchange signature differs from the root signature. -/
theorem containedAdjacentFlipExchangeSupport_ne_root
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) {p : Fin m × Fin m}
    (hp : p.1 ∈ u.val.1 \ q.val.1 ∧
      p.2 ∈ reducedCollisionExternalSupport u q) :
    containedAdjacentFlipExchangeSupport u p ≠ reducedCollisionSupport u := by
  have hxSupp : p.1 ∈ reducedCollisionSupport u := by
    simp [reducedCollisionSupport, (Finset.mem_sdiff.mp hp.1).1]
  have heNotSupp : p.2 ∉ reducedCollisionSupport u :=
    (Finset.mem_sdiff.mp hp.2).2
  have hxe : p.1 ≠ p.2 := by
    intro hEq
    exact heNotSupp (hEq ▸ hxSupp)
  intro hEq
  have hxExchange : p.1 ∈ containedAdjacentFlipExchangeSupport u p := by
    rw [hEq]
    exact hxSupp
  simp [containedAdjacentFlipExchangeSupport, hxe, hxSupp] at hxExchange

omit [DecidableEq G] in
/-- The exchange-support map is injective on the flip/external product when
the flip set is a singleton. -/
theorem containedAdjacentFlipExchangeSupport_injective
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hflipCard : (u.val.1 \ q.val.1).card = 1)
    {p z : Fin m × Fin m}
    (hp : p.1 ∈ u.val.1 \ q.val.1 ∧
      p.2 ∈ reducedCollisionExternalSupport u q)
    (hz : z.1 ∈ u.val.1 \ q.val.1 ∧
      z.2 ∈ reducedCollisionExternalSupport u q)
    (hEq : containedAdjacentFlipExchangeSupport u p =
      containedAdjacentFlipExchangeSupport u z) :
    p = z := by
  rcases Finset.card_eq_one.mp hflipCard with ⟨x, hx⟩
  have hp1 : p.1 = x := by simpa [hx] using hp.1
  have hz1 : z.1 = x := by simpa [hx] using hz.1
  have hfirst : p.1 = z.1 := hp1.trans hz1.symm
  have hp2Not : p.2 ∉ reducedCollisionSupport u :=
    (Finset.mem_sdiff.mp hp.2).2
  have hz2Not : z.2 ∉ reducedCollisionSupport u :=
    (Finset.mem_sdiff.mp hz.2).2
  have hp2Right : p.2 ∈
      insert z.2 ((reducedCollisionSupport u).erase z.1) := by
    change p.2 ∈ containedAdjacentFlipExchangeSupport u z
    rw [← hEq]
    exact Finset.mem_insert_self _ _
  have hsecond : p.2 = z.2 := by
    rcases Finset.mem_insert.mp hp2Right with hpz | hpErase
    · exact hpz
    · exact False.elim (hp2Not (Finset.mem_of_mem_erase hpErase))
  exact Prod.ext hfirst hsecond

/-- Every flip-fan layer has root weight. -/
theorem card_containedAdjacentFlipFanLayer_eq_rootWeight
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (i : Option (Fin m × Fin m))
    (hi : i ∈ containedAdjacentFlipFanIndices q u) :
    (containedAdjacentFlipFanLayer q u i).card =
      reducedCollisionWeight (m := m) u := by
  cases i with
  | none =>
      simp [containedAdjacentFlipFanLayer,
        card_blockedSignatureValueLayer hg, reducedCollisionWeight,
        reducedCollisionSupport]
  | some p =>
      have hp := (some_mem_containedAdjacentFlipFanIndices_iff q u).mp hi
      rw [containedAdjacentFlipFanLayer,
        card_blockedSignatureValueLayer hg,
        card_containedAdjacentFlipExchangeSupport q u hp]
      rfl

/-- Distinct flip-fan layers overlap in at most half the root weight. -/
theorem two_mul_card_containedAdjacentFlipFanLayers_inter_le
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hflipCard : (u.val.1 \ q.val.1).card = 1)
    (i : Option (Fin m × Fin m))
    (hi : i ∈ containedAdjacentFlipFanIndices q u)
    (j : Option (Fin m × Fin m))
    (hj : j ∈ containedAdjacentFlipFanIndices q u)
    (hij : i ≠ j) :
    2 * (containedAdjacentFlipFanLayer q u i ∩
        containedAdjacentFlipFanLayer q u j).card ≤
      reducedCollisionWeight (m := m) u := by
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some z =>
          have hz :=
            (some_mem_containedAdjacentFlipFanIndices_iff q u).mp hj
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (reducedCollisionSupport u)
                (containedAdjacentFlipExchangeSupport u z)
                (card_containedAdjacentFlipExchangeSupport q u hz).symm
                (Ne.symm <|
                  containedAdjacentFlipExchangeSupport_ne_root q u hz)
          simpa [containedAdjacentFlipFanLayer, reducedCollisionWeight,
            reducedCollisionSupport] using hbound
  | some p =>
      have hp :=
        (some_mem_containedAdjacentFlipFanIndices_iff q u).mp hi
      cases j with
      | none =>
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (containedAdjacentFlipExchangeSupport u p)
                (reducedCollisionSupport u)
                (card_containedAdjacentFlipExchangeSupport q u hp)
                (containedAdjacentFlipExchangeSupport_ne_root q u hp)
          rw [card_containedAdjacentFlipExchangeSupport q u hp] at hbound
          simpa [containedAdjacentFlipFanLayer, reducedCollisionWeight,
            reducedCollisionSupport] using hbound
      | some z =>
          have hz :=
            (some_mem_containedAdjacentFlipFanIndices_iff q u).mp hj
          have hpz : p ≠ z := by
            intro hEq
            subst z
            exact hij rfl
          have hsupportNe : containedAdjacentFlipExchangeSupport u p ≠
              containedAdjacentFlipExchangeSupport u z := by
            intro hEq
            exact hpz (containedAdjacentFlipExchangeSupport_injective
              q u hflipCard hp hz hEq)
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (containedAdjacentFlipExchangeSupport u p)
                (containedAdjacentFlipExchangeSupport u z)
                ((card_containedAdjacentFlipExchangeSupport q u hp).trans
                  (card_containedAdjacentFlipExchangeSupport q u hz).symm)
                hsupportNe
          rw [card_containedAdjacentFlipExchangeSupport q u hp] at hbound
          simpa [containedAdjacentFlipFanLayer, reducedCollisionWeight,
            reducedCollisionSupport] using hbound

/-- Every flip-fan layer remains in the subset-sum range. -/
theorem biUnion_containedAdjacentFlipFanLayer_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    (containedAdjacentFlipFanIndices q u).biUnion
        (containedAdjacentFlipFanLayer q u) ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  cases i <;> exact blockedSignatureValueLayer_subset_subsetSumRange _ hxi

/-- Normalized second-moment packing of the contained flip fan. -/
theorem containedAdjacentFlipFan_normalized_packing
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hflipCard : (u.val.1 \ q.val.1).card = 1)
    (hsupport : reducedCollisionSupport u ⊆ reducedCollisionSupport q) :
    2 * (reducedCollisionSupportDepth u q + 1) *
        reducedCollisionWeight (m := m) u ≤
      (reducedCollisionSupportDepth u q + 2) *
        ((containedAdjacentFlipFanIndices q u).biUnion
          (containedAdjacentFlipFanLayer q u)).card := by
  classical
  let F := containedAdjacentFlipFanIndices q u
  let L := containedAdjacentFlipFanLayer q u
  have hF : F.Nonempty := ⟨none,
    none_mem_containedAdjacentFlipFanIndices q u⟩
  have hbound := two_mul_card_mul_weight_le_succ_mul_familyUnion_card
    F L (reducedCollisionWeight (m := m) u) hF
      (by simp [reducedCollisionWeight])
      (fun i hi ↦ card_containedAdjacentFlipFanLayer_eq_rootWeight
        hg q u i hi)
      (fun i hi j hj hij ↦
        two_mul_card_containedAdjacentFlipFanLayers_inter_le
          hg q u hflipCard i hi j hj hij)
  have hFcard : F.card = reducedCollisionSupportDepth u q + 1 := by
    rw [card_containedAdjacentFlipFanIndices q u hflipCard,
      card_externalSupport_eq_depth_of_support_subset q u hsupport]
  simpa [F, L, hFcard, Nat.add_assoc] using hbound

/-- In the genuine critical residual, contained adjacent nesting has strictly
increasing support in the fan orientation; equal support would close G1 by
common touch. -/
theorem genuineResidual_containedCrowdedAdjacent_supportCard_lt
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (F : Finset (ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))))
    (hcanonical : F ⊆ criticalCanonicalReducedCollisions g)
    {v u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hpair : (v, u) ∈
      reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F) :
    (reducedCollisionSupport u).card <
      (reducedCollisionSupport v).card := by
  classical
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let hh := half_add_half hN
  have hh0 : ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ≠ 0 :=
    half_ne_zero hN
      (mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd))
  have hp :=
    mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff.mp
      hpair
  have hadjPair :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
  have hnest :=
    mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
  have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hcanonical hnest.1
  have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hcanonical hnest.2.1
  have hsupport :=
    (containedAdjacentPositiveNesting_negative_sSubset
      hg hh hh0 v u hvcanonical hucanonical hnest.2.2 hadj.2 hp.2).1
  by_contra hnot
  have hcardEq : (reducedCollisionSupport u).card =
      (reducedCollisionSupport v).card := by
    have hle := Finset.card_le_card hsupport
    omega
  have hsupportEq : reducedCollisionSupport u =
      reducedCollisionSupport v :=
    Finset.eq_of_subset_of_card_le hsupport hcardEq.ge
  have htouch := commonTouched_of_equalSupport_adjacentPositiveNesting
    hg hh hh0
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
      v u hvcanonical hucanonical hnest.2.2 hadj.2 hsupportEq
  exact hres.2.1 (by simpa [CriticalCommonTouched] using htouch)

/-- Critical contained edges therefore have positive depth, a nonempty
external set, a full restored layer, and a nontrivial normalized flip fan. -/
theorem genuineResidual_containedCrowdedAdjacent_flipFan
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (F : Finset (ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))))
    (hcanonical : F ⊆ criticalCanonicalReducedCollisions g)
    {v u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hpair : (v, u) ∈
      reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F) :
    0 < reducedCollisionSupportDepth u v ∧
      (reducedCollisionExternalSupport u v).Nonempty ∧
      IsFullRestoredCollisionLayer u v ∧
      2 * (reducedCollisionSupportDepth u v + 1) *
          reducedCollisionWeight (m := n) u ≤
        (reducedCollisionSupportDepth u v + 2) *
          ((containedAdjacentFlipFanIndices v u).biUnion
            (containedAdjacentFlipFanLayer v u)).card ∧
      (containedAdjacentFlipFanIndices v u).biUnion
          (containedAdjacentFlipFanLayer v u) ⊆ subsetSumRange g := by
  classical
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let hh := half_add_half hN
  have hh0 : ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ≠ 0 :=
    half_ne_zero hN
      (mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd))
  have hp :=
    mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff.mp
      hpair
  have hadjPair :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
  have hnest :=
    mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
  have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hcanonical hnest.1
  have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hcanonical hnest.2.1
  have hsupport :=
    (containedAdjacentPositiveNesting_negative_sSubset
      hg hh hh0 v u hvcanonical hucanonical hnest.2.2 hadj.2 hp.2).1
  have hlt := genuineResidual_containedCrowdedAdjacent_supportCard_lt
    hqodd g hg r hres F hcanonical hpair
  have hdepth : 0 < reducedCollisionSupportDepth u v := by
    simp only [reducedCollisionSupportDepth]
    omega
  have hexternalCard := card_externalSupport_eq_depth_of_support_subset
    v u hsupport
  have hexternal : (reducedCollisionExternalSupport u v).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 v u hvcanonical hucanonical hnest.2.2 hadj.2
  exact ⟨hdepth, hexternal,
    isFullRestoredCollisionLayer_of_support_card_le hg u v hlt.le,
    containedAdjacentFlipFan_normalized_packing hg v u hflip.1 hsupport,
    biUnion_containedAdjacentFlipFanLayer_subset_subsetSumRange v u⟩

end MinModulus
