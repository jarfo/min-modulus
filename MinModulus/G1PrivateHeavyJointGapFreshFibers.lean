/-
# Fresh gap fibers inside a repeated normalized heavy level

An abstract fresh-gap counter separates target-owner labels from labels
external to the deletion set.  If every selected gap also avoids two fixed
external coordinates, then the external image arm pays two extra units of
ambient capacity.  The target-owner arm is absorbed by the existing global
self-heavy normalization.

We instantiate this counter on the owner projection of one repeated joint
heavy-target coefficient level.  The level collision theorem supplies a gap
away from both the common heavy coordinate and the common omission.
-/
import MinModulus.G1PrivateHeavyJointGapLevels

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Pairs whose chosen fresh gap is their target owner. -/
noncomputable def minimalSupportSelectedPrivateFreshTargetGapPairs
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun p ↦ gap p = p.val.2.val)

/-- Pairs whose chosen fresh gap is external to the deletion set. -/
noncomputable def minimalSupportSelectedPrivateFreshExternalGapPairs
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun p ↦ gap p ∉ B)

/-- A target-owner/external selector partitions all ordered distinct pairs. -/
theorem card_minimalSupportSelectedPrivateFreshTarget_add_external
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (hlocation : ∀ p, gap p = p.val.2.val ∨ gap p ∉ B) :
    (minimalSupportSelectedPrivateFreshTargetGapPairs S gap).card +
      (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).card =
        S.card * (S.card - 1) := by
  classical
  let T := minimalSupportSelectedPrivateFreshTargetGapPairs S gap
  let E := minimalSupportSelectedPrivateFreshExternalGapPairs S gap
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro p hpT hpE
    have hpT' := Finset.mem_filter.mp hpT
    have hpE' := Finset.mem_filter.mp hpE
    apply hpE'.2
    rw [hpT'.2]
    exact p.val.2.val.property
  have hunion : T ∪ E = Finset.univ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hlocation p with htarget | hexternal
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htarget⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexternal⟩)
  change T.card + E.card = S.card * (S.card - 1)
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp [card_minimalSupportSelectedDistinctOrderedPair]

/-- A target-owner fresh gap makes its target owner-heavy. -/
theorem minimalSupportSelectedPrivateFreshTarget_ownerHeavy
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p))
    {p : MinimalSupportSelectedDistinctOrderedPair S}
    (hp : p ∈ minimalSupportSelectedPrivateFreshTargetGapPairs S gap) :
    p.val.2 ∈ minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S := by
  classical
  have htarget := (Finset.mem_filter.mp hp).2
  have hpGap := hgap p
  rw [htarget] at hpGap
  have howners : (p.val.1.val : Fin (m + 1)) ≠
      (p.val.2.val : Fin (m + 1)) := by
    intro hval
    apply p.property
    apply Subtype.ext
    exact Subtype.ext hval
  have hsourceZero := minimalSupportPrivateWitness_eq_zero_of_ne
    g h hmin p.val.1.val p.val.2.val.property (Ne.symm howners)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

/-- Fresh target-owner pairs inject into owner-heavy targets times sources. -/
theorem card_minimalSupportSelectedPrivateFreshTargetGapPairs_le
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p)) :
    (minimalSupportSelectedPrivateFreshTargetGapPairs S gap).card ≤
      (minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S).card *
        S.card := by
  classical
  let T := minimalSupportSelectedPrivateFreshTargetGapPairs S gap
  let O := minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S
  let enc : ↥T → ↥O × ↥S := fun p ↦
    (⟨p.val.val.2,
      minimalSupportSelectedPrivateFreshTarget_ownerHeavy
        g h hmin S gap hgap p.property⟩, p.val.val.1)
  have henc : Function.Injective enc := by
    intro p u hpu
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Prod.snd hpu
    · exact congrArg Subtype.val (congrArg Prod.fst hpu)
  have hcard := Fintype.card_le_of_injective enc henc
  change T.card ≤ O.card * S.card
  calc
    T.card = Fintype.card ↥T := (Fintype.card_coe T).symm
    _ ≤ Fintype.card (↥O × ↥S) := hcard
    _ = O.card * S.card := by simp

/-- Fresh external labels used by a selected pair family. -/
noncomputable def minimalSupportSelectedPrivateFreshExternalGapLabels
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1)) := by
  classical
  exact (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).image gap

/-- External pairs with one fixed fresh gap label. -/
noncomputable def minimalSupportSelectedPrivateFreshExternalGapFiber
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (i : Fin (m + 1)) := by
  classical
  exact (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).filter
    (fun p ↦ gap p = i)

/-- Every realized external label is external and inherits freshness. -/
theorem minimalSupportSelectedPrivateFreshExternalGapLabels_spec
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (z w : Fin (m + 1))
    (hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w)
    {i : Fin (m + 1)}
    (hi : i ∈ minimalSupportSelectedPrivateFreshExternalGapLabels S gap) :
    i ∉ B ∧ i ≠ z ∧ i ≠ w := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨(Finset.mem_filter.mp hp).2, (hfresh p).1, (hfresh p).2⟩

/-- Exact image/fiber dichotomy for fresh external labels. -/
theorem minimalSupportSelectedPrivateFreshExternal_labelImage_or_largeFiber
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).card) :
    L ≤ (minimalSupportSelectedPrivateFreshExternalGapLabels S gap).card ∨
      ∃ i ∈ minimalSupportSelectedPrivateFreshExternalGapLabels S gap,
        r < (minimalSupportSelectedPrivateFreshExternalGapFiber S gap i).card := by
  classical
  let E := minimalSupportSelectedPrivateFreshExternalGapPairs S gap
  let labels := minimalSupportSelectedPrivateFreshExternalGapLabels S gap
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < E.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ p ∈ E, gap p ∈ labels := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨i, hi, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := gap) hmaps hmul
    refine ⟨i, hi, ?_⟩
    simpa [E, minimalSupportSelectedPrivateFreshExternalGapFiber] using hfiber

/-- Many fresh external pairs either consume `L` new coordinates in addition
to fixed external `z,w`, or share one fresh external gap. -/
theorem minimalSupportSelectedPrivateFreshExternal_capacity_or_largeFiber
    {B : Finset (Fin (m + 1))} (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (z w : Fin (m + 1))
    (hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w)
    (hzB : z ∉ B) (hwB : w ∉ B) (hzw : z ≠ w)
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).card) :
    B.card + 2 + L ≤ m + 1 ∨
      ∃ i : Fin (m + 1), i ∉ B ∧ i ≠ z ∧ i ≠ w ∧
        r < (minimalSupportSelectedPrivateFreshExternalGapFiber S gap i).card := by
  classical
  let labels := minimalSupportSelectedPrivateFreshExternalGapLabels S gap
  rcases minimalSupportSelectedPrivateFreshExternal_labelImage_or_largeFiber
      S gap L r hcount with hlabels | hfiber
  · left
    change L ≤ labels.card at hlabels
    have hlabelsB : Disjoint labels B := by
      rw [Finset.disjoint_left]
      intro i hi hiB
      exact (minimalSupportSelectedPrivateFreshExternalGapLabels_spec
        S gap z w hfresh hi).1 hiB
    have hwLabels : w ∉ labels := by
      intro hw
      exact (minimalSupportSelectedPrivateFreshExternalGapLabels_spec
        S gap z w hfresh hw).2.2 rfl
    have hzLabels : z ∉ labels := by
      intro hz
      exact (minimalSupportSelectedPrivateFreshExternalGapLabels_spec
        S gap z w hfresh hz).2.1 rfl
    have hzInsert : z ∉ insert w labels := by simp [hzw, hzLabels]
    have hdisj : Disjoint (insert z (insert w labels)) B := by
      rw [Finset.disjoint_left]
      intro i hi hiB
      simp only [Finset.mem_insert] at hi
      rcases hi with rfl | rfl | hi
      · exact hzB hiB
      · exact hwB hiB
      · exact Finset.disjoint_left.mp hlabelsB hi hiB
    have hcap : B.card + (insert z (insert w labels)).card ≤ m + 1 := by
      rw [← Finset.card_union_of_disjoint hdisj.symm]
      simpa using Finset.card_le_univ (B ∪ insert z (insert w labels))
    rw [Finset.card_insert_of_notMem hzInsert,
      Finset.card_insert_of_notMem hwLabels] at hcap
    omega
  · right
    obtain ⟨i, hiLabel, hiFiber⟩ := hfiber
    have hiSpec := minimalSupportSelectedPrivateFreshExternalGapLabels_spec
      S gap z w hfresh hiLabel
    exact ⟨i, hiSpec.1, hiSpec.2.1, hiSpec.2.2, hiFiber⟩

/-- Abstract fresh-gap restart with owner normalization. -/
theorem minimalSupportSelectedPrivateFresh_selfHeavy_or_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p))
    (hlocation : ∀ p, gap p = p.val.2.val ∨ gap p ∉ B)
    (z w : Fin (m + 1))
    (hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w)
    (hzB : z ∉ B) (hwB : w ∉ B) (hzw : z ≠ w)
    (K L r : ℕ)
    (hcount : K * S.card + L * r < S.card * (S.card - 1)) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + 2 + L ≤ m + 1 ∨
      ∃ i : Fin (m + 1), i ∉ B ∧ i ≠ z ∧ i ≠ w ∧
        r < (minimalSupportSelectedPrivateFreshExternalGapFiber S gap i).card := by
  have hpartition := card_minimalSupportSelectedPrivateFreshTarget_add_external
    S gap hlocation
  have htargetBound := card_minimalSupportSelectedPrivateFreshTargetGapPairs_le
    g h hmin S gap hgap
  by_cases htarget : K * S.card <
      (minimalSupportSelectedPrivateFreshTargetGapPairs S gap).card
  · left
    have hSpos : 0 < S.card := by
      have hTpos : 0 <
          (minimalSupportSelectedPrivateFreshTargetGapPairs S gap).card :=
        lt_of_le_of_lt (Nat.zero_le _) htarget
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hTpos
      exact Finset.card_pos.mpr ⟨p.val.1.val, p.val.1.property⟩
    have hmul : S.card * K < S.card *
        (minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S).card := by
      simpa [Nat.mul_comm] using htarget.trans_le htargetBound
    have howner : K <
        (minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S).card :=
      (Nat.mul_lt_mul_left hSpos).mp hmul
    have hnormalize :=
      card_minimalSupportSelectedPrivateOwnerHeavyVertices_le_selfHeavy_add_one
        g h hmin S
    omega
  · right
    have htargetLe :
        (minimalSupportSelectedPrivateFreshTargetGapPairs S gap).card ≤
          K * S.card := Nat.le_of_not_gt htarget
    have hExternalCount : L * r <
        (minimalSupportSelectedPrivateFreshExternalGapPairs S gap).card := by
      omega
    exact minimalSupportSelectedPrivateFreshExternal_capacity_or_largeFiber
      S gap z w hfresh hzB hwB hzw L r hExternalCount

/-- With two fixed external coordinates, the fresh external branch is itself
an immediate three-coordinate capacity certificate. -/
theorem minimalSupportSelectedPrivateFresh_selfHeavy_or_card_add_three_le
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (gap : MinimalSupportSelectedDistinctOrderedPair S → Fin (m + 1))
    (hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p))
    (hlocation : ∀ p, gap p = p.val.2.val ∨ gap p ∉ B)
    (z w : Fin (m + 1))
    (hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w)
    (hzB : z ∉ B) (hwB : w ∉ B) (hzw : z ≠ w)
    (K : ℕ) (hcount : K * S.card < S.card * (S.card - 1)) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + 3 ≤ m + 1 := by
  have hfront :=
    minimalSupportSelectedPrivateFresh_selfHeavy_or_capacity_or_largeFiber
      g h hmin S gap hgap hlocation z w hfresh hzB hwB hzw K 1 0 (by
        simpa using hcount)
  rcases hfront with hself | hcapacity | hfiber
  · exact Or.inl hself
  · exact Or.inr (by omega)
  · right
    obtain ⟨i, hiB, hiz, hiw, _⟩ := hfiber
    exact card_add_three_le_of_three_external
      hiB hzB hwB hiz hiw hzw

/-- Owners underlying one fixed heavy coefficient level. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetLevelOwners
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) : Finset ↥B := by
  classical
  exact (minimalSupportPrivateJointGapHeavyTargetLevelFiber
    g hg h t hh q ht hq hmin hqzero z e delta w a).image (fun b ↦ b.val)

theorem card_minimalSupportPrivateJointGapHeavyTargetLevelOwners
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) :
    (minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a).card =
    (minimalSupportPrivateJointGapHeavyTargetLevelFiber
      g hg h t hh q ht hq hmin hqzero z e delta w a).card := by
  classical
  unfold minimalSupportPrivateJointGapHeavyTargetLevelOwners
  apply Finset.card_image_of_injective
  intro b u hbu
  exact Subtype.ext hbu

/-- Canonically lift a projected owner back into its heavy-target level. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (b : ↥(minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e) := by
  classical
  exact Classical.choose (Finset.mem_image.mp b.property)

theorem minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift_mem
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (b : ↥(minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
        g hg h t hh q ht hq hmin hqzero z e delta w a b ∈
      minimalSupportPrivateJointGapHeavyTargetLevelFiber
        g hg h t hh q ht hq hmin hqzero z e delta w a := by
  exact (Classical.choose_spec (Finset.mem_image.mp b.property)).1

@[simp] theorem minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift_val
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (b : ↥(minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    (minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
      g hg h t hh q ht hq hmin hqzero z e delta w a b).val = b.val := by
  exact (Classical.choose_spec (Finset.mem_image.mp b.property)).2

set_option maxHeartbeats 1000000 in
/-- Every ordered pair in the projected repeated level has a fresh gap. -/
theorem exists_fresh_gap_of_jointHeavyTargetLevelOwnerPair
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (p : MinimalSupportSelectedDistinctOrderedPair
      (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    ∃ i : Fin (m + 1),
      minimalSupportPrivateWitness g h hmin p.val.1.val i + 2 ≤
        minimalSupportPrivateWitness g h hmin p.val.2.val i ∧
      (i = p.val.2.val ∨ i ∉ B) ∧ i ≠ z ∧ i ≠ w := by
  let b := minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
    g hg h t hh q ht hq hmin hqzero z e delta w a p.val.1
  let u := minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
    g hg h t hh q ht hq hmin hqzero z e delta w a p.val.2
  have hbu : b ≠ u := by
    intro hsame
    apply p.property
    apply Subtype.ext
    have hvals := congrArg Subtype.val hsame
    simpa [b, u] using hvals
  have hfresh := exists_fresh_gap_of_distinct_jointHeavyTarget_sameLevel
    g hg h t hh q ht hq hmin hqzero z e delta w a b u
      (minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift_mem
        g hg h t hh q ht hq hmin hqzero z e delta w a p.val.1)
      (minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift_mem
        g hg h t hh q ht hq hmin hqzero z e delta w a p.val.2) hbu
  simpa [b, u] using hfresh

/-- Select the fresh gap of a projected repeated-level pair. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (p : MinimalSupportSelectedDistinctOrderedPair
      (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a)) : Fin (m + 1) :=
  Classical.choose (exists_fresh_gap_of_jointHeavyTargetLevelOwnerPair
    g hg h t hh q ht hq hmin hqzero z e delta w a p)

theorem minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (p : MinimalSupportSelectedDistinctOrderedPair
      (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    minimalSupportPrivateWitness g h hmin p.val.1.val
          (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
            g hg h t hh q ht hq hmin hqzero z e delta w a p) + 2 ≤
        minimalSupportPrivateWitness g h hmin p.val.2.val
          (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
            g hg h t hh q ht hq hmin hqzero z e delta w a p) ∧
      (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
          g hg h t hh q ht hq hmin hqzero z e delta w a p = p.val.2.val ∨
        minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
          g hg h t hh q ht hq hmin hqzero z e delta w a p ∉ B) ∧
      minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
          g hg h t hh q ht hq hmin hqzero z e delta w a p ≠ z ∧
      minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
          g hg h t hh q ht hq hmin hqzero z e delta w a p ≠ w :=
  Classical.choose_spec (exists_fresh_gap_of_jointHeavyTargetLevelOwnerPair
    g hg h t hh q ht hq hmin hqzero z e delta w a p)

/-- One projected level owner certifies that `z,w` are distinct and external. -/
theorem minimalSupportPrivateJointGapHeavyTargetLevel_fixed_external
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (b : ↥(minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a)) :
    z ∉ B ∧ w ∉ B ∧ z ≠ w := by
  let b' := minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift
    g hg h t hh q ht hq hmin hqzero z e delta w a b
  have hbLevel := minimalSupportPrivateJointGapHeavyTargetLevelOwnerLift_mem
    g hg h t hh q ht hq hmin hqzero z e delta w a b
  have hbData := Finset.mem_filter.mp hbLevel
  have hbTarget := minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
    g hg hh hmin
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e) delta w hbData.1
  have hbFixed := minimalSupportPrivateJointOwnerLift_heavy_at_fixed
    g hg h t q ht hq hmin hqzero z e b'
  have hzw : z ≠ w := by
    intro hzw
    have hwHeavy : 2 ≤ minimalSupportPrivateWitness g h hmin b'.val w := by
      rw [← hzw]
      exact hbFixed.2
    rw [hbTarget.2.2.2.2] at hwHeavy
    omega
  exact ⟨hbFixed.1, hbTarget.2.1, hzw⟩

/-- Instantiation of the abstract fresh-gap restart on a repeated joint-heavy
coefficient level. -/
theorem minimalSupportPrivateJointGapHeavyTargetLevel_selfHeavy_or_capacity_or_largeFreshFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) (K L r : ℕ)
    (hcount : let S := (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a)
      K * S.card + L * r < S.card * (S.card - 1)) :
    let S := minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a
    let gap := minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
      g hg h t hh q ht hq hmin hqzero z e delta w a
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + 2 + L ≤ m + 1 ∨
      ∃ i : Fin (m + 1), i ∉ B ∧ i ≠ z ∧ i ≠ w ∧
        r < (minimalSupportSelectedPrivateFreshExternalGapFiber S gap i).card := by
  let S := minimalSupportPrivateJointGapHeavyTargetLevelOwners
    g hg h t hh q ht hq hmin hqzero z e delta w a
  let gap := minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
    g hg h t hh q ht hq hmin hqzero z e delta w a
  have hSpos : 0 < S.card := by
    by_contra hzero
    have hScard : S.card = 0 := Nat.eq_zero_of_not_pos hzero
    change K * S.card + L * r < S.card * (S.card - 1) at hcount
    rw [hScard] at hcount
    simp at hcount
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hSpos
  have hfixed := minimalSupportPrivateJointGapHeavyTargetLevel_fixed_external
    g hg h t hh q ht hq hmin hqzero z e delta w a ⟨b, hb⟩
  have hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p) := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).1
  have hlocation : ∀ p, gap p = p.val.2.val ∨ gap p ∉ B := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).2.1
  have hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).2.2
  change K * S.card + L * r < S.card * (S.card - 1) at hcount
  exact minimalSupportSelectedPrivateFresh_selfHeavy_or_capacity_or_largeFiber
    g h hmin S gap hgap hlocation z w hfresh
      hfixed.1 hfixed.2.1 hfixed.2.2 K L r hcount

/-- In a repeated joint-heavy level, enough ordered-pair mass is completely
absorbed by global self-heavy mass or three-coordinate ambient capacity. -/
theorem minimalSupportPrivateJointGapHeavyTargetLevel_selfHeavy_or_card_add_three_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) (K : ℕ)
    (hcount : let S := (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a)
      K * S.card < S.card * (S.card - 1)) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + 3 ≤ m + 1 := by
  let S := minimalSupportPrivateJointGapHeavyTargetLevelOwners
    g hg h t hh q ht hq hmin hqzero z e delta w a
  let gap := minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate
    g hg h t hh q ht hq hmin hqzero z e delta w a
  have hSpos : 0 < S.card := by
    by_contra hzero
    have hScard : S.card = 0 := Nat.eq_zero_of_not_pos hzero
    change K * S.card < S.card * (S.card - 1) at hcount
    rw [hScard] at hcount
    simp at hcount
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hSpos
  have hfixed := minimalSupportPrivateJointGapHeavyTargetLevel_fixed_external
    g hg h t hh q ht hq hmin hqzero z e delta w a ⟨b, hb⟩
  have hgap : ∀ p, minimalSupportPrivateWitness g h hmin p.val.1.val (gap p) + 2 ≤
      minimalSupportPrivateWitness g h hmin p.val.2.val (gap p) := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).1
  have hlocation : ∀ p, gap p = p.val.2.val ∨ gap p ∉ B := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).2.1
  have hfresh : ∀ p, gap p ≠ z ∧ gap p ≠ w := by
    intro p
    exact (minimalSupportPrivateJointGapHeavyTargetLevelFreshCoordinate_spec
      g hg h t hh q ht hq hmin hqzero z e delta w a p).2.2
  change K * S.card < S.card * (S.card - 1) at hcount
  exact minimalSupportSelectedPrivateFresh_selfHeavy_or_card_add_three_le
    g h hmin S gap hgap hlocation z w hfresh
      hfixed.1 hfixed.2.1 hfixed.2.2 K hcount

/-- Outside three-coordinate capacity, one repeated coefficient level has at
most two more owners than the global self-heavy family. -/
theorem card_minimalSupportPrivateJointGapHeavyTargetLevelOwners_le_selfHeavy_add_two_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) :
    let S := minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a
    S.card ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2 ∨
      B.card + 3 ≤ m + 1 := by
  let S := minimalSupportPrivateJointGapHeavyTargetLevelOwners
    g hg h t hh q ht hq hmin hqzero z e delta w a
  change S.card ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2 ∨
    B.card + 3 ≤ m + 1
  by_cases hsmall : S.card ≤ 2
  · exact Or.inl (by omega)
  · have hSpos : 0 < S.card := by omega
    have hsubone : S.card - 1 = (S.card - 2) + 1 := by omega
    have hcount : (S.card - 2) * S.card < S.card * (S.card - 1) := by
      rw [hsubone]
      nlinarith
    rcases
        minimalSupportPrivateJointGapHeavyTargetLevel_selfHeavy_or_card_add_three_le
          g hg h t hh q ht hq hmin hqzero z e delta w a
            (S.card - 2) hcount with hself | hcapacity
    · change S.card - 2 ≤
        (minimalSupportPrivateSelfHeavyVertices g h hmin).card at hself
      exact Or.inl (by omega)
    · exact Or.inr hcapacity

/-- The complete normalized heavy-target family is bounded by the number of
coefficient levels times the global self-heavy bound, unless three external
coordinates already fit beside `B`. -/
theorem card_minimalSupportPrivateJointGapHeavyTargetVertices_le_levels_mul_selfHeavy_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (hfixed : delta = z) :
    (minimalSupportPrivateJointGapHeavyTargetVertices
      g hg h t hh q ht hq hmin hqzero z e delta w).card ≤
        m * ((minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2) ∨
      B.card + 3 ≤ m + 1 := by
  let H := minimalSupportPrivateJointGapHeavyTargetVertices
    g hg h t hh q ht hq hmin hqzero z e delta w
  let R := (minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2
  by_cases hbound : H.card ≤ m * R
  · exact Or.inl hbound
  · right
    have hcount : m * R < H.card := Nat.lt_of_not_ge hbound
    obtain ⟨a, _, hfiber⟩ :=
      exists_large_minimalSupportPrivateJointGapHeavyTargetLevelFiber
        g hg h t hh q ht hq hmin hqzero z e delta w hfixed R hcount
    have hprojection := card_minimalSupportPrivateJointGapHeavyTargetLevelOwners
      g hg h t hh q ht hq hmin hqzero z e delta w a
    rcases
        card_minimalSupportPrivateJointGapHeavyTargetLevelOwners_le_selfHeavy_add_two_or_capacity
          g hg h t hh q ht hq hmin hqzero z e delta w a with
      hlevel | hcapacity
    · change R <
        (minimalSupportPrivateJointGapHeavyTargetLevelFiber
          g hg h t hh q ht hq hmin hqzero z e delta w a).card at hfiber
      change (minimalSupportPrivateJointGapHeavyTargetLevelOwners
        g hg h t hh q ht hq hmin hqzero z e delta w a).card ≤ R at hlevel
      omega
    · exact hcapacity

end MinModulus
