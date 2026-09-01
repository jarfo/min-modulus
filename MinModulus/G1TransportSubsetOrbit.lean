import MinModulus.G1TransportPiecewisePermutation

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A rigid, nonempty family of live restoration edges after the no-escape
branch has supplied the two source/target partitions. -/
structure LiveRestorationPermutationSystem
    {ι : Type*} [DecidableEq ι]
    (g : Fin (m + 1) → G) (h : G)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h) : Prop where
  valid : ValidTuple g
  half_add_half : h + h = 0
  half_ne_zero : h ≠ 0
  index_nonempty : I.Nonempty
  target_canonical : ∀ i ∈ I,
    IsCanonicalReducedCollision half_add_half (e i).target
  target_injective : Set.InjOn (fun i ↦ (e i).target) I
  source_pairwise : (I : Set ι).PairwiseDisjoint
    (fun i ↦ (e i).sourceValueFace)
  target_union_eq_source_union :
    I.biUnion (fun i ↦ (e i).targetValueFace) =
      I.biUnion (fun i ↦ (e i).sourceValueFace)

namespace LiveRestorationPermutationSystem

variable {ι : Type*} [DecidableEq ι]
variable {g : Fin (m + 1) → G} {h : G}
variable {I : Finset ι} {e : ι → LiveRestorationEdgeDatum g h}

/-- The piecewise affine permutation underlying a rigid restoration system. -/
theorem partitionedTransport
    (S : LiveRestorationPermutationSystem g h I e) :
    PartitionedAffineTransport I (fun i ↦ (e i).affineTransport) :=
  liveRestorationEdgeDatumPartitionedTransport
    S.valid S.half_add_half S.half_ne_zero I e
      S.target_canonical S.target_injective S.source_pairwise
        S.target_union_eq_source_union

/-- The unique ordinary source subset representing an orbit value. -/
noncomputable def sourceSubsetAt
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) : Finset (Fin m) := by
  let P := S.partitionedTransport
  let i := P.sourceIndex x
  have hxSource : x.val ∈ (e i).sourceValueFace := by
    exact P.mem_source_sourceIndex x
  exact Classical.choose (Finset.mem_image.mp hxSource)

theorem sourceSubsetAt_mem
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) :
    S.sourceSubsetAt x ∈ restorationFanForcedExcludedSubsetSlice
      (e (S.partitionedTransport.sourceIndex x)).root
      (e (S.partitionedTransport.sourceIndex x)).target
      (e (S.partitionedTransport.sourceIndex x)).drop := by
  exact (Classical.choose_spec (Finset.mem_image.mp
    (S.partitionedTransport.mem_source_sourceIndex x))).1

theorem ssum_sourceSubsetAt
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) :
    ssum g (S.sourceSubsetAt x) = x.val := by
  exact (Classical.choose_spec (Finset.mem_image.mp
    (S.partitionedTransport.mem_source_sourceIndex x))).2

/-- The explicit subset restoration of the current unique source subset has
subset sum equal to the next piecewise-permutation value. -/
theorem ssum_transport_sourceSubsetAt_eq_map
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) :
    let P := S.partitionedTransport
    let i := P.sourceIndex x
    ssum g (restorationFanExcludedTransport
      (e i).target (S.sourceSubsetAt x)) = (P.map x).val := by
  let P := S.partitionedTransport
  let i := P.sourceIndex x
  have hformula :=
    ssum_restorationFanExcludedTransport_of_singletonPositive
      (e i).root (e i).target
      (e i).root_support_le_target (e i).dropped_nonempty
      (e i).drop (e i).other (e i).root_positive_card
      (e i).root_negative_pair (e i).drop_avoids_target
      (e i).other_mem_target_negative
      (e i).rootPositive_inter_targetNegative
      (S.sourceSubsetAt_mem x)
  have hsourceSum := S.ssum_sourceSubsetAt x
  change ssum g (restorationFanExcludedTransport
      (e i).target (S.sourceSubsetAt x)) =
    P.shiftAt x + x.val
  change ssum g (restorationFanExcludedTransport
      (e i).target (S.sourceSubsetAt x)) =
    (e i).affineTransport.shift + x.val
  rw [LiveRestorationEdgeDatum.affineTransport_shift, ← hsourceSum]
  rw [hformula]
  simp only [restorationFanCollisionShift]
  abel

/-- Subset-sum injectivity lifts one value-orbit step to the exact coordinate
transport: the next unique source subset is obtained by replacing the current
target-positive support with its target-negative support. -/
theorem sourceSubsetAt_toPerm
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) :
    let P := S.partitionedTransport
    S.sourceSubsetAt (P.toPerm x) =
      restorationFanExcludedTransport
        (e (P.sourceIndex x)).target (S.sourceSubsetAt x) := by
  let P := S.partitionedTransport
  apply ssum_injective g S.valid
  rw [S.ssum_sourceSubsetAt]
  change (P.toPerm x).val = _
  rw [P.toPerm_apply]
  exact (S.ssum_transport_sourceSubsetAt_eq_map x).symm

/-- Source subset seen at the `n`th point of the orbit. -/
noncomputable def orbitSourceSubset
    (S : LiveRestorationPermutationSystem g h I e)
    (n : ℕ) (x : S.partitionedTransport.carrier) : Finset (Fin m) :=
  S.sourceSubsetAt
    (((S.partitionedTransport.toPerm :
      S.partitionedTransport.carrier →
        S.partitionedTransport.carrier)^[n]) x)

/-- Edge index selected at the `n`th point of the orbit. -/
noncomputable def orbitSourceIndex
    (S : LiveRestorationPermutationSystem g h I e)
    (n : ℕ) (x : S.partitionedTransport.carrier) : ι :=
  S.partitionedTransport.sourceIndex
    (((S.partitionedTransport.toPerm :
      S.partitionedTransport.carrier →
        S.partitionedTransport.carrier)^[n]) x)

/-- Exact subset recurrence along the compatible orbit. -/
theorem orbitSourceSubset_succ
    (S : LiveRestorationPermutationSystem g h I e)
    (n : ℕ) (x : S.partitionedTransport.carrier) :
    S.orbitSourceSubset (n + 1) x =
      restorationFanExcludedTransport
        (e (S.orbitSourceIndex n x)).target
        (S.orbitSourceSubset n x) := by
  rw [orbitSourceSubset, orbitSourceSubset, orbitSourceIndex]
  rw [Function.iterate_succ_apply']
  exact S.sourceSubsetAt_toPerm _

/-- Coordinate-level form of the orbit flow: at each step the selected
target's negative tail is inserted, its entire support is cleared from the
old subset, and all outside padding is retained. -/
theorem mem_orbitSourceSubset_succ_iff
    (S : LiveRestorationPermutationSystem g h I e)
    (n : ℕ) (x : S.partitionedTransport.carrier) (a : Fin m) :
    a ∈ S.orbitSourceSubset (n + 1) x ↔
      a ∈ (e (S.orbitSourceIndex n x)).target.val.2 ∨
        (a ∈ S.orbitSourceSubset n x ∧
          a ∉ reducedCollisionSupport
            (e (S.orbitSourceIndex n x)).target) := by
  rw [S.orbitSourceSubset_succ]
  simp [restorationFanExcludedTransport]

/-- At the positive global permutation order, the lifted ordinary subset
orbit also closes exactly. -/
theorem orbitSourceSubset_orderOf_eq
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier) :
    S.orbitSourceSubset (orderOf S.partitionedTransport.toPerm) x =
      S.orbitSourceSubset 0 x := by
  have hpow : S.partitionedTransport.toPerm ^
      orderOf S.partitionedTransport.toPerm = 1 :=
    pow_orderOf_eq_one S.partitionedTransport.toPerm
  simp only [orbitSourceSubset]
  rw [Equiv.Perm.iterate_eq_pow, hpow]
  rfl

end LiveRestorationPermutationSystem

end MinModulus
