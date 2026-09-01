import MinModulus.G1TransportBalancedCover

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finite family of affine translations whose source pieces and target
pieces are two partitions of the same value set. -/
structure PartitionedAffineTransport
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (edge : ι → FinsetAffineTransport G) where
  source_pairwise : (I : Set ι).PairwiseDisjoint (fun i ↦ (edge i).source)
  target_pairwise : (I : Set ι).PairwiseDisjoint (fun i ↦ (edge i).target)
  source_union_eq_target_union :
    I.biUnion (fun i ↦ (edge i).source) =
      I.biUnion (fun i ↦ (edge i).target)

namespace PartitionedAffineTransport

variable {ι : Type*} [DecidableEq ι]
variable {I : Finset ι} {edge : ι → FinsetAffineTransport G}

/-- The common finite value set on which the piecewise transport acts. -/
def carrier (_P : PartitionedAffineTransport I edge) : Finset G :=
  I.biUnion (fun i ↦ (edge i).source)

/-- Unique source-piece index containing a value of the common carrier. -/
noncomputable def sourceIndex
    (P : PartitionedAffineTransport I edge) (x : P.carrier) : ι :=
  Classical.choose (Finset.mem_biUnion.mp x.property)

theorem sourceIndex_mem
    (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    P.sourceIndex x ∈ I :=
  (Classical.choose_spec (Finset.mem_biUnion.mp x.property)).1

theorem mem_source_sourceIndex
    (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    x.val ∈ (edge (P.sourceIndex x)).source :=
  (Classical.choose_spec (Finset.mem_biUnion.mp x.property)).2

/-- Edge shift selected at a point of the source partition. -/
noncomputable def shiftAt
    (P : PartitionedAffineTransport I edge) (x : P.carrier) : G :=
  (edge (P.sourceIndex x)).shift

/-- Apply the uniquely selected affine edge to one carrier value. -/
noncomputable def map
    (P : PartitionedAffineTransport I edge) (x : P.carrier) : P.carrier := by
  let i := P.sourceIndex x
  refine ⟨(edge i).shift + x.val, ?_⟩
  have htarget : (edge i).shift + x.val ∈ (edge i).target := by
    rw [← (edge i).transport_eq]
    exact Finset.mem_image.mpr
      ⟨x.val, P.mem_source_sourceIndex x, rfl⟩
  change (edge i).shift + x.val ∈
    I.biUnion (fun i ↦ (edge i).source)
  rw [P.source_union_eq_target_union]
  exact Finset.mem_biUnion.mpr ⟨i, P.sourceIndex_mem x, htarget⟩

@[simp]
theorem map_val (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    (P.map x).val = P.shiftAt x + x.val := by
  simp [map, shiftAt]

theorem map_mem_target
    (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    (P.map x).val ∈ (edge (P.sourceIndex x)).target := by
  rw [map_val, shiftAt, ← (edge (P.sourceIndex x)).transport_eq]
  exact Finset.mem_image.mpr
    ⟨x.val, P.mem_source_sourceIndex x, rfl⟩

/-- Pairwise-disjoint target pieces make the piecewise translation
injective. -/
theorem map_injective (P : PartitionedAffineTransport I edge) :
    Function.Injective P.map := by
  intro x y hxy
  have hindex : P.sourceIndex x = P.sourceIndex y := by
    by_contra hne
    have hdisj := P.target_pairwise
      (P.sourceIndex_mem x) (P.sourceIndex_mem y) hne
    have hmemx := P.map_mem_target x
    have hmemy := P.map_mem_target y
    rw [hxy] at hmemx
    exact Finset.disjoint_left.mp hdisj hmemx hmemy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  rw [P.map_val, P.map_val, shiftAt, shiftAt, hindex] at hval
  exact add_left_cancel hval

/-- The piecewise translation is a permutation of the common finite
carrier. -/
noncomputable def toPerm
    (P : PartitionedAffineTransport I edge) : Equiv.Perm P.carrier :=
  Equiv.ofBijective P.map
    ((Fintype.bijective_iff_injective_and_card P.map).mpr
      ⟨P.map_injective, rfl⟩)

@[simp]
theorem toPerm_apply
    (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    P.toPerm x = P.map x := rfl

/-- Accumulated pointwise edge shift along `n` iterations. -/
noncomputable def orbitShiftSum
    (P : PartitionedAffineTransport I edge) : ℕ → P.carrier → G
  | 0, _ => 0
  | n + 1, x => P.shiftAt x + P.orbitShiftSum n (P.toPerm x)

/-- Iteration of the piecewise permutation is translation by the accumulated
selected edge shifts. -/
theorem iterate_val_eq_orbitShiftSum_add
    (P : PartitionedAffineTransport I edge)
    (n : ℕ) (x : P.carrier) :
    (((P.toPerm : P.carrier → P.carrier)^[n]) x).val =
      P.orbitShiftSum n x + x.val := by
  induction n generalizing x with
  | zero => simp [orbitShiftSum]
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [orbitShiftSum, P.toPerm_apply, P.map_val]
      abel

/-- The global permutation order gives a genuine compatible point-cycle;
its literal sum of selected edge shifts is zero. -/
theorem orbitShiftSum_orderOf_toPerm_eq_zero
    (P : PartitionedAffineTransport I edge) (x : P.carrier) :
    P.orbitShiftSum (orderOf P.toPerm) x = 0 := by
  have hpow : P.toPerm ^ orderOf P.toPerm = 1 :=
    pow_orderOf_eq_one P.toPerm
  have hiterate :
      (((P.toPerm : P.carrier → P.carrier)^[orderOf P.toPerm]) x) = x := by
    rw [Equiv.Perm.iterate_eq_pow, hpow]
    rfl
  have hvalue := P.iterate_val_eq_orbitShiftSum_add
    (orderOf P.toPerm) x
  rw [hiterate] at hvalue
  have hcancel : P.orbitShiftSum (orderOf P.toPerm) x + x.val =
      0 + x.val := by simpa using hvalue.symm
  exact add_right_cancel hcancel

theorem orderOf_toPerm_pos (P : PartitionedAffineTransport I edge) :
    0 < orderOf P.toPerm := orderOf_pos P.toPerm

end PartitionedAffineTransport

section RestorationPiecewise

variable {m : ℕ}

/-- The affine transport carried by a packaged live restoration edge. -/
noncomputable def LiveRestorationEdgeDatum.affineTransport
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) : FinsetAffineTransport G :=
  restorationFanAffineTransport e.root e.target
    e.root_support_le_target e.dropped_nonempty e.drop e.other
      e.root_positive_card e.root_negative_pair e.drop_avoids_target
        e.other_mem_target_negative e.rootPositive_inter_targetNegative

@[simp]
theorem LiveRestorationEdgeDatum.affineTransport_source
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) :
    e.affineTransport.source = e.sourceValueFace := rfl

@[simp]
theorem LiveRestorationEdgeDatum.affineTransport_target
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) :
    e.affineTransport.target = e.targetValueFace := rfl

@[simp]
theorem LiveRestorationEdgeDatum.affineTransport_shift
    {g : Fin (m + 1) → G} {h : G}
    (e : LiveRestorationEdgeDatum g h) :
    e.affineTransport.shift =
      -restorationFanCollisionShift e.root e.target := rfl

/-- In the rigid no-escape branch, live restoration edges assemble into a
piecewise affine permutation of their common source/target union. -/
theorem liveRestorationEdgeDatumPartitionedTransport
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I)
    (hsource : (I : Set ι).PairwiseDisjoint
      (fun i ↦ (e i).sourceValueFace))
    (hunion : I.biUnion (fun i ↦ (e i).targetValueFace) =
      I.biUnion (fun i ↦ (e i).sourceValueFace)) :
    PartitionedAffineTransport I (fun i ↦ (e i).affineTransport) where
  source_pairwise := by simpa using hsource
  target_pairwise := by
    simpa using liveRestorationEdgeDatum_targetValueFaces_pairwiseDisjoint
      hg hh hh0 I e hcanonical hinjective
  source_union_eq_target_union := by simpa using hunion.symm

/-- Every edge datum has a nonempty source face. -/
theorem LiveRestorationEdgeDatum.sourceValueFace_nonempty
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (e : LiveRestorationEdgeDatum g h) : e.sourceValueFace.Nonempty := by
  have hcard := e.two_mul_card_sourceValueFace hg
  have hweight : 0 < e.weight := by
    simp [LiveRestorationEdgeDatum.weight, reducedCollisionWeight]
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty] at hcard
  simp at hcard
  omega

/-- A nonempty rigid restoration family has a positive-length compatible
point-orbit whose accumulated genuine restoration-edge shift is literally
zero. -/
theorem liveRestorationEdgeDatum_exists_positiveOrbit_zero_shift
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hI : I.Nonempty)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I)
    (hsource : (I : Set ι).PairwiseDisjoint
      (fun i ↦ (e i).sourceValueFace))
    (hunion : I.biUnion (fun i ↦ (e i).targetValueFace) =
      I.biUnion (fun i ↦ (e i).sourceValueFace)) :
    let P := liveRestorationEdgeDatumPartitionedTransport
      hg hh hh0 I e hcanonical hinjective hsource hunion
    ∃ x : P.carrier,
      0 < orderOf P.toPerm ∧
        P.orbitShiftSum (orderOf P.toPerm) x = 0 := by
  let P := liveRestorationEdgeDatumPartitionedTransport
    hg hh hh0 I e hcanonical hinjective hsource hunion
  obtain ⟨i, hi⟩ := hI
  obtain ⟨x, hx⟩ := (e i).sourceValueFace_nonempty hg
  have hxCarrier : x ∈ P.carrier := by
    exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  let xP : P.carrier := ⟨x, hxCarrier⟩
  exact ⟨xP, P.orderOf_toPerm_pos,
    P.orbitShiftSum_orderOf_toPerm_eq_zero xP⟩

/-- In the restoration specialization, the pointwise shift selected by the
piecewise permutation is exactly the negative collision shift of its unique
source edge. -/
theorem liveRestorationEdgeDatumPartitionedTransport_shiftAt
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I)
    (hsource : (I : Set ι).PairwiseDisjoint
      (fun i ↦ (e i).sourceValueFace))
    (hunion : I.biUnion (fun i ↦ (e i).targetValueFace) =
      I.biUnion (fun i ↦ (e i).sourceValueFace))
    (x : (liveRestorationEdgeDatumPartitionedTransport
      hg hh hh0 I e hcanonical hinjective hsource hunion).carrier) :
    let P := liveRestorationEdgeDatumPartitionedTransport
      hg hh hh0 I e hcanonical hinjective hsource hunion
    P.shiftAt x = -restorationFanCollisionShift
      (e (P.sourceIndex x)).root (e (P.sourceIndex x)).target := by
  rfl

/-- Complete global dichotomy for a nonempty finite canonical restoration
family: either a transported value escapes all sources, or the balanced
piecewise permutation has a positive point-orbit with zero accumulated
genuine edge shift. -/
theorem liveRestorationEdgeDatum_exists_globalEscape_or_positiveOrbit_zero_shift
    {ι : Type*} [DecidableEq ι]
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (I : Finset ι) (e : ι → LiveRestorationEdgeDatum g h)
    (hI : I.Nonempty)
    (hcanonical : ∀ i ∈ I,
      IsCanonicalReducedCollision hh (e i).target)
    (hinjective : Set.InjOn (fun i ↦ (e i).target) I) :
    (∃ x ∈ I.biUnion (fun i ↦ (e i).targetValueFace),
        x ∉ I.biUnion (fun i ↦ (e i).sourceValueFace)) ∨
      ∃ (hsource : (I : Set ι).PairwiseDisjoint
          (fun i ↦ (e i).sourceValueFace))
        (hunion : I.biUnion (fun i ↦ (e i).targetValueFace) =
          I.biUnion (fun i ↦ (e i).sourceValueFace)),
        let P := liveRestorationEdgeDatumPartitionedTransport
          hg hh hh0 I e hcanonical hinjective hsource hunion
        ∃ x : P.carrier,
          0 < orderOf P.toPerm ∧
            P.orbitShiftSum (orderOf P.toPerm) x = 0 := by
  rcases liveRestorationEdgeDatum_exists_globalEscape_or_balancedRigidity
      hg hh hh0 I e hcanonical hinjective with hescape | hrigid
  · exact Or.inl hescape
  · right
    obtain ⟨hunion, hsource, _hrows, _hcols⟩ := hrigid
    exact ⟨hsource, hunion,
      liveRestorationEdgeDatum_exists_positiveOrbit_zero_shift
        hg hh hh0 I e hI hcanonical hinjective hsource hunion⟩

end RestorationPiecewise

end MinModulus
