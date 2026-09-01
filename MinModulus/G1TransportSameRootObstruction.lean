import MinModulus.G1TransportLastWrite

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A transported target face is disjoint from the excluded source face of
the very edge that produced it: the target forces the whole root support,
while the source avoids the other root-negative coordinate. -/
theorem restorationFanTransportFace_disjoint_ownExcludedSource
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    Disjoint (restorationFanExcludedTransportSubsetSlice q j)
      (restorationFanForcedExcludedSubsetSlice r q j) := by
  classical
  have hsource :=
    restorationFanForcedExcludedSubsetSlice_eq_booleanConstraintFace
      r q hcard hdrop j k hAcard hB hjq hkq hAq
  have hkB : k ∈ r.val.2 := by rw [hB]; simp
  have hkRoot : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hkB
  have hkErase : k ∈ (reducedCollisionSupport r).erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hjk, hkRoot⟩
  rw [Finset.disjoint_left]
  intro S hTarget hSource
  have hRootUpper :=
    restorationFanExcludedTransportSubsetSlice_subset_rootUpper
      r q j k hAcard hB hkq hAq hTarget
  have hkS :=
    (mem_blockedSignatureUpperSubsetLayer_iff.mp hRootUpper) hkRoot
  rw [hsource] at hSource
  have hAvoid := (mem_booleanConstraintFace_iff.mp hSource).2
  exact Finset.disjoint_left.mp hAvoid hkS hkErase

/-- Under validity, own-edge source/target disjointness transfers to the
actual subset-sum value faces. -/
theorem restorationFanTransportValueFace_disjoint_ownExcludedSource
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    Disjoint (restorationFanExcludedTransportValueSlice q j)
      (restorationFanForcedExcludedValueSlice r q j) := by
  classical
  have hsubset := restorationFanTransportFace_disjoint_ownExcludedSource
    r q hcard hdrop j k hjk hAcard hB hjq hkq hAq
  rw [Finset.disjoint_left]
  intro x hxTarget hxSource
  rcases Finset.mem_image.mp hxTarget with ⟨S, hSTarget, hSx⟩
  rcases Finset.mem_image.mp hxSource with ⟨T, hTSource, hTx⟩
  have hST : S = T := ssum_injective g hg (hSx.trans hTx.symm)
  subst T
  exact Finset.disjoint_left.mp hsubset hSTarget hTSource

/-- The two excluded source faces attached to one live root. -/
noncomputable def pairedRestorationFanForcedExcludedSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    Finset (Finset (Fin m)) :=
  restorationFanForcedExcludedSubsetSlice r v j ∪
    restorationFanForcedExcludedSubsetSlice r u k

/-- Value image of the two excluded source faces attached to one live root. -/
noncomputable def pairedRestorationFanForcedExcludedValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  restorationFanForcedExcludedValueSlice r v j ∪
    restorationFanForcedExcludedValueSlice r u k

omit [DecidableEq G] in
/-- Neither selected same-root edge can continue into either selected source:
the whole paired transported target union is disjoint from the paired source
union. -/
theorem pairedRestorationFanTransport_disjoint_sameRootSources
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2)
    (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    Disjoint (pairedRestorationFanExcludedTransportSubsetUnion v u j k)
      (pairedRestorationFanForcedExcludedSubsetUnion r v u j k) := by
  classical
  have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
  rw [pairedRestorationFanExcludedTransportSubsetUnion,
    pairedRestorationFanForcedExcludedSubsetUnion,
    Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  exact ⟨
    ⟨restorationFanTransportFace_disjoint_ownExcludedSource
        r v hcardv hdropv j k hjk hAcard hB hjv hkv hAv,
      restorationFanTransportFace_disjoint_oppositeExcludedSource
        r v u hcardu hdropu j k hjk hAcard hB hku hkv hju hAv hAu⟩,
    ⟨restorationFanTransportFace_disjoint_oppositeExcludedSource
        r u v hcardv hdropv k j (Ne.symm hjk) hAcard hBswap
          hjv hju hkv hAu hAv,
      restorationFanTransportFace_disjoint_ownExcludedSource
        r u hcardu hdropu k j (Ne.symm hjk) hAcard hBswap
          hku hju hAu⟩⟩

/-- The same no-continuation theorem at the value level. -/
theorem pairedRestorationFanTransportValue_disjoint_sameRootSources
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2)
    (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    Disjoint (pairedRestorationFanExcludedTransportValueUnion v u j k)
      (pairedRestorationFanForcedExcludedValueUnion r v u j k) := by
  classical
  have hsubset := pairedRestorationFanTransport_disjoint_sameRootSources
    r v u hcardv hcardu hdropv hdropu j k hjk hAcard hB
      hjv hku hkv hju hAv hAu
  rw [pairedRestorationFanExcludedTransportValueUnion,
    pairedRestorationFanForcedExcludedValueUnion,
    restorationFanExcludedTransportValueSlice,
    restorationFanExcludedTransportValueSlice,
    restorationFanForcedExcludedValueSlice,
    restorationFanForcedExcludedValueSlice,
    ← Finset.image_union, ← Finset.image_union,
    Finset.disjoint_image (ssum_injective g hg)]
  exact hsubset

end MinModulus
