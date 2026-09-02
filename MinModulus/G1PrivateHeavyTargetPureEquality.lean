/-
# Normalizing the equal-witness pure-target arm

When the protected private-heavy witness is literally the retained pure
target, the payload's distinguished coordinates become rigid.  The heavy
coordinate is the unique coefficient-`2` center.  If that center is the
private owner, the owner-coincidence law pins the escape to the same center.
Otherwise the owner is the other pure endpoint and both the center and escape
are external to the transversal.  An escape away from the center is outside
the pure support and is necessarily an omission of the protected quarter
witness.
-/
import MinModulus.G1PrivateHeavyTargetPureComparison

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A coefficient at least two in a nondegenerate pure edge occurs at its
displayed center. -/
theorem pureEdgeCoeffs_ge_two_eq_center
    (e z x i : Fin (m + 1))
    (hez : e ≠ z) (hex : e ≠ x) (hxz : x ≠ z)
    (hi : 2 ≤ pureEdgeCoeffs e z x i) :
    i = e := by
  by_cases hie : i = e
  · exact hie
  by_cases hiz : i = z
  · subst i
    simp [pureEdgeCoeffs, Ne.symm hez, Ne.symm hxz] at hi
  by_cases hix : i = x
  · subst i
    simp [pureEdgeCoeffs, Ne.symm hex, hxz] at hi
  simp [pureEdgeCoeffs, hie, hiz, hix] at hi

/-- A protected coefficient-floor escape against a pure edge is either its
center or an outside-support omission of the quarter witness. -/
theorem quarterEscape_pureEdge_center_or_externalOmission
    (q c : Fin (m + 1) → ℤ)
    (e z x i : Fin (m + 1))
    (hez : e ≠ z) (hex : e ≠ x) (hxz : x ≠ z)
    (hqFloor : ∀ a, -1 ≤ q a)
    (hcShape : c = pureEdgeCoeffs e z x)
    (hi : 2 * q i + 2 ≤ c i) :
    i = e ∨
      (i ≠ e ∧ i ≠ z ∧ i ≠ x ∧ q i = -1 ∧ c i = 0) := by
  by_cases hie : i = e
  · exact Or.inl hie
  right
  have hciNonneg : 0 ≤ c i := by
    have hqi := hqFloor i
    omega
  have hiz : i ≠ z := by
    intro hiz
    subst i
    rw [hcShape] at hciNonneg
    simp [pureEdgeCoeffs, Ne.symm hez, Ne.symm hxz] at hciNonneg
  have hix : i ≠ x := by
    intro hix
    subst i
    rw [hcShape] at hciNonneg
    simp [pureEdgeCoeffs, Ne.symm hex, hxz] at hciNonneg
  have hciZero : c i = 0 := by
    rw [hcShape]
    simp [pureEdgeCoeffs, hie, hiz, hix]
  have hqi : q i = -1 := by
    have hqFloorI := hqFloor i
    rw [hciZero] at hi
    omega
  exact ⟨hie, hiz, hix, hqi, hciZero⟩

omit [DecidableEq G] in
/-- Exact payload geometry when its private-heavy witness equals the retained
pure target.  The theorem retains the original pure coordinates and splits
according to whether the unique heavy center is the owner. -/
theorem minimalSupportTransversalShiftTargetPurePair_equalPrivateHeavy
    (g : Fin (m + 1) → G) {h t : G}
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1)) (hzB : z ∉ B)
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z)
    (q c : Fin (m + 1) → ℤ) (hq : Witness g t q)
    (hqzero : ∀ a ∈ B, q a = 0)
    (owner : ↥B) (k : Fin m) (i : Fin (m + 1))
    (hcowner : c owner ≠ 0)
    (hk : 2 ≤ c k.succ)
    (hkLocation : k.succ = owner ∨ k.succ ∉ B)
    (hi : 2 * q i + 2 ≤ c i)
    (hiLocation : i = owner ∨ i ∉ B)
    (hownerCoincide : k.succ = owner → i = owner)
    (heq : c = minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)) :
    ∃ x : Fin (m + 1), ∃ e : Fin m,
      x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ y, minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) y = -1 ↔
        y = z ∨ y = x) ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) =
        pureEdgeCoeffs e.succ z x ∧
      k.succ = e.succ ∧
      ((owner = e.succ ∧ i = e.succ ∧ q i = 0) ∨
        (owner = x ∧ e.succ ∉ B ∧ i ∉ B ∧
          i ≠ z ∧ i ≠ x ∧
          (i = e.succ ∨ (i ≠ e.succ ∧ q i = -1 ∧ c i = 0)))) := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  obtain ⟨x, e, hxz, hez, hex, homit, heTwo, hshape⟩ := hpure
  refine ⟨x, e, hxz, hez, hex, homit, heTwo, hshape, ?_⟩
  have hkPure : 2 ≤ pureEdgeCoeffs e.succ z x k.succ := by
    calc
      2 ≤ c k.succ := hk
      _ = p k.succ := by simpa [p, u] using congrFun heq k.succ
      _ = pureEdgeCoeffs e.succ z x k.succ := by
        simpa [p, u] using congrFun hshape k.succ
  have hkCenter : k.succ = e.succ :=
    pureEdgeCoeffs_ge_two_eq_center e.succ z x k.succ hez hex hxz hkPure
  refine ⟨hkCenter, ?_⟩
  have hcShape : c = pureEdgeCoeffs e.succ z x := by
    calc
      c = p := by simpa [p, u] using heq
      _ = pureEdgeCoeffs e.succ z x := by simpa [p, u] using hshape
  have hownerSupport : (owner : Fin (m + 1)) ∈
      ({e.succ, z, x} : Finset (Fin (m + 1))) := by
    rw [hcShape] at hcowner
    exact pureEdgeCoeffs_ne_zero_mem e.succ z x owner hcowner
  simp only [Finset.mem_insert, Finset.mem_singleton] at hownerSupport
  have hescape := quarterEscape_pureEdge_center_or_externalOmission
    q c e.succ z x i hez hex hxz hq.2.1 hcShape hi
  rcases hownerSupport with hownerCenter | hownerZ | hownerX
  · left
    have hkOwner : k.succ = (owner : Fin (m + 1)) :=
      hkCenter.trans hownerCenter.symm
    have hiOwner : i = (owner : Fin (m + 1)) := hownerCoincide hkOwner
    have hiCenter : i = e.succ := hiOwner.trans hownerCenter
    exact ⟨hownerCenter, hiCenter, by
      exact hqzero i (by rw [hiOwner]; exact owner.property)⟩
  · have hownerB : (owner : Fin (m + 1)) ∈ B := owner.property
    rw [hownerZ] at hownerB
    exact (hzB hownerB).elim
  · right
    have heB : e.succ ∉ B := by
      rcases hkLocation with hkOwner | hkExternal
      · have : e.succ = x := hkCenter.symm.trans (hkOwner.trans hownerX)
        exact (hex this).elim
      · rwa [hkCenter] at hkExternal
    have hiNotX : i ≠ x := by
      rcases hescape with hiCenter | ⟨_hiCenter, _hiZ, hiX, _hq, _hc⟩
      · exact hiCenter.trans_ne hex
      · exact hiX
    have hiB : i ∉ B := by
      rcases hiLocation with hiOwner | hiExternal
      · exact (hiNotX (hiOwner.trans hownerX)) |>.elim
      · exact hiExternal
    have hiNotZ : i ≠ z := by
      rcases hescape with hiCenter | ⟨_hiCenter, hiZ, _hiX, _hq, _hc⟩
      · exact hiCenter.trans_ne hez
      · exact hiZ
    refine ⟨hownerX, heB, hiB, hiNotZ, hiNotX, ?_⟩
    rcases hescape with hiCenter | ⟨hiNotCenter, _hiZ, _hiX, hqi, hci⟩
    · exact Or.inl hiCenter
    · exact Or.inr ⟨hiNotCenter, hqi, hci⟩

end MinModulus
