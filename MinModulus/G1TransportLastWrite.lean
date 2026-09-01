import MinModulus.G1TransportSubsetOrbit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every property realized before a finite endpoint has a last realization,
with the remaining interval expressed in the form needed by orbit recursion. -/
theorem exists_last_before
    (P : ℕ → Prop) [DecidablePred P] (L : ℕ)
    (hP : ∃ t < L, P t) :
    ∃ k d, k + 1 + d = L ∧ P k ∧
      ∀ t < d, ¬P (k + 1 + t) := by
  obtain ⟨t, htL, htP⟩ := hP
  let k := Nat.findGreatest P (L - 1)
  have htLe : t ≤ L - 1 := by omega
  have hkP : P k := Nat.findGreatest_spec htLe htP
  have hkLe : k ≤ L - 1 := Nat.findGreatest_le (L - 1)
  have hkOneLe : k + 1 ≤ L := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkOneLe
  refine ⟨k, d, by omega, hkP, ?_⟩
  intro u hu
  exact Nat.findGreatest_is_greatest
    (P := P) (n := L - 1) (k := k + 1 + u)
      (by simp only [k]; omega) (by omega)

namespace LiveRestorationPermutationSystem

variable {ι : Type*} [DecidableEq ι]
variable {g : Fin (m + 1) → G} {h : G}
variable {I : Finset ι} {e : ι → LiveRestorationEdgeDatum g h}

/-- If a coordinate is untouched by the next `d` selected target supports,
its membership bit is preserved across that whole orbit interval. -/
theorem mem_orbitSourceSubset_add_iff_of_untouched
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier)
    (a : Fin m) (k d : ℕ)
    (huntouched : ∀ t < d,
      a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex (k + t) x)).target) :
    a ∈ S.orbitSourceSubset (k + d) x ↔
      a ∈ S.orbitSourceSubset k x := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprefix : ∀ t < d,
          a ∉ reducedCollisionSupport
            (e (S.orbitSourceIndex (k + t) x)).target := by
        intro t ht
        exact huntouched t (by omega)
      have hlast : a ∉ reducedCollisionSupport
          (e (S.orbitSourceIndex (k + d) x)).target := by
        exact huntouched d (by omega)
      have hstep := S.mem_orbitSourceSubset_succ_iff (k + d) x a
      have hBnot : a ∉ (e (S.orbitSourceIndex (k + d) x)).target.val.2 := by
        intro haB
        exact hlast (Finset.mem_union_right _ haB)
      rw [show k + (d + 1) = (k + d) + 1 by omega, hstep]
      simp only [hBnot, false_or]
      exact (and_iff_left hlast).trans (ih hprefix)

/-- Last-write theorem for an orbit interval.  If step `k` touches a
coordinate and the following `d` steps do not, then its terminal bit is
exactly the bit written by the negative tail at step `k`. -/
theorem mem_orbitSourceSubset_after_last_touch_iff
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier)
    (a : Fin m) (k d : ℕ)
    (htouch : a ∈ reducedCollisionSupport
      (e (S.orbitSourceIndex k x)).target)
    (hlaterUntouched : ∀ t < d,
      a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex (k + 1 + t) x)).target) :
    a ∈ S.orbitSourceSubset (k + 1 + d) x ↔
      a ∈ (e (S.orbitSourceIndex k x)).target.val.2 := by
  have htail := S.mem_orbitSourceSubset_add_iff_of_untouched
    x a (k + 1) d (by
      intro t ht
      simpa [Nat.add_assoc] using hlaterUntouched t ht)
  have hstep := S.mem_orbitSourceSubset_succ_iff k x a
  have houtsideFalse : ¬(a ∈ S.orbitSourceSubset k x ∧
      a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex k x)).target) := by
    intro ha
    exact ha.2 htouch
  rw [htail, hstep]
  simp only [houtsideFalse, or_false]

/-- On a closed orbit, the last selected support touching a coordinate must
write exactly its initial membership bit. -/
theorem mem_initial_iff_mem_negative_of_last_touch_before_order
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier)
    (a : Fin m) (k d : ℕ)
    (hlength : k + 1 + d = orderOf S.partitionedTransport.toPerm)
    (htouch : a ∈ reducedCollisionSupport
      (e (S.orbitSourceIndex k x)).target)
    (hlaterUntouched : ∀ t < d,
      a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex (k + 1 + t) x)).target) :
    a ∈ S.orbitSourceSubset 0 x ↔
      a ∈ (e (S.orbitSourceIndex k x)).target.val.2 := by
  have hlast := S.mem_orbitSourceSubset_after_last_touch_iff
    x a k d htouch hlaterUntouched
  rw [hlength, S.orbitSourceSubset_orderOf_eq] at hlast
  exact hlast

/-- Dually, if the last touching target writes zero at a coordinate (the
coordinate lies in its positive tail), then that coordinate is absent from
the initial/terminal source subset. -/
theorem not_mem_initial_of_last_touch_positive
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier)
    (a : Fin m) (k d : ℕ)
    (hlength : k + 1 + d = orderOf S.partitionedTransport.toPerm)
    (haPositive : a ∈ (e (S.orbitSourceIndex k x)).target.val.1)
    (hlaterUntouched : ∀ t < d,
      a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex (k + 1 + t) x)).target) :
    a ∉ S.orbitSourceSubset 0 x := by
  have htouch : a ∈ reducedCollisionSupport
      (e (S.orbitSourceIndex k x)).target :=
    Finset.mem_union_left _ haPositive
  have hiff := S.mem_initial_iff_mem_negative_of_last_touch_before_order
    x a k d hlength htouch hlaterUntouched
  intro haInitial
  have haNegative := hiff.mp haInitial
  exact Finset.disjoint_left.mp
    (e (S.orbitSourceIndex k x)).target.property.1
      haPositive haNegative

/-- Any coordinate touched somewhere on the closed orbit has a canonical last
touch, and its initial/terminal bit is the negative-tail bit written there. -/
theorem exists_last_touch_initial_iff_negative
    (S : LiveRestorationPermutationSystem g h I e)
    (x : S.partitionedTransport.carrier)
    (a : Fin m)
    (htouched : ∃ t < orderOf S.partitionedTransport.toPerm,
      a ∈ reducedCollisionSupport
        (e (S.orbitSourceIndex t x)).target) :
    ∃ k d,
      k + 1 + d = orderOf S.partitionedTransport.toPerm ∧
      a ∈ reducedCollisionSupport
        (e (S.orbitSourceIndex k x)).target ∧
      (∀ t < d, a ∉ reducedCollisionSupport
        (e (S.orbitSourceIndex (k + 1 + t) x)).target) ∧
      (a ∈ S.orbitSourceSubset 0 x ↔
        a ∈ (e (S.orbitSourceIndex k x)).target.val.2) := by
  obtain ⟨k, d, hlength, htouch, hlater⟩ :=
    exists_last_before
      (fun t ↦ a ∈ reducedCollisionSupport
        (e (S.orbitSourceIndex t x)).target)
      (orderOf S.partitionedTransport.toPerm) htouched
  exact ⟨k, d, hlength, htouch, hlater,
    S.mem_initial_iff_mem_negative_of_last_touch_before_order
      x a k d hlength htouch hlater⟩

end LiveRestorationPermutationSystem

end MinModulus
