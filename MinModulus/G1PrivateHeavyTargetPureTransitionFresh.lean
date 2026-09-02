/-
# Fresh endpoint in a pure-center transition

Two distinct coefficient-two witnesses with the same exact omission pair
force equality of the doubled center values.  In a cyclic even group, the
unique-involution argument then gives a common touched coordinate.  Under the
standing no-common-touch hypothesis, their centers must therefore coincide.

Apply this rigidity to the center-changing transition.  The new pure edge
already shares one endpoint with the old edge.  Its other endpoint cannot be
the other old endpoint, because that would give the same omission pair while
the centers are known to differ.  Thus every surviving transition changes
center and introduces a genuinely fresh endpoint.
-/
import MinModulus.G1PrivateHeavyTargetPureTransitionResidual

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Under no common touch and uniqueness of the nonzero involution, two
coefficient-two witnesses with the same exact omission pair have the same
center. -/
theorem exactPair_coeffTwo_centers_eq_of_no_common_touched
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {p c : Fin (m + 1) → ℤ}
    (hp : Witness g h p) (hc : Witness g h c)
    (z x e k : Fin (m + 1))
    (hxz : z ≠ x) (hez : e ≠ z) (hex : e ≠ x)
    (hkz : k ≠ z) (hkx : k ≠ x)
    (homitP : ∀ a, p a = -1 ↔ a = z ∨ a = x)
    (homitC : ∀ a, c a = -1 ↔ a = z ∨ a = x)
    (heTwo : p e = 2) (hkTwo : c k = 2) :
    e = k := by
  by_contra hek
  apply hno
  exact common_touched_of_two_smul_eq g hg hh hne hunique hek
    (two_smul_eq_of_same_exact_pair_coeff_two
      g hp hc z x e k hxz hez hex hkz hkx
        homitP homitC heTwo hkTwo)

omit [DecidableEq G] in
/-- The non-shared endpoint of a center-changing pure edge is outside the
old endpoint pair.  The conclusion retains the exact old/new omission and
center data needed to build the next finite transition state. -/
theorem MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_freshEndpoint
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (c : Fin (m + 1) → ℤ) (k : Fin m)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b z c k) :
    ∃ x : Fin (m + 1), ∃ e : Fin m,
      ∃ y w : Fin (m + 1),
        x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
        (∀ a, minimalSupportPrivateWitness g h hmin
            (minimalSupportTransversalShiftTarget g hno hmin b) a = -1 ↔
          a = z ∨ a = x) ∧
        minimalSupportPrivateWitness g h hmin
            (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
        (y = z ∨ y = x) ∧ y ≠ w ∧
        w ≠ z ∧ w ≠ x ∧
        k.succ ≠ y ∧ k.succ ≠ w ∧
        (∀ a, c a = -1 ↔ a = y ∨ a = w) ∧
        c k.succ = 2 ∧ k.succ ≠ e.succ := by
  obtain ⟨x, e, y, w, hxz, hez, hex, homitP, heTwo, _hpShape,
    hyEndpoint, hyw, hky, hkw, hc, homitC, hkTwo, _hcShape,
    hkCenter⟩ := hchange
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  have hp : Witness g h p :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  have homitP' : ∀ a, p a = -1 ↔ a = z ∨ a = x := by
    simpa [p, u] using homitP
  have heTwo' : p e.succ = 2 := by
    simpa [p, u] using heTwo
  have hwz : w ≠ z := by
    intro hwz
    have hyx : y = x := by
      rcases hyEndpoint with hyz | hyx
      · exact (hyw (hyz.trans hwz.symm)).elim
      · exact hyx
    have hkz : k.succ ≠ z := by simpa [hwz] using hkw
    have hkx : k.succ ≠ x := by simpa [hyx] using hky
    have homitC' : ∀ a, c a = -1 ↔ a = z ∨ a = x := by
      intro a
      simpa [hyx, hwz, or_comm] using homitC a
    have hcenters := exactPair_coeffTwo_centers_eq_of_no_common_touched
      g hg hh hne hunique hno hp hc z x e.succ k.succ
        (Ne.symm hxz) hez hex hkz hkx homitP' homitC' heTwo' hkTwo
    exact hkCenter hcenters.symm
  have hwx : w ≠ x := by
    intro hwx
    have hyz : y = z := by
      rcases hyEndpoint with hyz | hyx
      · exact hyz
      · exact (hyw (hyx.trans hwx.symm)).elim
    have hkz : k.succ ≠ z := by simpa [hyz] using hky
    have hkx : k.succ ≠ x := by simpa [hwx] using hkw
    have homitC' : ∀ a, c a = -1 ↔ a = z ∨ a = x := by
      intro a
      simpa [hyz, hwx] using homitC a
    have hcenters := exactPair_coeffTwo_centers_eq_of_no_common_touched
      g hg hh hne hunique hno hp hc z x e.succ k.succ
        (Ne.symm hxz) hez hex hkz hkx homitP' homitC' heTwo' hkTwo
    exact hkCenter hcenters.symm
  exact ⟨x, e, y, w, hxz, hez, hex, homitP, heTwo,
    hyEndpoint, hyw, hwz, hwx, hky, hkw, homitC, hkTwo, hkCenter⟩

/-- Critical cyclic specialization of the fresh-endpoint transition. -/
theorem MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_freshEndpoint_zmod
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ a : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r →
        r a ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (b : ↥B) (z : Fin (n + 1))
    (c : Fin (n + 1) → ℤ) (k : Fin n)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
        hno hmin b z c k) :
    ∃ x : Fin (n + 1), ∃ e : Fin n,
      ∃ y w : Fin (n + 1),
        x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
        (∀ a, minimalSupportPrivateWitness g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
              (minimalSupportTransversalShiftTarget g hno hmin b) a = -1 ↔
          a = z ∨ a = x) ∧
        minimalSupportPrivateWitness g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin
              (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
        (y = z ∨ y = x) ∧ y ≠ w ∧
        w ≠ z ∧ w ≠ x ∧
        k.succ ≠ y ∧ k.succ ≠ w ∧
        (∀ a, c a = -1 ↔ a = y ∨ a = w) ∧
        c k.succ = 2 ∧ k.succ ≠ e.succ := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  exact hchange.exists_freshEndpoint g hg
    (half_add_half hN) (half_ne_zero hN hM)
    (fun u hu => zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
      hno hmin b z c k

end MinModulus
