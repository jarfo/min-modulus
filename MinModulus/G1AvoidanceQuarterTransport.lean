/-
# Transporting the quarter quartet to the next half target

When `N = 2M` and `M = 2K`, a point `t : ZMod N` with `2t = M` maps to
`K : ZMod M`.  Every witness at `t` therefore maps coefficient-for-
coefficient to a half-witness for the reduced tuple modulo `M`.  Applied to
the all-zero triangle quartet, this produces four explicit omission layers
at the next descent target.
-/
import MinModulus.G1AvoidanceTriangleQuarterLayers
import MinModulus.G1QuarterCenterTransport

namespace MinModulus

open Finset

variable {m : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Witnesses transport along additive homomorphisms without changing their
integer coefficient vector. -/
theorem witness_map_addMonoidHom
    (f : G →+ H) (g : Fin m → G) {h : G} {c : Fin m → ℤ}
    (hc : Witness g h c) : Witness (fun i ↦ f (g i)) (f h) c := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  calc
    (∑ i, c i • f (g i)) = ∑ i, f (c i • g i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul]
    _ = f (∑ i, c i • g i) := (map_sum f _ _).symm
    _ = f h := by rw [hc.2.2.2]

/-- The six-coordinate omission quartet at a fixed target. -/
def WitnessOmissionQuartetAt (g : Fin m → G) (t : G) : Prop :=
  ∃ a b d x y z : Fin m, ∃ c0 c1 c2 c3 : Fin m → ℤ,
    a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
    (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
    (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
    (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
    x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    Witness g t c0 ∧ ExactOmissions c0 {a, b, d} ∧
    Witness g t c1 ∧ ExactOmissions c1 {y, z} ∧
    Witness g t c2 ∧ ExactOmissions c2 {z, x} ∧
    Witness g t c3 ∧ ExactOmissions c3 {x, y}

/-- A quarter omission quartet modulo `N` maps to a half-target quartet for
the reduced tuple modulo `M`. -/
theorem quarterOmissionQuartet_castsToHalf
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N)
    (hquartet : WitnessQuarterOmissionQuartet g (M : ZMod N)) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    WitnessOmissionQuartetAt (fun i ↦ f (g i)) (K : ZMod M) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  dsimp only
  obtain ⟨t, a, b, d, x, y, z, c0, c1, c2, c3, ht,
    hab, hbd, hda, hx, hy, hz, hxy, hyz, hzx,
    hc0, h0, hc1, h1, hc2, h2, hc3, h3⟩ := hquartet
  have htcast : f t = (K : ZMod M) :=
    quarterCenter_cast_eq_half hN hM hK t ht
  have hc0' := witness_map_addMonoidHom f.toAddMonoidHom g hc0
  have hc1' := witness_map_addMonoidHom f.toAddMonoidHom g hc1
  have hc2' := witness_map_addMonoidHom f.toAddMonoidHom g hc2
  have hc3' := witness_map_addMonoidHom f.toAddMonoidHom g hc3
  change Witness (fun i ↦ f (g i)) (f t) c0 at hc0'
  change Witness (fun i ↦ f (g i)) (f t) c1 at hc1'
  change Witness (fun i ↦ f (g i)) (f t) c2 at hc2'
  change Witness (fun i ↦ f (g i)) (f t) c3 at hc3'
  rw [htcast] at hc0' hc1' hc2' hc3'
  exact ⟨a, b, d, x, y, z, c0, c1, c2, c3,
    hab, hbd, hda, hx, hy, hz, hxy, hyz, hzx,
    hc0', h0, hc1', h1, hc2', h2, hc3', h3⟩

/-- The same transport for a bare quarter point. -/
theorem quarterPoint_castsToHalf
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (hquarter : WitnessQuarterPoint (M : ZMod N)) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    ∃ t : ZMod N, t + t = (M : ZMod N) ∧
      f t = (K : ZMod M) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  dsimp only
  obtain ⟨t, ht⟩ := hquarter
  exact ⟨t, ht, quarterCenter_cast_eq_half hN hM hK t ht⟩

/-- Specialized depth form: for `s≥1`, a quarter quartet at modulus
`2^(s+1)q` becomes four half-witnesses modulo `2^s q`. -/
theorem quarterOmissionQuartet_castsTo_nextTwoAdicHalf
    {s q : ℕ} (hs : 1 ≤ s) (hq : 0 < q)
    (g : Fin m → ZMod (2 ^ (s + 1) * q))
    (hquartet : WitnessQuarterOmissionQuartet g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    let f : ZMod (2 ^ (s + 1) * q) →+* ZMod (2 ^ s * q) :=
      ZMod.castHom (show 2 ^ s * q ∣ 2 ^ (s + 1) * q by
        exact ⟨2, by rw [pow_succ]; ring⟩) (ZMod (2 ^ s * q))
    WitnessOmissionQuartetAt (fun i ↦ f (g i))
      ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) := by
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 2 ^ s * q = 2 * (2 ^ (s - 1) * q) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  have hK : 0 < 2 ^ (s - 1) * q :=
    mul_pos (pow_pos (by norm_num) _) hq
  letI : NeZero (2 ^ (s + 1) * q) := ⟨Nat.ne_of_gt
    (mul_pos (pow_pos (by norm_num) _) hq)⟩
  simpa using quarterOmissionQuartet_castsToHalf hN hM hK g hquartet

end MinModulus
