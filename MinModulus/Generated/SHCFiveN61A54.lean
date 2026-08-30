import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes61_54_00 : List ℕ := [131]

private theorem valid61_54_00 : ∀ code ∈ codes61_54_00, validRelationCode code := by
  decide

private theorem cover61_54_00 : ∀ q : IncreasingTwo 3,
    coveredNat 61 codes61_54_00 (blockValues 56 57 q) = true := by
  decide

private def codes61_54_01 : List ℕ := [772]

private theorem valid61_54_01 : ∀ code ∈ codes61_54_01, validRelationCode code := by
  decide

private theorem cover61_54_01 : ∀ q : IncreasingTwo 2,
    coveredNat 61 codes61_54_01 (blockValues 56 58 q) = true := by
  decide

theorem certificate61_a54
    (q : IncreasingFourTail 59 (⟨54, by norm_num⟩ : Fin 56)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 61 (increasingFourValues (N := 61) ⟨⟨54, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_54_00 _ valid61_54_00 (cover61_54_00 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_54_01 _ valid61_54_01 (cover61_54_01 q')

end MinModulus.SHCFiveCertificate.Generated
