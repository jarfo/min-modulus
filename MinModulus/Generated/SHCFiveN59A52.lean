import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes59_52_00 : List ℕ := [131]

private theorem valid59_52_00 : ∀ code ∈ codes59_52_00, validRelationCode code := by
  decide

private theorem cover59_52_00 : ∀ q : IncreasingTwo 3,
    coveredNat 59 codes59_52_00 (blockValues 54 55 q) = true := by
  decide

private def codes59_52_01 : List ℕ := [772]

private theorem valid59_52_01 : ∀ code ∈ codes59_52_01, validRelationCode code := by
  decide

private theorem cover59_52_01 : ∀ q : IncreasingTwo 2,
    coveredNat 59 codes59_52_01 (blockValues 54 56 q) = true := by
  decide

theorem certificate59_a52
    (q : IncreasingFourTail 57 (⟨52, by norm_num⟩ : Fin 54)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 59 (increasingFourValues (N := 59) ⟨⟨52, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_52_00 _ valid59_52_00 (cover59_52_00 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_52_01 _ valid59_52_01 (cover59_52_01 q')

end MinModulus.SHCFiveCertificate.Generated
