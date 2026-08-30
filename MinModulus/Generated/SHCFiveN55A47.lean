import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes55_47_00 : List ℕ := [131]

private theorem valid55_47_00 : ∀ code ∈ codes55_47_00, validRelationCode code := by
  decide

private theorem cover55_47_00 : ∀ q : IncreasingTwo 4,
    coveredNat 55 codes55_47_00 (blockValues 49 50 q) = true := by
  decide

private def codes55_47_01 : List ℕ := [77, 386]

private theorem valid55_47_01 : ∀ code ∈ codes55_47_01, validRelationCode code := by
  decide

private theorem cover55_47_01 : ∀ q : IncreasingTwo 3,
    coveredNat 55 codes55_47_01 (blockValues 49 51 q) = true := by
  decide

private def codes55_47_02 : List ℕ := [772]

private theorem valid55_47_02 : ∀ code ∈ codes55_47_02, validRelationCode code := by
  decide

private theorem cover55_47_02 : ∀ q : IncreasingTwo 2,
    coveredNat 55 codes55_47_02 (blockValues 49 52 q) = true := by
  decide

theorem certificate55_a47
    (q : IncreasingFourTail 53 (⟨47, by norm_num⟩ : Fin 50)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 55 (increasingFourValues (N := 55) ⟨⟨47, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_47_00 _ valid55_47_00 (cover55_47_00 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_47_01 _ valid55_47_01 (cover55_47_01 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_47_02 _ valid55_47_02 (cover55_47_02 q')

end MinModulus.SHCFiveCertificate.Generated
