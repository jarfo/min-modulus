import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes57_49_00 : List ℕ := [131]

private theorem valid57_49_00 : ∀ code ∈ codes57_49_00, validRelationCode code := by
  decide

private theorem cover57_49_00 : ∀ q : IncreasingTwo 4,
    coveredNat 57 codes57_49_00 (blockValues 51 52 q) = true := by
  decide

private def codes57_49_01 : List ℕ := [77, 386]

private theorem valid57_49_01 : ∀ code ∈ codes57_49_01, validRelationCode code := by
  decide

private theorem cover57_49_01 : ∀ q : IncreasingTwo 3,
    coveredNat 57 codes57_49_01 (blockValues 51 53 q) = true := by
  decide

private def codes57_49_02 : List ℕ := [772]

private theorem valid57_49_02 : ∀ code ∈ codes57_49_02, validRelationCode code := by
  decide

private theorem cover57_49_02 : ∀ q : IncreasingTwo 2,
    coveredNat 57 codes57_49_02 (blockValues 51 54 q) = true := by
  decide

theorem certificate57_a49
    (q : IncreasingFourTail 55 (⟨49, by norm_num⟩ : Fin 52)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 57 (increasingFourValues (N := 57) ⟨⟨49, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_49_00 _ valid57_49_00 (cover57_49_00 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_49_01 _ valid57_49_01 (cover57_49_01 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_49_02 _ valid57_49_02 (cover57_49_02 q')

end MinModulus.SHCFiveCertificate.Generated
