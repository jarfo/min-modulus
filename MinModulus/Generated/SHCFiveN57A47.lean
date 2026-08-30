import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes57_47_00 : List ℕ := [131]

private theorem valid57_47_00 : ∀ code ∈ codes57_47_00, validRelationCode code := by
  decide

private theorem cover57_47_00 : ∀ q : IncreasingTwo 6,
    coveredNat 57 codes57_47_00 (blockValues 49 50 q) = true := by
  decide

private def codes57_47_01 : List ℕ := [17, 642, 85, 89]

private theorem valid57_47_01 : ∀ code ∈ codes57_47_01, validRelationCode code := by
  decide

private theorem cover57_47_01 : ∀ q : IncreasingTwo 5,
    coveredNat 57 codes57_47_01 (blockValues 49 51 q) = true := by
  decide

private def codes57_47_02 : List ℕ := [77, 386, 898]

private theorem valid57_47_02 : ∀ code ∈ codes57_47_02, validRelationCode code := by
  decide

private theorem cover57_47_02 : ∀ q : IncreasingTwo 4,
    coveredNat 57 codes57_47_02 (blockValues 49 52 q) = true := by
  decide

private def codes57_47_03 : List ℕ := [1346]

private theorem valid57_47_03 : ∀ code ∈ codes57_47_03, validRelationCode code := by
  decide

private theorem cover57_47_03 : ∀ q : IncreasingTwo 3,
    coveredNat 57 codes57_47_03 (blockValues 49 53 q) = true := by
  decide

private def codes57_47_04 : List ℕ := [772]

private theorem valid57_47_04 : ∀ code ∈ codes57_47_04, validRelationCode code := by
  decide

private theorem cover57_47_04 : ∀ q : IncreasingTwo 2,
    coveredNat 57 codes57_47_04 (blockValues 49 54 q) = true := by
  decide

theorem certificate57_a47
    (q : IncreasingFourTail 55 (⟨47, by norm_num⟩ : Fin 52)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 57 (increasingFourValues (N := 57) ⟨⟨47, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_47_00 _ valid57_47_00 (cover57_47_00 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_47_01 _ valid57_47_01 (cover57_47_01 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_47_02 _ valid57_47_02 (cover57_47_02 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_47_03 _ valid57_47_03 (cover57_47_03 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_47_04 _ valid57_47_04 (cover57_47_04 q')

end MinModulus.SHCFiveCertificate.Generated
