import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes59_47_00 : List ℕ := [131]

private theorem valid59_47_00 : ∀ code ∈ codes59_47_00, validRelationCode code := by
  decide

private theorem cover59_47_00 : ∀ q : IncreasingTwo 8,
    coveredNat 59 codes59_47_00 (blockValues 49 50 q) = true := by
  decide

private def codes59_47_01 : List ℕ := [17, 642, 85, 521, 402, 89]

private theorem valid59_47_01 : ∀ code ∈ codes59_47_01, validRelationCode code := by
  decide

private theorem cover59_47_01 : ∀ q : IncreasingTwo 7,
    coveredNat 59 codes59_47_01 (blockValues 49 51 q) = true := by
  decide

private def codes59_47_02 : List ℕ := [17, 521, 261, 403, 772]

private theorem valid59_47_02 : ∀ code ∈ codes59_47_02, validRelationCode code := by
  decide

private theorem cover59_47_02 : ∀ q : IncreasingTwo 6,
    coveredNat 59 codes59_47_02 (blockValues 49 52 q) = true := by
  decide

private def codes59_47_03 : List ℕ := [77, 386, 17, 93]

private theorem valid59_47_03 : ∀ code ∈ codes59_47_03, validRelationCode code := by
  decide

private theorem cover59_47_03 : ∀ q : IncreasingTwo 5,
    coveredNat 59 codes59_47_03 (blockValues 49 53 q) = true := by
  decide

private def codes59_47_04 : List ℕ := [1346]

private theorem valid59_47_04 : ∀ code ∈ codes59_47_04, validRelationCode code := by
  decide

private theorem cover59_47_04 : ∀ q : IncreasingTwo 4,
    coveredNat 59 codes59_47_04 (blockValues 49 54 q) = true := by
  decide

private def codes59_47_05 : List ℕ := [17, 153]

private theorem valid59_47_05 : ∀ code ∈ codes59_47_05, validRelationCode code := by
  decide

private theorem cover59_47_05 : ∀ q : IncreasingTwo 3,
    coveredNat 59 codes59_47_05 (blockValues 49 55 q) = true := by
  decide

private def codes59_47_06 : List ℕ := [772]

private theorem valid59_47_06 : ∀ code ∈ codes59_47_06, validRelationCode code := by
  decide

private theorem cover59_47_06 : ∀ q : IncreasingTwo 2,
    coveredNat 59 codes59_47_06 (blockValues 49 56 q) = true := by
  decide

theorem certificate59_a47
    (q : IncreasingFourTail 57 (⟨47, by norm_num⟩ : Fin 54)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 59 (increasingFourValues (N := 59) ⟨⟨47, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_00 _ valid59_47_00 (cover59_47_00 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_01 _ valid59_47_01 (cover59_47_01 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_02 _ valid59_47_02 (cover59_47_02 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_03 _ valid59_47_03 (cover59_47_03 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_04 _ valid59_47_04 (cover59_47_04 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_05 _ valid59_47_05 (cover59_47_05 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_47_06 _ valid59_47_06 (cover59_47_06 q')

end MinModulus.SHCFiveCertificate.Generated
