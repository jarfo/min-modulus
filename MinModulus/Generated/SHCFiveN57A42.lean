import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes57_42_00 : List ℕ := [131]

private theorem valid57_42_00 : ∀ code ∈ codes57_42_00, validRelationCode code := by
  decide

private theorem cover57_42_00 : ∀ q : IncreasingTwo 11,
    coveredNat 57 codes57_42_00 (blockValues 44 45 q) = true := by
  decide

private def codes57_42_01 : List ℕ := [17, 642, 85, 521, 402, 589, 261, 2626, 153]

private theorem valid57_42_01 : ∀ code ∈ codes57_42_01, validRelationCode code := by
  decide

private theorem cover57_42_01 : ∀ q : IncreasingTwo 10,
    coveredNat 57 codes57_42_01 (blockValues 44 46 q) = true := by
  decide

private def codes57_42_02 : List ℕ := [17, 521, 261, 403, 402, 589, 643, 642]

private theorem valid57_42_02 : ∀ code ∈ codes57_42_02, validRelationCode code := by
  decide

private theorem cover57_42_02 : ∀ q : IncreasingTwo 9,
    coveredNat 57 codes57_42_02 (blockValues 44 47 q) = true := by
  decide

private def codes57_42_03 : List ℕ := [17, 521, 261, 4234, 643, 642, 85]

private theorem valid57_42_03 : ∀ code ∈ codes57_42_03, validRelationCode code := by
  decide

private theorem cover57_42_03 : ∀ q : IncreasingTwo 8,
    coveredNat 57 codes57_42_03 (blockValues 44 48 q) = true := by
  decide

private def codes57_42_04 : List ℕ := [17, 521, 261, 77, 386, 93]

private theorem valid57_42_04 : ∀ code ∈ codes57_42_04, validRelationCode code := by
  decide

private theorem cover57_42_04 : ∀ q : IncreasingTwo 7,
    coveredNat 57 codes57_42_04 (blockValues 44 49 q) = true := by
  decide

private def codes57_42_05 : List ℕ := [386, 17, 521, 387, 898]

private theorem valid57_42_05 : ∀ code ∈ codes57_42_05, validRelationCode code := by
  decide

private theorem cover57_42_05 : ∀ q : IncreasingTwo 6,
    coveredNat 57 codes57_42_05 (blockValues 44 50 q) = true := by
  decide

private def codes57_42_06 : List ℕ := [1506]

private theorem valid57_42_06 : ∀ code ∈ codes57_42_06, validRelationCode code := by
  decide

private theorem cover57_42_06 : ∀ q : IncreasingTwo 5,
    coveredNat 57 codes57_42_06 (blockValues 44 51 q) = true := by
  decide

private def codes57_42_07 : List ℕ := [17, 521, 153]

private theorem valid57_42_07 : ∀ code ∈ codes57_42_07, validRelationCode code := by
  decide

private theorem cover57_42_07 : ∀ q : IncreasingTwo 4,
    coveredNat 57 codes57_42_07 (blockValues 44 52 q) = true := by
  decide

private def codes57_42_08 : List ℕ := [17, 153]

private theorem valid57_42_08 : ∀ code ∈ codes57_42_08, validRelationCode code := by
  decide

private theorem cover57_42_08 : ∀ q : IncreasingTwo 3,
    coveredNat 57 codes57_42_08 (blockValues 44 53 q) = true := by
  decide

private def codes57_42_09 : List ℕ := [772]

private theorem valid57_42_09 : ∀ code ∈ codes57_42_09, validRelationCode code := by
  decide

private theorem cover57_42_09 : ∀ q : IncreasingTwo 2,
    coveredNat 57 codes57_42_09 (blockValues 44 54 q) = true := by
  decide

theorem certificate57_a42
    (q : IncreasingFourTail 55 (⟨42, by norm_num⟩ : Fin 52)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 57 (increasingFourValues (N := 57) ⟨⟨42, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (11 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 11 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_00 _ valid57_42_00 (cover57_42_00 q')
  · let c' : Fin (10 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 10 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_01 _ valid57_42_01 (cover57_42_01 q')
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_02 _ valid57_42_02 (cover57_42_02 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_03 _ valid57_42_03 (cover57_42_03 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_04 _ valid57_42_04 (cover57_42_04 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_05 _ valid57_42_05 (cover57_42_05 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_06 _ valid57_42_06 (cover57_42_06 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_07 _ valid57_42_07 (cover57_42_07 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_08 _ valid57_42_08 (cover57_42_08 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_42_09 _ valid57_42_09 (cover57_42_09 q')

end MinModulus.SHCFiveCertificate.Generated
