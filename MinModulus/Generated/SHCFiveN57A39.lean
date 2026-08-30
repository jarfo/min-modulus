import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes57_39_00 : List ℕ := [131]

private theorem valid57_39_00 : ∀ code ∈ codes57_39_00, validRelationCode code := by
  decide

private theorem cover57_39_00 : ∀ q : IncreasingTwo 14,
    coveredNat 57 codes57_39_00 (blockValues 41 42 q) = true := by
  decide

private def codes57_39_01 : List ℕ := [17, 642, 85, 521, 402, 589, 261, 2626, 2631, 772, 4227, 2308]

private theorem valid57_39_01 : ∀ code ∈ codes57_39_01, validRelationCode code := by
  decide

private theorem cover57_39_01 : ∀ q : IncreasingTwo 13,
    coveredNat 57 codes57_39_01 (blockValues 41 43 q) = true := by
  decide

private def codes57_39_02 : List ℕ := [17, 521, 261, 403, 402, 589, 643, 642, 85, 2786, 771]

private theorem valid57_39_02 : ∀ code ∈ codes57_39_02, validRelationCode code := by
  decide

private theorem cover57_39_02 : ∀ q : IncreasingTwo 12,
    coveredNat 57 codes57_39_02 (blockValues 41 44 q) = true := by
  decide

private def codes57_39_03 : List ℕ := [17, 521, 261, 4234, 643, 642, 85, 1668, 3911, 3906]

private theorem valid57_39_03 : ∀ code ∈ codes57_39_03, validRelationCode code := by
  decide

private theorem cover57_39_03 : ∀ q : IncreasingTwo 11,
    coveredNat 57 codes57_39_03 (blockValues 41 45 q) = true := by
  decide

private def codes57_39_04 : List ℕ := [17, 521, 261, 1528, 4234, 643, 642, 85, 770]

private theorem valid57_39_04 : ∀ code ∈ codes57_39_04, validRelationCode code := by
  decide

private theorem cover57_39_04 : ∀ q : IncreasingTwo 10,
    coveredNat 57 codes57_39_04 (blockValues 41 46 q) = true := by
  decide

private def codes57_39_05 : List ℕ := [17, 521, 261, 1347, 77, 386, 387, 898]

private theorem valid57_39_05 : ∀ code ∈ codes57_39_05, validRelationCode code := by
  decide

private theorem cover57_39_05 : ∀ q : IncreasingTwo 9,
    coveredNat 57 codes57_39_05 (blockValues 41 47 q) = true := by
  decide

private def codes57_39_06 : List ℕ := [77, 386, 17, 521, 387, 2954, 899]

private theorem valid57_39_06 : ∀ code ∈ codes57_39_06, validRelationCode code := by
  decide

private theorem cover57_39_06 : ∀ q : IncreasingTwo 8,
    coveredNat 57 codes57_39_06 (blockValues 41 48 q) = true := by
  decide

private def codes57_39_07 : List ℕ := [1346]

private theorem valid57_39_07 : ∀ code ∈ codes57_39_07, validRelationCode code := by
  decide

private theorem cover57_39_07 : ∀ q : IncreasingTwo 7,
    coveredNat 57 codes57_39_07 (blockValues 41 49 q) = true := by
  decide

private def codes57_39_08 : List ℕ := [17, 521, 261, 3946, 772]

private theorem valid57_39_08 : ∀ code ∈ codes57_39_08, validRelationCode code := by
  decide

private theorem cover57_39_08 : ∀ q : IncreasingTwo 6,
    coveredNat 57 codes57_39_08 (blockValues 41 50 q) = true := by
  decide

private def codes57_39_09 : List ℕ := [17, 521, 261, 772]

private theorem valid57_39_09 : ∀ code ∈ codes57_39_09, validRelationCode code := by
  decide

private theorem cover57_39_09 : ∀ q : IncreasingTwo 5,
    coveredNat 57 codes57_39_09 (blockValues 41 51 q) = true := by
  decide

private def codes57_39_10 : List ℕ := [17, 521, 153]

private theorem valid57_39_10 : ∀ code ∈ codes57_39_10, validRelationCode code := by
  decide

private theorem cover57_39_10 : ∀ q : IncreasingTwo 4,
    coveredNat 57 codes57_39_10 (blockValues 41 52 q) = true := by
  decide

private def codes57_39_11 : List ℕ := [17, 153]

private theorem valid57_39_11 : ∀ code ∈ codes57_39_11, validRelationCode code := by
  decide

private theorem cover57_39_11 : ∀ q : IncreasingTwo 3,
    coveredNat 57 codes57_39_11 (blockValues 41 53 q) = true := by
  decide

private def codes57_39_12 : List ℕ := [772]

private theorem valid57_39_12 : ∀ code ∈ codes57_39_12, validRelationCode code := by
  decide

private theorem cover57_39_12 : ∀ q : IncreasingTwo 2,
    coveredNat 57 codes57_39_12 (blockValues 41 54 q) = true := by
  decide

theorem certificate57_a39
    (q : IncreasingFourTail 55 (⟨39, by norm_num⟩ : Fin 52)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 57 (increasingFourValues (N := 57) ⟨⟨39, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (14 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 14 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_00 _ valid57_39_00 (cover57_39_00 q')
  · let c' : Fin (13 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 13 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_01 _ valid57_39_01 (cover57_39_01 q')
  · let c' : Fin (12 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 12 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_02 _ valid57_39_02 (cover57_39_02 q')
  · let c' : Fin (11 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 11 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_03 _ valid57_39_03 (cover57_39_03 q')
  · let c' : Fin (10 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 10 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_04 _ valid57_39_04 (cover57_39_04 q')
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_05 _ valid57_39_05 (cover57_39_05 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_06 _ valid57_39_06 (cover57_39_06 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_07 _ valid57_39_07 (cover57_39_07 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_08 _ valid57_39_08 (cover57_39_08 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_09 _ valid57_39_09 (cover57_39_09 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_10 _ valid57_39_10 (cover57_39_10 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_11 _ valid57_39_11 (cover57_39_11 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_39_12 _ valid57_39_12 (cover57_39_12 q')

end MinModulus.SHCFiveCertificate.Generated
