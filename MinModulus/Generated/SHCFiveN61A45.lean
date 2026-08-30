import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes61_45_00 : List ℕ := [131]

private theorem valid61_45_00 : ∀ code ∈ codes61_45_00, validRelationCode code := by
  decide

private theorem cover61_45_00 : ∀ q : IncreasingTwo 12,
    coveredNat 61 codes61_45_00 (blockValues 47 48 q) = true := by
  decide

private def codes61_45_01 : List ℕ := [17, 642, 85, 521, 402, 589, 261, 2626, 2631, 772]

private theorem valid61_45_01 : ∀ code ∈ codes61_45_01, validRelationCode code := by
  decide

private theorem cover61_45_01 : ∀ q : IncreasingTwo 11,
    coveredNat 61 codes61_45_01 (blockValues 47 49 q) = true := by
  decide

private def codes61_45_02 : List ℕ := [17, 521, 261, 403, 402, 589, 643, 642, 85]

private theorem valid61_45_02 : ∀ code ∈ codes61_45_02, validRelationCode code := by
  decide

private theorem cover61_45_02 : ∀ q : IncreasingTwo 10,
    coveredNat 61 codes61_45_02 (blockValues 47 50 q) = true := by
  decide

private def codes61_45_03 : List ℕ := [17, 521, 261, 4234, 643, 642, 85, 770]

private theorem valid61_45_03 : ∀ code ∈ codes61_45_03, validRelationCode code := by
  decide

private theorem cover61_45_03 : ∀ q : IncreasingTwo 9,
    coveredNat 61 codes61_45_03 (blockValues 47 51 q) = true := by
  decide

private def codes61_45_04 : List ℕ := [17, 521, 261, 1347, 77, 386, 93]

private theorem valid61_45_04 : ∀ code ∈ codes61_45_04, validRelationCode code := by
  decide

private theorem cover61_45_04 : ∀ q : IncreasingTwo 8,
    coveredNat 61 codes61_45_04 (blockValues 47 52 q) = true := by
  decide

private def codes61_45_05 : List ℕ := [77, 386, 17, 521, 387, 898]

private theorem valid61_45_05 : ∀ code ∈ codes61_45_05, validRelationCode code := by
  decide

private theorem cover61_45_05 : ∀ q : IncreasingTwo 7,
    coveredNat 61 codes61_45_05 (blockValues 47 53 q) = true := by
  decide

private def codes61_45_06 : List ℕ := [1346]

private theorem valid61_45_06 : ∀ code ∈ codes61_45_06, validRelationCode code := by
  decide

private theorem cover61_45_06 : ∀ q : IncreasingTwo 6,
    coveredNat 61 codes61_45_06 (blockValues 47 54 q) = true := by
  decide

private def codes61_45_07 : List ℕ := [17, 521, 261, 772]

private theorem valid61_45_07 : ∀ code ∈ codes61_45_07, validRelationCode code := by
  decide

private theorem cover61_45_07 : ∀ q : IncreasingTwo 5,
    coveredNat 61 codes61_45_07 (blockValues 47 55 q) = true := by
  decide

private def codes61_45_08 : List ℕ := [17, 521, 153]

private theorem valid61_45_08 : ∀ code ∈ codes61_45_08, validRelationCode code := by
  decide

private theorem cover61_45_08 : ∀ q : IncreasingTwo 4,
    coveredNat 61 codes61_45_08 (blockValues 47 56 q) = true := by
  decide

private def codes61_45_09 : List ℕ := [17, 153]

private theorem valid61_45_09 : ∀ code ∈ codes61_45_09, validRelationCode code := by
  decide

private theorem cover61_45_09 : ∀ q : IncreasingTwo 3,
    coveredNat 61 codes61_45_09 (blockValues 47 57 q) = true := by
  decide

private def codes61_45_10 : List ℕ := [772]

private theorem valid61_45_10 : ∀ code ∈ codes61_45_10, validRelationCode code := by
  decide

private theorem cover61_45_10 : ∀ q : IncreasingTwo 2,
    coveredNat 61 codes61_45_10 (blockValues 47 58 q) = true := by
  decide

theorem certificate61_a45
    (q : IncreasingFourTail 59 (⟨45, by norm_num⟩ : Fin 56)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 61 (increasingFourValues (N := 61) ⟨⟨45, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (12 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 12 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_00 _ valid61_45_00 (cover61_45_00 q')
  · let c' : Fin (11 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 11 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_01 _ valid61_45_01 (cover61_45_01 q')
  · let c' : Fin (10 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 10 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_02 _ valid61_45_02 (cover61_45_02 q')
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_03 _ valid61_45_03 (cover61_45_03 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_04 _ valid61_45_04 (cover61_45_04 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_05 _ valid61_45_05 (cover61_45_05 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_06 _ valid61_45_06 (cover61_45_06 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_07 _ valid61_45_07 (cover61_45_07 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_08 _ valid61_45_08 (cover61_45_08 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_09 _ valid61_45_09 (cover61_45_09 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_45_10 _ valid61_45_10 (cover61_45_10 q')

end MinModulus.SHCFiveCertificate.Generated
