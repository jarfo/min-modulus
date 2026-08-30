import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes61_48_00 : List ℕ := [131]

private theorem valid61_48_00 : ∀ code ∈ codes61_48_00, validRelationCode code := by
  decide

private theorem cover61_48_00 : ∀ q : IncreasingTwo 9,
    coveredNat 61 codes61_48_00 (blockValues 50 51 q) = true := by
  decide

private def codes61_48_01 : List ℕ := [17, 642, 85, 521, 402, 589, 89]

private theorem valid61_48_01 : ∀ code ∈ codes61_48_01, validRelationCode code := by
  decide

private theorem cover61_48_01 : ∀ q : IncreasingTwo 8,
    coveredNat 61 codes61_48_01 (blockValues 50 52 q) = true := by
  decide

private def codes61_48_02 : List ℕ := [17, 521, 261, 403, 402, 772]

private theorem valid61_48_02 : ∀ code ∈ codes61_48_02, validRelationCode code := by
  decide

private theorem cover61_48_02 : ∀ q : IncreasingTwo 7,
    coveredNat 61 codes61_48_02 (blockValues 50 53 q) = true := by
  decide

private def codes61_48_03 : List ℕ := [17, 521, 261, 77, 386]

private theorem valid61_48_03 : ∀ code ∈ codes61_48_03, validRelationCode code := by
  decide

private theorem cover61_48_03 : ∀ q : IncreasingTwo 6,
    coveredNat 61 codes61_48_03 (blockValues 50 54 q) = true := by
  decide

private def codes61_48_04 : List ℕ := [386, 17, 521, 772]

private theorem valid61_48_04 : ∀ code ∈ codes61_48_04, validRelationCode code := by
  decide

private theorem cover61_48_04 : ∀ q : IncreasingTwo 5,
    coveredNat 61 codes61_48_04 (blockValues 50 55 q) = true := by
  decide

private def codes61_48_05 : List ℕ := [1506]

private theorem valid61_48_05 : ∀ code ∈ codes61_48_05, validRelationCode code := by
  decide

private theorem cover61_48_05 : ∀ q : IncreasingTwo 4,
    coveredNat 61 codes61_48_05 (blockValues 50 56 q) = true := by
  decide

private def codes61_48_06 : List ℕ := [17, 153]

private theorem valid61_48_06 : ∀ code ∈ codes61_48_06, validRelationCode code := by
  decide

private theorem cover61_48_06 : ∀ q : IncreasingTwo 3,
    coveredNat 61 codes61_48_06 (blockValues 50 57 q) = true := by
  decide

private def codes61_48_07 : List ℕ := [772]

private theorem valid61_48_07 : ∀ code ∈ codes61_48_07, validRelationCode code := by
  decide

private theorem cover61_48_07 : ∀ q : IncreasingTwo 2,
    coveredNat 61 codes61_48_07 (blockValues 50 58 q) = true := by
  decide

theorem certificate61_a48
    (q : IncreasingFourTail 59 (⟨48, by norm_num⟩ : Fin 56)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 61 (increasingFourValues (N := 61) ⟨⟨48, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_00 _ valid61_48_00 (cover61_48_00 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_01 _ valid61_48_01 (cover61_48_01 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_02 _ valid61_48_02 (cover61_48_02 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_03 _ valid61_48_03 (cover61_48_03 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_04 _ valid61_48_04 (cover61_48_04 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_05 _ valid61_48_05 (cover61_48_05 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_06 _ valid61_48_06 (cover61_48_06 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_48_07 _ valid61_48_07 (cover61_48_07 q')

end MinModulus.SHCFiveCertificate.Generated
