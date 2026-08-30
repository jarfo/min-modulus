import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes55_38_00 : List ℕ := [131]

private theorem valid55_38_00 : ∀ code ∈ codes55_38_00, validRelationCode code := by
  decide

private theorem cover55_38_00 : ∀ q : IncreasingTwo 13,
    coveredNat 55 codes55_38_00 (blockValues 40 41 q) = true := by
  decide

private def codes55_38_01 : List ℕ := [17, 642, 85, 521, 402, 589, 261, 2626, 2631, 772, 153, 773]

private theorem valid55_38_01 : ∀ code ∈ codes55_38_01, validRelationCode code := by
  decide

private theorem cover55_38_01 : ∀ q : IncreasingTwo 12,
    coveredNat 55 codes55_38_01 (blockValues 40 42 q) = true := by
  decide

private def codes55_38_02 : List ℕ := [17, 521, 261, 403, 402, 589, 643, 642, 85, 770]

private theorem valid55_38_02 : ∀ code ∈ codes55_38_02, validRelationCode code := by
  decide

private theorem cover55_38_02 : ∀ q : IncreasingTwo 11,
    coveredNat 55 codes55_38_02 (blockValues 40 43 q) = true := by
  decide

private def codes55_38_03 : List ℕ := [17, 521, 261, 4234, 643, 642, 85, 3911, 89]

private theorem valid55_38_03 : ∀ code ∈ codes55_38_03, validRelationCode code := by
  decide

private theorem cover55_38_03 : ∀ q : IncreasingTwo 10,
    coveredNat 55 codes55_38_03 (blockValues 40 44 q) = true := by
  decide

private def codes55_38_04 : List ℕ := [17, 521, 261, 1528, 4234, 643, 642, 85]

private theorem valid55_38_04 : ∀ code ∈ codes55_38_04, validRelationCode code := by
  decide

private theorem cover55_38_04 : ∀ q : IncreasingTwo 9,
    coveredNat 55 codes55_38_04 (blockValues 40 45 q) = true := by
  decide

private def codes55_38_05 : List ℕ := [17, 521, 261, 77, 386, 387, 898]

private theorem valid55_38_05 : ∀ code ∈ codes55_38_05, validRelationCode code := by
  decide

private theorem cover55_38_05 : ∀ q : IncreasingTwo 8,
    coveredNat 55 codes55_38_05 (blockValues 40 46 q) = true := by
  decide

private def codes55_38_06 : List ℕ := [386, 17, 521, 387, 2954, 899]

private theorem valid55_38_06 : ∀ code ∈ codes55_38_06, validRelationCode code := by
  decide

private theorem cover55_38_06 : ∀ q : IncreasingTwo 7,
    coveredNat 55 codes55_38_06 (blockValues 40 47 q) = true := by
  decide

private def codes55_38_07 : List ℕ := [1506]

private theorem valid55_38_07 : ∀ code ∈ codes55_38_07, validRelationCode code := by
  decide

private theorem cover55_38_07 : ∀ q : IncreasingTwo 6,
    coveredNat 55 codes55_38_07 (blockValues 40 48 q) = true := by
  decide

private def codes55_38_08 : List ℕ := [17, 521, 261, 772]

private theorem valid55_38_08 : ∀ code ∈ codes55_38_08, validRelationCode code := by
  decide

private theorem cover55_38_08 : ∀ q : IncreasingTwo 5,
    coveredNat 55 codes55_38_08 (blockValues 40 49 q) = true := by
  decide

private def codes55_38_09 : List ℕ := [17, 521, 153]

private theorem valid55_38_09 : ∀ code ∈ codes55_38_09, validRelationCode code := by
  decide

private theorem cover55_38_09 : ∀ q : IncreasingTwo 4,
    coveredNat 55 codes55_38_09 (blockValues 40 50 q) = true := by
  decide

private def codes55_38_10 : List ℕ := [17, 153]

private theorem valid55_38_10 : ∀ code ∈ codes55_38_10, validRelationCode code := by
  decide

private theorem cover55_38_10 : ∀ q : IncreasingTwo 3,
    coveredNat 55 codes55_38_10 (blockValues 40 51 q) = true := by
  decide

private def codes55_38_11 : List ℕ := [772]

private theorem valid55_38_11 : ∀ code ∈ codes55_38_11, validRelationCode code := by
  decide

private theorem cover55_38_11 : ∀ q : IncreasingTwo 2,
    coveredNat 55 codes55_38_11 (blockValues 40 52 q) = true := by
  decide

theorem certificate55_a38
    (q : IncreasingFourTail 53 (⟨38, by norm_num⟩ : Fin 50)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 55 (increasingFourValues (N := 55) ⟨⟨38, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (13 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 13 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_00 _ valid55_38_00 (cover55_38_00 q')
  · let c' : Fin (12 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 12 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_01 _ valid55_38_01 (cover55_38_01 q')
  · let c' : Fin (11 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 11 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_02 _ valid55_38_02 (cover55_38_02 q')
  · let c' : Fin (10 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 10 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_03 _ valid55_38_03 (cover55_38_03 q')
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_04 _ valid55_38_04 (cover55_38_04 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_05 _ valid55_38_05 (cover55_38_05 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_06 _ valid55_38_06 (cover55_38_06 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_07 _ valid55_38_07 (cover55_38_07 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_08 _ valid55_38_08 (cover55_38_08 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_09 _ valid55_38_09 (cover55_38_09 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_10 _ valid55_38_10 (cover55_38_10 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_38_11 _ valid55_38_11 (cover55_38_11 q')

end MinModulus.SHCFiveCertificate.Generated
