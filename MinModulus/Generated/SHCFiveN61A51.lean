import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes61_51_00 : List ℕ := [131]

private theorem valid61_51_00 : ∀ code ∈ codes61_51_00, validRelationCode code := by
  decide

private theorem cover61_51_00 : ∀ q : IncreasingTwo 6,
    coveredNat 61 codes61_51_00 (blockValues 53 54 q) = true := by
  decide

private def codes61_51_01 : List ℕ := [17, 642, 85, 89]

private theorem valid61_51_01 : ∀ code ∈ codes61_51_01, validRelationCode code := by
  decide

private theorem cover61_51_01 : ∀ q : IncreasingTwo 5,
    coveredNat 61 codes61_51_01 (blockValues 53 55 q) = true := by
  decide

private def codes61_51_02 : List ℕ := [77, 386, 898]

private theorem valid61_51_02 : ∀ code ∈ codes61_51_02, validRelationCode code := by
  decide

private theorem cover61_51_02 : ∀ q : IncreasingTwo 4,
    coveredNat 61 codes61_51_02 (blockValues 53 56 q) = true := by
  decide

private def codes61_51_03 : List ℕ := [1346]

private theorem valid61_51_03 : ∀ code ∈ codes61_51_03, validRelationCode code := by
  decide

private theorem cover61_51_03 : ∀ q : IncreasingTwo 3,
    coveredNat 61 codes61_51_03 (blockValues 53 57 q) = true := by
  decide

private def codes61_51_04 : List ℕ := [772]

private theorem valid61_51_04 : ∀ code ∈ codes61_51_04, validRelationCode code := by
  decide

private theorem cover61_51_04 : ∀ q : IncreasingTwo 2,
    coveredNat 61 codes61_51_04 (blockValues 53 58 q) = true := by
  decide

theorem certificate61_a51
    (q : IncreasingFourTail 59 (⟨51, by norm_num⟩ : Fin 56)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 61 (increasingFourValues (N := 61) ⟨⟨51, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_51_00 _ valid61_51_00 (cover61_51_00 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_51_01 _ valid61_51_01 (cover61_51_01 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_51_02 _ valid61_51_02 (cover61_51_02 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_51_03 _ valid61_51_03 (cover61_51_03 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_51_04 _ valid61_51_04 (cover61_51_04 q')

end MinModulus.SHCFiveCertificate.Generated
