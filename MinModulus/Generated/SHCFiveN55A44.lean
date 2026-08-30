import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes55_44_00 : List ℕ := [131]

private theorem valid55_44_00 : ∀ code ∈ codes55_44_00, validRelationCode code := by
  decide

private theorem cover55_44_00 : ∀ q : IncreasingTwo 7,
    coveredNat 55 codes55_44_00 (blockValues 46 47 q) = true := by
  decide

private def codes55_44_01 : List ℕ := [17, 642, 85, 521, 402]

private theorem valid55_44_01 : ∀ code ∈ codes55_44_01, validRelationCode code := by
  decide

private theorem cover55_44_01 : ∀ q : IncreasingTwo 6,
    coveredNat 55 codes55_44_01 (blockValues 46 48 q) = true := by
  decide

private def codes55_44_02 : List ℕ := [17, 521, 261, 772]

private theorem valid55_44_02 : ∀ code ∈ codes55_44_02, validRelationCode code := by
  decide

private theorem cover55_44_02 : ∀ q : IncreasingTwo 5,
    coveredNat 55 codes55_44_02 (blockValues 46 49 q) = true := by
  decide

private def codes55_44_03 : List ℕ := [386, 17, 772]

private theorem valid55_44_03 : ∀ code ∈ codes55_44_03, validRelationCode code := by
  decide

private theorem cover55_44_03 : ∀ q : IncreasingTwo 4,
    coveredNat 55 codes55_44_03 (blockValues 46 50 q) = true := by
  decide

private def codes55_44_04 : List ℕ := [1506]

private theorem valid55_44_04 : ∀ code ∈ codes55_44_04, validRelationCode code := by
  decide

private theorem cover55_44_04 : ∀ q : IncreasingTwo 3,
    coveredNat 55 codes55_44_04 (blockValues 46 51 q) = true := by
  decide

private def codes55_44_05 : List ℕ := [772]

private theorem valid55_44_05 : ∀ code ∈ codes55_44_05, validRelationCode code := by
  decide

private theorem cover55_44_05 : ∀ q : IncreasingTwo 2,
    coveredNat 55 codes55_44_05 (blockValues 46 52 q) = true := by
  decide

theorem certificate55_a44
    (q : IncreasingFourTail 53 (⟨44, by norm_num⟩ : Fin 50)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 55 (increasingFourValues (N := 55) ⟨⟨44, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_00 _ valid55_44_00 (cover55_44_00 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_01 _ valid55_44_01 (cover55_44_01 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_02 _ valid55_44_02 (cover55_44_02 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_03 _ valid55_44_03 (cover55_44_03 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_04 _ valid55_44_04 (cover55_44_04 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 55 codes55_44_05 _ valid55_44_05 (cover55_44_05 q')

end MinModulus.SHCFiveCertificate.Generated
