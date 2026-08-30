import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes59_50_00 : List ℕ := [131]

private theorem valid59_50_00 : ∀ code ∈ codes59_50_00, validRelationCode code := by
  decide

private theorem cover59_50_00 : ∀ q : IncreasingTwo 5,
    coveredNat 59 codes59_50_00 (blockValues 52 53 q) = true := by
  decide

private def codes59_50_01 : List ℕ := [17, 642, 770]

private theorem valid59_50_01 : ∀ code ∈ codes59_50_01, validRelationCode code := by
  decide

private theorem cover59_50_01 : ∀ q : IncreasingTwo 4,
    coveredNat 59 codes59_50_01 (blockValues 52 54 q) = true := by
  decide

private def codes59_50_02 : List ℕ := [386, 898]

private theorem valid59_50_02 : ∀ code ∈ codes59_50_02, validRelationCode code := by
  decide

private theorem cover59_50_02 : ∀ q : IncreasingTwo 3,
    coveredNat 59 codes59_50_02 (blockValues 52 55 q) = true := by
  decide

private def codes59_50_03 : List ℕ := [772]

private theorem valid59_50_03 : ∀ code ∈ codes59_50_03, validRelationCode code := by
  decide

private theorem cover59_50_03 : ∀ q : IncreasingTwo 2,
    coveredNat 59 codes59_50_03 (blockValues 52 56 q) = true := by
  decide

theorem certificate59_a50
    (q : IncreasingFourTail 57 (⟨50, by norm_num⟩ : Fin 54)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 59 (increasingFourValues (N := 59) ⟨⟨50, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_50_00 _ valid59_50_00 (cover59_50_00 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_50_01 _ valid59_50_01 (cover59_50_01 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_50_02 _ valid59_50_02 (cover59_50_02 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_50_03 _ valid59_50_03 (cover59_50_03 q')

end MinModulus.SHCFiveCertificate.Generated
