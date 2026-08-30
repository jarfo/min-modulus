import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes57_48_00 : List ℕ := [131]

private theorem valid57_48_00 : ∀ code ∈ codes57_48_00, validRelationCode code := by
  decide

private theorem cover57_48_00 : ∀ q : IncreasingTwo 5,
    coveredNat 57 codes57_48_00 (blockValues 50 51 q) = true := by
  decide

private def codes57_48_01 : List ℕ := [17, 642, 770]

private theorem valid57_48_01 : ∀ code ∈ codes57_48_01, validRelationCode code := by
  decide

private theorem cover57_48_01 : ∀ q : IncreasingTwo 4,
    coveredNat 57 codes57_48_01 (blockValues 50 52 q) = true := by
  decide

private def codes57_48_02 : List ℕ := [386, 898]

private theorem valid57_48_02 : ∀ code ∈ codes57_48_02, validRelationCode code := by
  decide

private theorem cover57_48_02 : ∀ q : IncreasingTwo 3,
    coveredNat 57 codes57_48_02 (blockValues 50 53 q) = true := by
  decide

private def codes57_48_03 : List ℕ := [772]

private theorem valid57_48_03 : ∀ code ∈ codes57_48_03, validRelationCode code := by
  decide

private theorem cover57_48_03 : ∀ q : IncreasingTwo 2,
    coveredNat 57 codes57_48_03 (blockValues 50 54 q) = true := by
  decide

theorem certificate57_a48
    (q : IncreasingFourTail 55 (⟨48, by norm_num⟩ : Fin 52)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 57 (increasingFourValues (N := 57) ⟨⟨48, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_48_00 _ valid57_48_00 (cover57_48_00 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_48_01 _ valid57_48_01 (cover57_48_01 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_48_02 _ valid57_48_02 (cover57_48_02 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 57 codes57_48_03 _ valid57_48_03 (cover57_48_03 q')

end MinModulus.SHCFiveCertificate.Generated
