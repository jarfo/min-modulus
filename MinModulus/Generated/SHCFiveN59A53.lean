import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes59_53_00 : List ℕ := [772]

private theorem valid59_53_00 : ∀ code ∈ codes59_53_00, validRelationCode code := by
  decide

private theorem cover59_53_00 : ∀ q : IncreasingTwo 2,
    coveredNat 59 codes59_53_00 (blockValues 55 56 q) = true := by
  decide

theorem certificate59_a53
    (q : IncreasingFourTail 57 (⟨53, by norm_num⟩ : Fin 54)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 59 (increasingFourValues (N := 59) ⟨⟨53, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 59 codes59_53_00 _ valid59_53_00 (cover59_53_00 q')

end MinModulus.SHCFiveCertificate.Generated
