import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_37 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid49_37 : ∀ code ∈ codes49_37, validRelationCode code := by
  decide

private theorem cover49_37 : ∀ q : IncreasingFourTail 47 (⟨37, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_37 (increasingFourValues (N := 49) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a37
    (q : IncreasingFourTail 47 (⟨37, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_37 _ valid49_37 (cover49_37 q)

end MinModulus.SHCFiveCertificate.Generated
