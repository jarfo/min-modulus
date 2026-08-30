import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_18 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 22, 2786, 526, 4227, 2308, 402, 642, 2626, 465, 705, 2476, 386, 14, 449]

private theorem valid41_18 : ∀ code ∈ codes41_18, validRelationCode code := by
  decide

private theorem cover41_18 : ∀ q : IncreasingFourTail 39 (⟨18, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_18 (increasingFourValues (N := 41) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a18
    (q : IncreasingFourTail 39 (⟨18, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_18 _ valid41_18 (cover41_18 q)

end MinModulus.SHCFiveCertificate.Generated
