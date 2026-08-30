import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_17 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 465, 2476, 773, 2468, 4544, 3906, 643, 403, 2786, 772, 85, 2465, 386, 705, 4885, 4387]

private theorem valid41_17 : ∀ code ∈ codes41_17, validRelationCode code := by
  decide

private theorem cover41_17 : ∀ q : IncreasingFourTail 39 (⟨17, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_17 (increasingFourValues (N := 41) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a17
    (q : IncreasingFourTail 39 (⟨17, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_17 _ valid41_17 (cover41_17 q)

end MinModulus.SHCFiveCertificate.Generated
