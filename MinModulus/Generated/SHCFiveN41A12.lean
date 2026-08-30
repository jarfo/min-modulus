import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_12 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 4584, 279, 589, 403, 153, 773, 4884, 2546, 518, 2308, 321, 642, 2626, 4232, 4387, 4227, 2631, 85, 643, 2468, 10, 2786, 209, 2624, 519, 2064, 4234, 193, 26, 262, 89, 18, 19, 770, 1984, 28, 6, 386, 522, 22, 337]

private theorem valid41_12 : ∀ code ∈ codes41_12, validRelationCode code := by
  decide

private theorem cover41_12 : ∀ q : IncreasingFourTail 39 (⟨12, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_12 (increasingFourValues (N := 41) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a12
    (q : IncreasingFourTail 39 (⟨12, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_12 _ valid41_12 (cover41_12 q)

end MinModulus.SHCFiveCertificate.Generated
