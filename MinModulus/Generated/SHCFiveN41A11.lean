import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_11 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 4584, 402, 279, 713, 4425, 589, 403, 153, 773, 4884, 1186, 642, 2626, 4227, 2308, 85, 2631, 4387, 643, 4232, 2468, 11, 519, 2786, 10, 4234, 321, 18, 2624, 209, 1905, 27, 3745, 2305, 3585, 518, 2465, 3586, 193, 93, 1988, 770, 522, 1865, 1827, 28]

private theorem valid41_11 : ∀ code ∈ codes41_11, validRelationCode code := by
  decide

private theorem cover41_11 : ∀ q : IncreasingFourTail 39 (⟨11, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_11 (increasingFourValues (N := 41) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a11
    (q : IncreasingFourTail 39 (⟨11, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_11 _ valid41_11 (cover41_11 q)

end MinModulus.SHCFiveCertificate.Generated
