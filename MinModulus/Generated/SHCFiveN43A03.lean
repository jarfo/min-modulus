import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 642, 402, 2626, 643, 403, 2786, 21, 85, 4385, 770, 2648, 641, 4224, 4225, 705, 774, 2628, 385, 4544, 2546, 386, 3344, 3185, 3765, 154, 401, 525, 1186, 2788, 465, 3907, 4707, 526, 589, 3586, 3786, 2631, 1827, 773, 13, 387, 775, 3757, 22, 833, 899, 4884, 2954]

private theorem valid43_03 : ∀ code ∈ codes43_03, validRelationCode code := by
  decide

private theorem cover43_03 : ∀ q : IncreasingFourTail 41 (⟨3, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_03 (increasingFourValues (N := 43) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a03
    (q : IncreasingFourTail 41 (⟨3, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_03 _ valid43_03 (cover43_03 q)

end MinModulus.SHCFiveCertificate.Generated
