import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 3785, 2485, 524, 403, 2786, 2306, 643, 20, 3765, 85, 209, 589, 2631, 713, 321, 4547, 4237, 4234, 774, 2466, 401, 775, 2148, 4224, 2788, 2628, 641, 4544, 5025, 4225, 3118, 155, 2305, 3746, 153, 2546, 154, 3025, 4265, 2808, 770, 5504, 4884, 3185, 28, 386, 769]

private theorem valid43_04 : ∀ code ∈ codes43_04, validRelationCode code := by
  decide

private theorem cover43_04 : ∀ q : IncreasingFourTail 41 (⟨4, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_04 (increasingFourValues (N := 43) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a04
    (q : IncreasingFourTail 41 (⟨4, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_04 _ valid43_04 (cover43_04 q)

end MinModulus.SHCFiveCertificate.Generated
