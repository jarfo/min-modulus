import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_09 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 772, 4227, 2308, 201, 337, 577, 153, 773, 402, 4387, 4232, 642, 2468, 2626, 2786, 1825, 643, 403, 1665, 4234, 522, 262, 2631, 589, 4884, 85, 18, 209, 4425, 523, 263, 1186, 713, 321, 1905, 4265, 2465, 10, 19, 2624, 2305, 518, 4584, 278, 385, 1187, 4547, 519, 4237, 524, 770, 387, 3025, 12, 3907, 386, 11, 2954, 24, 30, 899]

private theorem valid45_09 : ∀ code ∈ codes45_09, validRelationCode code := by
  decide

private theorem cover45_09 : ∀ q : IncreasingFourTail 43 (⟨9, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_09 (increasingFourValues (N := 45) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a09
    (q : IncreasingFourTail 43 (⟨9, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_09 _ valid45_09 (cover45_09 q)

end MinModulus.SHCFiveCertificate.Generated
