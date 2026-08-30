import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2628, 774, 643, 402, 2626, 4552, 4237, 2786, 837, 465, 2788, 2476, 2478, 21, 4234, 12, 770, 775, 23, 5045, 4230, 26, 833, 29]

private theorem valid45_01 : ∀ code ∈ codes45_01, validRelationCode code := by
  decide

private theorem cover45_01 : ∀ q : IncreasingFourTail 43 (⟨1, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_01 (increasingFourValues (N := 45) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a01
    (q : IncreasingFourTail 43 (⟨1, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_01 _ valid45_01 (cover45_01 q)

end MinModulus.SHCFiveCertificate.Generated
