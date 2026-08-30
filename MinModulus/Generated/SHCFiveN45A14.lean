import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_14 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4265, 278, 279, 589, 403, 153, 773, 4884, 4227, 2624, 209, 2626, 642, 2468, 2308, 643, 4232, 2786, 321, 2631, 85, 4387, 2064, 2305, 518, 4234, 1984, 3904, 519, 193, 1546, 1665, 1527, 10, 262, 201, 577, 5184, 19, 5504, 4876, 217, 1668, 28, 770, 18, 522, 6, 14]

private theorem valid45_14 : ∀ code ∈ codes45_14, validRelationCode code := by
  decide

private theorem cover45_14 : ∀ q : IncreasingFourTail 43 (⟨14, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_14 (increasingFourValues (N := 45) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a14
    (q : IncreasingFourTail 43 (⟨14, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_14 _ valid45_14 (cover45_14 q)

end MinModulus.SHCFiveCertificate.Generated
