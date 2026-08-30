import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_10 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 4884, 4234, 2704, 2024, 3904, 1507, 4265, 321, 11, 201, 1825, 2305, 209, 518, 713, 2624, 337, 1905, 4425, 10, 2465, 4584, 577, 278, 2064, 3765, 522, 3746, 262, 1665, 3586, 2944, 1988, 387, 774, 401, 4224, 3585, 2546, 519, 770, 193, 385, 2954, 4870, 28, 386, 4874]

private theorem valid45_10 : ∀ code ∈ codes45_10, validRelationCode code := by
  decide

private theorem cover45_10 : ∀ q : IncreasingFourTail 43 (⟨10, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_10 (increasingFourValues (N := 45) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a10
    (q : IncreasingFourTail 43 (⟨10, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_10 _ valid45_10 (cover45_10 q)

end MinModulus.SHCFiveCertificate.Generated
