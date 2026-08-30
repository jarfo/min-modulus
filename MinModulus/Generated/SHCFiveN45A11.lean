import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_11 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 278, 4265, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 85, 2631, 643, 4227, 2308, 2786, 518, 2465, 10, 1905, 2305, 209, 321, 2624, 4387, 2468, 4232, 519, 4234, 385, 2064, 1347, 2546, 386, 1837, 770, 262, 522, 3746, 2148, 27, 3745, 401, 263, 2466, 3586, 12, 337, 3585, 193, 524, 577, 1865, 3907, 18, 774, 526, 13, 387]

private theorem valid45_11 : ∀ code ∈ codes45_11, validRelationCode code := by
  decide

private theorem cover45_11 : ∀ q : IncreasingFourTail 43 (⟨11, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_11 (increasingFourValues (N := 45) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a11
    (q : IncreasingFourTail 43 (⟨11, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_11 _ valid45_11 (cover45_11 q)

end MinModulus.SHCFiveCertificate.Generated
