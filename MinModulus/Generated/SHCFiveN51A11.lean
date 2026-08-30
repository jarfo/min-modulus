import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_11 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 1347, 402, 4227, 2308, 85, 589, 2631, 773, 4387, 153, 403, 2786, 643, 4232, 2468, 4884, 4234, 3904, 2024, 2704, 201, 1825, 337, 577, 209, 4425, 321, 713, 262, 1905, 522, 2465, 4265, 1665, 3765, 10, 2305, 518, 18, 2624, 278, 4584, 263, 2064, 523, 19, 519, 12, 11, 27, 770, 5025, 3586, 3907, 3906, 524, 4066, 2958, 387, 386, 3786, 3757, 3927, 3273, 774, 3746, 30, 449, 193, 4547, 20, 89, 401, 771, 4385, 3745, 2485, 3585, 28, 526, 833, 29, 155, 4225]

private theorem valid51_11 : ∀ code ∈ codes51_11, validRelationCode code := by
  decide

private theorem cover51_11 : ∀ q : IncreasingFourTail 49 (⟨11, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_11 (increasingFourValues (N := 51) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a11
    (q : IncreasingFourTail 49 (⟨11, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_11 _ valid51_11 (cover51_11 q)

end MinModulus.SHCFiveCertificate.Generated
