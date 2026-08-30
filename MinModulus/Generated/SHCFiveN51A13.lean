import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_13 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 402, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 642, 2626, 85, 643, 2631, 4227, 2308, 2786, 2465, 1905, 518, 2468, 209, 321, 2305, 10, 2624, 4387, 4232, 519, 2064, 4234, 1186, 1347, 3586, 385, 2546, 3746, 2944, 833, 12, 193, 3907, 770, 1865, 89, 3585, 263, 3745, 387, 3757, 522, 1527, 1837, 386, 262, 201, 337, 401, 771, 1827, 1528, 1187, 524, 769, 775, 5504, 5505, 2148, 2808, 6, 5510, 3912, 961, 577, 641, 3273, 898, 526, 897, 525, 29, 523]

private theorem valid51_13 : ∀ code ∈ codes51_13, validRelationCode code := by
  decide

private theorem cover51_13 : ∀ q : IncreasingFourTail 49 (⟨13, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_13 (increasingFourValues (N := 51) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a13
    (q : IncreasingFourTail 49 (⟨13, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_13 _ valid51_13 (cover51_13 q)

end MinModulus.SHCFiveCertificate.Generated
