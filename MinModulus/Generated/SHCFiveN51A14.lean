import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_14 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 1186, 642, 2626, 4227, 2308, 4232, 2468, 643, 2786, 2631, 4387, 85, 11, 4234, 2624, 10, 321, 518, 2305, 209, 519, 1905, 2064, 2465, 1187, 1528, 193, 1546, 1988, 5025, 12, 3745, 3586, 5184, 3585, 5504, 387, 1984, 4876, 89, 385, 771, 28, 262, 770, 6, 337, 897, 3746, 1548, 386, 3268, 1993, 837, 5204, 2148, 2954, 4066, 5036, 465, 527, 1825, 2545, 5505, 4885, 2466, 2546, 1527, 3907, 4552, 29, 523, 27, 2944]

private theorem valid51_14 : ∀ code ∈ codes51_14, validRelationCode code := by
  decide

private theorem cover51_14 : ∀ q : IncreasingFourTail 49 (⟨14, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_14 (increasingFourValues (N := 51) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a14
    (q : IncreasingFourTail 49 (⟨14, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_14 _ valid51_14 (cover51_14 q)

end MinModulus.SHCFiveCertificate.Generated
