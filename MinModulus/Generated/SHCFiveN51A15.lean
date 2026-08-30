import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 278, 4584, 402, 713, 589, 403, 279, 4884, 153, 773, 10, 518, 4227, 2308, 642, 2626, 2786, 643, 2631, 321, 2468, 4387, 4232, 519, 209, 85, 11, 4234, 2624, 18, 193, 19, 262, 263, 6, 1984, 577, 523, 3757, 522, 2148, 3586, 3746, 1993, 2064, 5036, 3273, 13, 5191, 3268, 833, 897, 2546, 4876, 154, 27, 1546, 12, 386, 26, 31, 1827, 1837, 1868, 2478, 770, 705, 201, 401, 641, 387, 23, 2808, 20, 774, 899, 3906, 1187]

private theorem valid51_15 : ∀ code ∈ codes51_15, validRelationCode code := by
  decide

private theorem cover51_15 : ∀ q : IncreasingFourTail 49 (⟨15, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_15 (increasingFourValues (N := 51) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a15
    (q : IncreasingFourTail 49 (⟨15, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_15 _ valid51_15 (cover51_15 q)

end MinModulus.SHCFiveCertificate.Generated
