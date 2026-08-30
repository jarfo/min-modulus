import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_20 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 4227, 772, 2308, 3745, 642, 402, 2545, 2468, 1865, 2626, 773, 589, 2631, 85, 4387, 4232, 643, 153, 4884, 2786, 403, 1507, 5025, 321, 209, 2305, 10, 518, 713, 2476, 2624, 1827, 465, 385, 386, 278, 387, 4544, 833, 4584, 2866, 1828, 1668, 526, 705, 3344, 5504, 770, 22, 14, 279]

private theorem valid51_20 : ∀ code ∈ codes51_20, validRelationCode code := by
  decide

private theorem cover51_20 : ∀ q : IncreasingFourTail 49 (⟨20, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_20 (increasingFourValues (N := 51) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a20
    (q : IncreasingFourTail 49 (⟨20, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_20 _ valid51_20 (cover51_20 q)

end MinModulus.SHCFiveCertificate.Generated
