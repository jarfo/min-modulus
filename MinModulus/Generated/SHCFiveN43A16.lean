import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_16 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 402, 642, 2626, 3585, 773, 2468, 10, 278, 518, 4387, 4232, 153, 643, 385, 403, 4884, 85, 589, 2631, 1865, 2545, 833, 5025, 3745, 1868, 1668, 519, 4544, 770, 705, 321, 1667, 279]

private theorem valid43_16 : ∀ code ∈ codes43_16, validRelationCode code := by
  decide

private theorem cover43_16 : ∀ q : IncreasingFourTail 41 (⟨16, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_16 (increasingFourValues (N := 43) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a16
    (q : IncreasingFourTail 41 (⟨16, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_16 _ valid43_16 (cover43_16 q)

end MinModulus.SHCFiveCertificate.Generated
