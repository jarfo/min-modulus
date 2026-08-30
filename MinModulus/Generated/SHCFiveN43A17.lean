import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_17 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 4227, 772, 2308, 1865, 2545, 773, 2468, 1347, 402, 642, 2626, 85, 589, 2631, 4387, 2954, 3757, 833, 5036, 4232, 153, 2305, 4876, 3268, 465, 321, 1548, 770, 14, 705]

private theorem valid43_17 : ∀ code ∈ codes43_17, validRelationCode code := by
  decide

private theorem cover43_17 : ∀ q : IncreasingFourTail 41 (⟨17, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_17 (increasingFourValues (N := 43) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a17
    (q : IncreasingFourTail 41 (⟨17, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_17 _ valid43_17 (cover43_17 q)

end MinModulus.SHCFiveCertificate.Generated
