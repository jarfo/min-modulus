import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_19 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 526, 22, 2786, 4227, 2308, 402, 642, 153, 4232, 1347, 386, 2626, 2476, 4884, 705, 93, 465]

private theorem valid43_19 : ∀ code ∈ codes43_19, validRelationCode code := by
  decide

private theorem cover43_19 : ∀ q : IncreasingFourTail 41 (⟨19, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_19 (increasingFourValues (N := 43) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a19
    (q : IncreasingFourTail 41 (⟨19, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_19 _ valid43_19 (cover43_19 q)

end MinModulus.SHCFiveCertificate.Generated
