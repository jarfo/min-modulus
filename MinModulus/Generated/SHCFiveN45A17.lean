import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_17 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 153, 773, 4387, 4232, 2468, 402, 642, 2626, 1865, 2545, 3585, 3745, 2631, 85, 589, 643, 4884, 2786, 403, 5184, 5025, 4876, 279, 3907, 899, 385, 519, 4234, 898, 321, 4544, 770, 10, 518, 705, 713]

private theorem valid45_17 : ∀ code ∈ codes45_17, validRelationCode code := by
  decide

private theorem cover45_17 : ∀ q : IncreasingFourTail 43 (⟨17, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_17 (increasingFourValues (N := 45) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a17
    (q : IncreasingFourTail 43 (⟨17, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_17 _ valid45_17 (cover45_17 q)

end MinModulus.SHCFiveCertificate.Generated
