import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_23 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 85, 643, 772, 2626, 402, 153, 773, 2308, 2786, 2631, 589, 2468, 4232, 4234, 403, 4884, 4387, 1347, 770, 705, 899, 387]

private theorem valid45_23 : ∀ code ∈ codes45_23, validRelationCode code := by
  decide

private theorem cover45_23 : ∀ q : IncreasingFourTail 43 (⟨23, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_23 (increasingFourValues (N := 45) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a23
    (q : IncreasingFourTail 43 (⟨23, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_23 _ valid45_23 (cover45_23 q)

end MinModulus.SHCFiveCertificate.Generated
