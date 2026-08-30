import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_22 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 4227, 589, 773, 2631, 2468, 772, 402, 465, 4884, 85, 643, 4387, 4232, 2476, 2626, 2308, 705, 153, 898, 386, 30, 899]

private theorem valid45_22 : ∀ code ∈ codes45_22, validRelationCode code := by
  decide

private theorem cover45_22 : ∀ q : IncreasingFourTail 43 (⟨22, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_22 (increasingFourValues (N := 45) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a22
    (q : IncreasingFourTail 43 (⟨22, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_22 _ valid45_22 (cover45_22 q)

end MinModulus.SHCFiveCertificate.Generated
