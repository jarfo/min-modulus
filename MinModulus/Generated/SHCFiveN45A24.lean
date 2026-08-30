import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_24 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 89, 2866, 5191, 898, 387]

private theorem valid45_24 : ∀ code ∈ codes45_24, validRelationCode code := by
  decide

private theorem cover45_24 : ∀ q : IncreasingFourTail 43 (⟨24, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_24 (increasingFourValues (N := 45) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a24
    (q : IncreasingFourTail 43 (⟨24, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_24 _ valid45_24 (cover45_24 q)

end MinModulus.SHCFiveCertificate.Generated
