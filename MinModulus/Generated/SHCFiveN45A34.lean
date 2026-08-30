import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_34 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid45_34 : ∀ code ∈ codes45_34, validRelationCode code := by
  decide

private theorem cover45_34 : ∀ q : IncreasingFourTail 43 (⟨34, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_34 (increasingFourValues (N := 45) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a34
    (q : IncreasingFourTail 43 (⟨34, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_34 _ valid45_34 (cover45_34 q)

end MinModulus.SHCFiveCertificate.Generated
