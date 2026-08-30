import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid45_30 : ∀ code ∈ codes45_30, validRelationCode code := by
  decide

private theorem cover45_30 : ∀ q : IncreasingFourTail 43 (⟨30, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_30 (increasingFourValues (N := 45) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a30
    (q : IncreasingFourTail 43 (⟨30, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_30 _ valid45_30 (cover45_30 q)

end MinModulus.SHCFiveCertificate.Generated
