import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_33 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid45_33 : ∀ code ∈ codes45_33, validRelationCode code := by
  decide

private theorem cover45_33 : ∀ q : IncreasingFourTail 43 (⟨33, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_33 (increasingFourValues (N := 45) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a33
    (q : IncreasingFourTail 43 (⟨33, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_33 _ valid45_33 (cover45_33 q)

end MinModulus.SHCFiveCertificate.Generated
