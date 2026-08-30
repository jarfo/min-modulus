import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_38 : List ℕ := [17, 402]

private theorem valid45_38 : ∀ code ∈ codes45_38, validRelationCode code := by
  decide

private theorem cover45_38 : ∀ q : IncreasingFourTail 43 (⟨38, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_38 (increasingFourValues (N := 45) ⟨⟨38, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a38
    (q : IncreasingFourTail 43 (⟨38, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨38, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_38 _ valid45_38 (cover45_38 q)

end MinModulus.SHCFiveCertificate.Generated
