import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_47 : List ℕ := [772]

private theorem valid53_47 : ∀ code ∈ codes53_47, validRelationCode code := by
  decide

private theorem cover53_47 : ∀ q : IncreasingFourTail 51 (⟨47, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_47 (increasingFourValues (N := 53) ⟨⟨47, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a47
    (q : IncreasingFourTail 51 (⟨47, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨47, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_47 _ valid53_47 (cover53_47 q)

end MinModulus.SHCFiveCertificate.Generated
