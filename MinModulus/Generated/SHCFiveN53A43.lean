import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_43 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid53_43 : ∀ code ∈ codes53_43, validRelationCode code := by
  decide

private theorem cover53_43 : ∀ q : IncreasingFourTail 51 (⟨43, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_43 (increasingFourValues (N := 53) ⟨⟨43, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a43
    (q : IncreasingFourTail 51 (⟨43, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨43, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_43 _ valid53_43 (cover53_43 q)

end MinModulus.SHCFiveCertificate.Generated
