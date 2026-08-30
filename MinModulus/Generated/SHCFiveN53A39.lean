import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_39 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid53_39 : ∀ code ∈ codes53_39, validRelationCode code := by
  decide

private theorem cover53_39 : ∀ q : IncreasingFourTail 51 (⟨39, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_39 (increasingFourValues (N := 53) ⟨⟨39, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a39
    (q : IncreasingFourTail 51 (⟨39, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨39, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_39 _ valid53_39 (cover53_39 q)

end MinModulus.SHCFiveCertificate.Generated
