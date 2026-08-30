import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_34 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid53_34 : ∀ code ∈ codes53_34, validRelationCode code := by
  decide

private theorem cover53_34 : ∀ q : IncreasingFourTail 51 (⟨34, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_34 (increasingFourValues (N := 53) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a34
    (q : IncreasingFourTail 51 (⟨34, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_34 _ valid53_34 (cover53_34 q)

end MinModulus.SHCFiveCertificate.Generated
