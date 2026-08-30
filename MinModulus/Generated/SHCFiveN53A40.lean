import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_40 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid53_40 : ∀ code ∈ codes53_40, validRelationCode code := by
  decide

private theorem cover53_40 : ∀ q : IncreasingFourTail 51 (⟨40, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_40 (increasingFourValues (N := 53) ⟨⟨40, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a40
    (q : IncreasingFourTail 51 (⟨40, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨40, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_40 _ valid53_40 (cover53_40 q)

end MinModulus.SHCFiveCertificate.Generated
