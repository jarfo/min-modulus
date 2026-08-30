import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_37 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid53_37 : ∀ code ∈ codes53_37, validRelationCode code := by
  decide

private theorem cover53_37 : ∀ q : IncreasingFourTail 51 (⟨37, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_37 (increasingFourValues (N := 53) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a37
    (q : IncreasingFourTail 51 (⟨37, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_37 _ valid53_37 (cover53_37 q)

end MinModulus.SHCFiveCertificate.Generated
