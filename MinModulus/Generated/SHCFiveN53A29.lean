import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 1347, 402, 4227, 2308, 85, 589, 2631, 773, 4387, 153, 403, 2786, 643, 4232, 2468, 4884, 4234, 770, 3907, 2648, 1668, 93, 1868, 386, 89, 1346, 1667, 899, 387]

private theorem valid53_29 : ∀ code ∈ codes53_29, validRelationCode code := by
  decide

private theorem cover53_29 : ∀ q : IncreasingFourTail 51 (⟨29, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_29 (increasingFourValues (N := 53) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a29
    (q : IncreasingFourTail 51 (⟨29, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_29 _ valid53_29 (cover53_29 q)

end MinModulus.SHCFiveCertificate.Generated
