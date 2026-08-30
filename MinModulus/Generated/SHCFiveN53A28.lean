import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_28 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 772, 402, 2626, 2308, 4234, 85, 643, 153, 403, 2786, 4232, 589, 2468, 773, 2631, 4387, 1507, 770, 4884, 3765, 1548, 386, 898, 89, 387, 2808, 1528, 3344, 5514, 705, 3264, 4544, 2866, 5191, 2067]

private theorem valid53_28 : ∀ code ∈ codes53_28, validRelationCode code := by
  decide

private theorem cover53_28 : ∀ q : IncreasingFourTail 51 (⟨28, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_28 (increasingFourValues (N := 53) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a28
    (q : IncreasingFourTail 51 (⟨28, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_28 _ valid53_28 (cover53_28 q)

end MinModulus.SHCFiveCertificate.Generated
