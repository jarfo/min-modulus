import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_26 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 4227, 589, 773, 2631, 2468, 772, 402, 465, 4884, 85, 643, 4387, 4232, 2476, 2626, 2308, 2786, 153, 403, 526, 705, 386, 4234, 3911, 2706, 5191, 22, 89, 770, 26, 449, 77, 93, 897, 4066, 1506]

private theorem valid53_26 : ∀ code ∈ codes53_26, validRelationCode code := by
  decide

private theorem cover53_26 : ∀ q : IncreasingFourTail 51 (⟨26, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_26 (increasingFourValues (N := 53) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a26
    (q : IncreasingFourTail 51 (⟨26, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_26 _ valid53_26 (cover53_26 q)

end MinModulus.SHCFiveCertificate.Generated
