import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 4884, 4234, 3765, 1828, 3906, 5191, 770, 5346, 2866, 2808, 449, 387]

private theorem valid51_28 : ∀ code ∈ codes51_28, validRelationCode code := by
  decide

private theorem cover51_28 : ∀ q : IncreasingFourTail 49 (⟨28, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_28 (increasingFourValues (N := 51) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a28
    (q : IncreasingFourTail 49 (⟨28, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_28 _ valid51_28 (cover51_28 q)

end MinModulus.SHCFiveCertificate.Generated
