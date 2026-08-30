import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 403, 4387, 402, 589, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 386, 1667]

private theorem valid51_31 : ∀ code ∈ codes51_31, validRelationCode code := by
  decide

private theorem cover51_31 : ∀ q : IncreasingFourTail 49 (⟨31, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_31 (increasingFourValues (N := 51) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a31
    (q : IncreasingFourTail 49 (⟨31, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_31 _ valid51_31 (cover51_31 q)

end MinModulus.SHCFiveCertificate.Generated
