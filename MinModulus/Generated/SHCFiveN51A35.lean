import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_35 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid51_35 : ∀ code ∈ codes51_35, validRelationCode code := by
  decide

private theorem cover51_35 : ∀ q : IncreasingFourTail 49 (⟨35, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_35 (increasingFourValues (N := 51) ⟨⟨35, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a35
    (q : IncreasingFourTail 49 (⟨35, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨35, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_35 _ valid51_35 (cover51_35 q)

end MinModulus.SHCFiveCertificate.Generated
