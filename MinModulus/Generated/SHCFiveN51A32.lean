import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_32 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid51_32 : ∀ code ∈ codes51_32, validRelationCode code := by
  decide

private theorem cover51_32 : ∀ q : IncreasingFourTail 49 (⟨32, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_32 (increasingFourValues (N := 51) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a32
    (q : IncreasingFourTail 49 (⟨32, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_32 _ valid51_32 (cover51_32 q)

end MinModulus.SHCFiveCertificate.Generated
