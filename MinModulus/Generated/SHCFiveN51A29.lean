import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 589, 403, 4387, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 386, 1347, 1667, 770, 3907, 387, 1827]

private theorem valid51_29 : ∀ code ∈ codes51_29, validRelationCode code := by
  decide

private theorem cover51_29 : ∀ q : IncreasingFourTail 49 (⟨29, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_29 (increasingFourValues (N := 51) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a29
    (q : IncreasingFourTail 49 (⟨29, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_29 _ valid51_29 (cover51_29 q)

end MinModulus.SHCFiveCertificate.Generated
