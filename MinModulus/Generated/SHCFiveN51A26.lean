import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_26 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 772, 402, 2626, 2308, 85, 643, 4234, 153, 403, 2786, 773, 589, 2468, 4232, 2631, 4387, 1507, 4884, 770, 4885, 3756, 1827, 1548, 387, 1528, 386, 23, 22, 526, 89, 5045]

private theorem valid51_26 : ∀ code ∈ codes51_26, validRelationCode code := by
  decide

private theorem cover51_26 : ∀ q : IncreasingFourTail 49 (⟨26, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_26 (increasingFourValues (N := 51) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a26
    (q : IncreasingFourTail 49 (⟨26, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_26 _ valid51_26 (cover51_26 q)

end MinModulus.SHCFiveCertificate.Generated
