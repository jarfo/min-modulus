import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_25 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 589, 2468, 1347, 773, 2631, 4227, 772, 402, 2626, 643, 4232, 465, 85, 2476, 4884, 4387, 2308, 705, 153, 403, 2786, 4234, 1667, 386, 387, 770, 26, 526, 833, 77, 5514, 3906]

private theorem valid51_25 : ∀ code ∈ codes51_25, validRelationCode code := by
  decide

private theorem cover51_25 : ∀ q : IncreasingFourTail 49 (⟨25, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_25 (increasingFourValues (N := 51) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a25
    (q : IncreasingFourTail 49 (⟨25, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_25 _ valid51_25 (cover51_25 q)

end MinModulus.SHCFiveCertificate.Generated
