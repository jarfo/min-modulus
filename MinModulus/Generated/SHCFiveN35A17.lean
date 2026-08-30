import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_17 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 589, 2468, 772, 4884, 526, 403, 402, 465, 773, 153]

private theorem valid35_17 : ∀ code ∈ codes35_17, validRelationCode code := by
  decide

private theorem cover35_17 : ∀ q : IncreasingFourTail 33 (⟨17, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_17 (increasingFourValues (N := 35) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a17
    (q : IncreasingFourTail 33 (⟨17, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_17 _ valid35_17 (cover35_17 q)

end MinModulus.SHCFiveCertificate.Generated
