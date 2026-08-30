import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_15 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 526, 22, 2786, 4227, 2308]

private theorem valid35_15 : ∀ code ∈ codes35_15, validRelationCode code := by
  decide

private theorem cover35_15 : ∀ q : IncreasingFourTail 33 (⟨15, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_15 (increasingFourValues (N := 35) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a15
    (q : IncreasingFourTail 33 (⟨15, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_15 _ valid35_15 (cover35_15 q)

end MinModulus.SHCFiveCertificate.Generated
