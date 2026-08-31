import MinModulus.Generated.SHCSixNormalizedN67A60B00

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate67_a60
    (q : IncreasingFiveTail 65 (⟨60, by norm_num⟩ : Fin 61)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 67 (increasingFiveValues (N := 67) ⟨(⟨60, by norm_num⟩ : Fin 61), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨60, by norm_num⟩ : Fin 61), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 62 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a60_b00 q'

end MinModulus.SHCSixCertificate.Generated
