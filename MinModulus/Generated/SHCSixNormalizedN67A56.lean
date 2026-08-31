import MinModulus.Generated.SHCSixNormalizedN67A56B00
import MinModulus.Generated.SHCSixNormalizedN67A56B01
import MinModulus.Generated.SHCSixNormalizedN67A56B02
import MinModulus.Generated.SHCSixNormalizedN67A56B03
import MinModulus.Generated.SHCSixNormalizedN67A56B04

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate67_a56
    (q : IncreasingFiveTail 65 (⟨56, by norm_num⟩ : Fin 61)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 67 (increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 58 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a56_b00 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 58 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a56_b01 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 58 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a56_b02 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 58 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a56_b03 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨56, by norm_num⟩ : Fin 61), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 58 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a56_b04 q'

end MinModulus.SHCSixCertificate.Generated
