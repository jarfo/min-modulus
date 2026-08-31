import MinModulus.Generated.SHCSixNormalizedN69A53B00
import MinModulus.Generated.SHCSixNormalizedN69A53B01
import MinModulus.Generated.SHCSixNormalizedN69A53B02
import MinModulus.Generated.SHCSixNormalizedN69A53B03
import MinModulus.Generated.SHCSixNormalizedN69A53B04
import MinModulus.Generated.SHCSixNormalizedN69A53B05
import MinModulus.Generated.SHCSixNormalizedN69A53B06
import MinModulus.Generated.SHCSixNormalizedN69A53B07
import MinModulus.Generated.SHCSixNormalizedN69A53B08
import MinModulus.Generated.SHCSixNormalizedN69A53B09

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate69_a53
    (q : IncreasingFiveTail 67 (⟨53, by norm_num⟩ : Fin 63)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 69 (increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 56 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b00 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 57 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b01 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 58 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b02 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b03 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b04 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b05 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b06 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b07 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 64 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b08 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨53, by norm_num⟩ : Fin 63), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 55 65 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a53_b09 q'

end MinModulus.SHCSixCertificate.Generated
