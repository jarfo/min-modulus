import MinModulus.Generated.SHCSixN105A40B00
import MinModulus.Generated.SHCSixN105A40B01
import MinModulus.Generated.SHCSixN105A40B02
import MinModulus.Generated.SHCSixN105A40B03
import MinModulus.Generated.SHCSixN105A40B04
import MinModulus.Generated.SHCSixN105A40B05
import MinModulus.Generated.SHCSixN105A40B06
import MinModulus.Generated.SHCSixN105A40B07
import MinModulus.Generated.SHCSixN105A40B08
import MinModulus.Generated.SHCSixN105A40B09
import MinModulus.Generated.SHCSixN105A40B10

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate105_a40
    (q : IncreasingFiveTail 55 (⟨40, by norm_num⟩ : Fin 51)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat (values ⟨(⟨40, by norm_num⟩ : Fin 51), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b00 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b01 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b02 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b03 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b04 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨46, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b05 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨47, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b06 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨48, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b07 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b08 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨50, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b09 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨40, by norm_num⟩ : Fin 51), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨40, by norm_num⟩ : Fin 55) (⟨51, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a40_b10 q'

end MinModulus.SHCSixExceptionalCertificate.Generated
