import MinModulus.Generated.SHCSixN105A34B00
import MinModulus.Generated.SHCSixN105A34B01
import MinModulus.Generated.SHCSixN105A34B02
import MinModulus.Generated.SHCSixN105A34B03
import MinModulus.Generated.SHCSixN105A34B04
import MinModulus.Generated.SHCSixN105A34B05
import MinModulus.Generated.SHCSixN105A34B06
import MinModulus.Generated.SHCSixN105A34B07
import MinModulus.Generated.SHCSixN105A34B08
import MinModulus.Generated.SHCSixN105A34B09
import MinModulus.Generated.SHCSixN105A34B10
import MinModulus.Generated.SHCSixN105A34B11
import MinModulus.Generated.SHCSixN105A34B12
import MinModulus.Generated.SHCSixN105A34B13
import MinModulus.Generated.SHCSixN105A34B14
import MinModulus.Generated.SHCSixN105A34B15
import MinModulus.Generated.SHCSixN105A34B16

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate105_a34
    (q : IncreasingFiveTail 55 (⟨34, by norm_num⟩ : Fin 51)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat (values ⟨(⟨34, by norm_num⟩ : Fin 51), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (19 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (19 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 19 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b00 q'
  · let c' : Fin (18 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (18 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 18 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨36, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b01 q'
  · let c' : Fin (17 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (17 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 17 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b02 q'
  · let c' : Fin (16 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (16 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 16 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b03 q'
  · let c' : Fin (15 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (15 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 15 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b04 q'
  · let c' : Fin (14 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (14 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 14 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b05 q'
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b06 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b07 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b08 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b09 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b10 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨11, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨46, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b11 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨12, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨47, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b12 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨13, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨48, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b13 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨14, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b14 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨15, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨50, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b15 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : values ⟨(⟨34, by norm_num⟩ : Fin 51), ⟨⟨16, by norm_num⟩, c, d, e⟩⟩ =
        blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨51, by norm_num⟩ : Fin 55) q' := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact certificate105_a34_b16 q'

end MinModulus.SHCSixExceptionalCertificate.Generated
