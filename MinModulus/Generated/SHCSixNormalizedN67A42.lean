import MinModulus.Generated.SHCSixNormalizedN67A42B00
import MinModulus.Generated.SHCSixNormalizedN67A42B01
import MinModulus.Generated.SHCSixNormalizedN67A42B02
import MinModulus.Generated.SHCSixNormalizedN67A42B03
import MinModulus.Generated.SHCSixNormalizedN67A42B04
import MinModulus.Generated.SHCSixNormalizedN67A42B05
import MinModulus.Generated.SHCSixNormalizedN67A42B06
import MinModulus.Generated.SHCSixNormalizedN67A42B07
import MinModulus.Generated.SHCSixNormalizedN67A42B08
import MinModulus.Generated.SHCSixNormalizedN67A42B09
import MinModulus.Generated.SHCSixNormalizedN67A42B10
import MinModulus.Generated.SHCSixNormalizedN67A42B11
import MinModulus.Generated.SHCSixNormalizedN67A42B12
import MinModulus.Generated.SHCSixNormalizedN67A42B13
import MinModulus.Generated.SHCSixNormalizedN67A42B14
import MinModulus.Generated.SHCSixNormalizedN67A42B15
import MinModulus.Generated.SHCSixNormalizedN67A42B16
import MinModulus.Generated.SHCSixNormalizedN67A42B17
import MinModulus.Generated.SHCSixNormalizedN67A42B18

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate67_a42
    (q : IncreasingFiveTail 65 (⟨42, by norm_num⟩ : Fin 61)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 67 (increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (21 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (21 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (21 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 21 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 45 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b00 q'
  · let c' : Fin (20 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (20 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (20 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 20 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 46 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b01 q'
  · let c' : Fin (19 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (19 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 19 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 47 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b02 q'
  · let c' : Fin (18 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (18 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 18 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 48 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b03 q'
  · let c' : Fin (17 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (17 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 17 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 49 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b04 q'
  · let c' : Fin (16 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (16 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 16 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 50 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b05 q'
  · let c' : Fin (15 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (15 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 15 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 51 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b06 q'
  · let c' : Fin (14 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (14 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 14 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 52 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b07 q'
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 53 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b08 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 54 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b09 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 55 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b10 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨11, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 56 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b11 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨12, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 57 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b12 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨13, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 58 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b13 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨14, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b14 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨15, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b15 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨16, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b16 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨17, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b17 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨42, by norm_num⟩ : Fin 61), ⟨⟨18, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 44 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a42_b18 q'

end MinModulus.SHCSixCertificate.Generated
