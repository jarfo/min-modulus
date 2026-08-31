import MinModulus.Generated.SHCSixNormalizedN69A26B00
import MinModulus.Generated.SHCSixNormalizedN69A26B01
import MinModulus.Generated.SHCSixNormalizedN69A26B02
import MinModulus.Generated.SHCSixNormalizedN69A26B03
import MinModulus.Generated.SHCSixNormalizedN69A26B04
import MinModulus.Generated.SHCSixNormalizedN69A26B05
import MinModulus.Generated.SHCSixNormalizedN69A26B06
import MinModulus.Generated.SHCSixNormalizedN69A26B07
import MinModulus.Generated.SHCSixNormalizedN69A26B08
import MinModulus.Generated.SHCSixNormalizedN69A26B09
import MinModulus.Generated.SHCSixNormalizedN69A26B10
import MinModulus.Generated.SHCSixNormalizedN69A26B11
import MinModulus.Generated.SHCSixNormalizedN69A26B12
import MinModulus.Generated.SHCSixNormalizedN69A26B13
import MinModulus.Generated.SHCSixNormalizedN69A26B14
import MinModulus.Generated.SHCSixNormalizedN69A26B15
import MinModulus.Generated.SHCSixNormalizedN69A26B16
import MinModulus.Generated.SHCSixNormalizedN69A26B17
import MinModulus.Generated.SHCSixNormalizedN69A26B18
import MinModulus.Generated.SHCSixNormalizedN69A26B19
import MinModulus.Generated.SHCSixNormalizedN69A26B20
import MinModulus.Generated.SHCSixNormalizedN69A26B21
import MinModulus.Generated.SHCSixNormalizedN69A26B22
import MinModulus.Generated.SHCSixNormalizedN69A26B23
import MinModulus.Generated.SHCSixNormalizedN69A26B24
import MinModulus.Generated.SHCSixNormalizedN69A26B25
import MinModulus.Generated.SHCSixNormalizedN69A26B26
import MinModulus.Generated.SHCSixNormalizedN69A26B27
import MinModulus.Generated.SHCSixNormalizedN69A26B28
import MinModulus.Generated.SHCSixNormalizedN69A26B29
import MinModulus.Generated.SHCSixNormalizedN69A26B30
import MinModulus.Generated.SHCSixNormalizedN69A26B31
import MinModulus.Generated.SHCSixNormalizedN69A26B32
import MinModulus.Generated.SHCSixNormalizedN69A26B33
import MinModulus.Generated.SHCSixNormalizedN69A26B34
import MinModulus.Generated.SHCSixNormalizedN69A26B35
import MinModulus.Generated.SHCSixNormalizedN69A26B36

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate69_a26
    (q : IncreasingFiveTail 67 (⟨26, by norm_num⟩ : Fin 63)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 69 (increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (39 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (39 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (39 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 39 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 29 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b00 q'
  · let c' : Fin (38 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (38 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (38 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 38 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 30 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b01 q'
  · let c' : Fin (37 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (37 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (37 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 37 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 31 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b02 q'
  · let c' : Fin (36 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (36 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (36 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 36 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 32 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b03 q'
  · let c' : Fin (35 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (35 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (35 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 35 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 33 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b04 q'
  · let c' : Fin (34 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (34 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (34 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 34 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 34 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b05 q'
  · let c' : Fin (33 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (33 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (33 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 33 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 35 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b06 q'
  · let c' : Fin (32 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (32 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (32 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 32 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 36 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b07 q'
  · let c' : Fin (31 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (31 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (31 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 31 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 37 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b08 q'
  · let c' : Fin (30 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (30 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (30 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 30 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 38 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b09 q'
  · let c' : Fin (29 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (29 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (29 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 29 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 39 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b10 q'
  · let c' : Fin (28 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (28 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (28 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 28 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨11, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 40 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b11 q'
  · let c' : Fin (27 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (27 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (27 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 27 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨12, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 41 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b12 q'
  · let c' : Fin (26 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (26 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (26 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 26 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨13, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 42 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b13 q'
  · let c' : Fin (25 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (25 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (25 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 25 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨14, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 43 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b14 q'
  · let c' : Fin (24 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (24 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (24 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 24 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨15, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 44 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b15 q'
  · let c' : Fin (23 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (23 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (23 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 23 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨16, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 45 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b16 q'
  · let c' : Fin (22 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (22 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (22 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 22 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨17, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 46 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b17 q'
  · let c' : Fin (21 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (21 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (21 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 21 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨18, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 47 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b18 q'
  · let c' : Fin (20 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (20 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (20 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 20 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨19, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 48 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b19 q'
  · let c' : Fin (19 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (19 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 19 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨20, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 49 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b20 q'
  · let c' : Fin (18 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (18 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 18 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨21, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 50 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b21 q'
  · let c' : Fin (17 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (17 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 17 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨22, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 51 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b22 q'
  · let c' : Fin (16 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (16 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 16 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨23, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 52 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b23 q'
  · let c' : Fin (15 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (15 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 15 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨24, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 53 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b24 q'
  · let c' : Fin (14 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (14 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 14 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨25, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 54 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b25 q'
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨26, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 55 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b26 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨27, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 56 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b27 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨28, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 57 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b28 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨29, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 58 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b29 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨30, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b30 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨31, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b31 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨32, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b32 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨33, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b33 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨34, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b34 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨35, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 64 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b35 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨26, by norm_num⟩ : Fin 63), ⟨⟨36, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 28 65 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a26_b36 q'

end MinModulus.SHCSixCertificate.Generated
