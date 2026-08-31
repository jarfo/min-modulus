import MinModulus.Generated.SHCSixNormalizedN67A02B00
import MinModulus.Generated.SHCSixNormalizedN67A02B01
import MinModulus.Generated.SHCSixNormalizedN67A02B02
import MinModulus.Generated.SHCSixNormalizedN67A02B03
import MinModulus.Generated.SHCSixNormalizedN67A02B04
import MinModulus.Generated.SHCSixNormalizedN67A02B05
import MinModulus.Generated.SHCSixNormalizedN67A02B06
import MinModulus.Generated.SHCSixNormalizedN67A02B07
import MinModulus.Generated.SHCSixNormalizedN67A02B08
import MinModulus.Generated.SHCSixNormalizedN67A02B09
import MinModulus.Generated.SHCSixNormalizedN67A02B10
import MinModulus.Generated.SHCSixNormalizedN67A02B11
import MinModulus.Generated.SHCSixNormalizedN67A02B12
import MinModulus.Generated.SHCSixNormalizedN67A02B13
import MinModulus.Generated.SHCSixNormalizedN67A02B14
import MinModulus.Generated.SHCSixNormalizedN67A02B15
import MinModulus.Generated.SHCSixNormalizedN67A02B16
import MinModulus.Generated.SHCSixNormalizedN67A02B17
import MinModulus.Generated.SHCSixNormalizedN67A02B18
import MinModulus.Generated.SHCSixNormalizedN67A02B19
import MinModulus.Generated.SHCSixNormalizedN67A02B20
import MinModulus.Generated.SHCSixNormalizedN67A02B21
import MinModulus.Generated.SHCSixNormalizedN67A02B22
import MinModulus.Generated.SHCSixNormalizedN67A02B23
import MinModulus.Generated.SHCSixNormalizedN67A02B24
import MinModulus.Generated.SHCSixNormalizedN67A02B25
import MinModulus.Generated.SHCSixNormalizedN67A02B26
import MinModulus.Generated.SHCSixNormalizedN67A02B27
import MinModulus.Generated.SHCSixNormalizedN67A02B28
import MinModulus.Generated.SHCSixNormalizedN67A02B29
import MinModulus.Generated.SHCSixNormalizedN67A02B30
import MinModulus.Generated.SHCSixNormalizedN67A02B31
import MinModulus.Generated.SHCSixNormalizedN67A02B32
import MinModulus.Generated.SHCSixNormalizedN67A02B33
import MinModulus.Generated.SHCSixNormalizedN67A02B34
import MinModulus.Generated.SHCSixNormalizedN67A02B35
import MinModulus.Generated.SHCSixNormalizedN67A02B36
import MinModulus.Generated.SHCSixNormalizedN67A02B37
import MinModulus.Generated.SHCSixNormalizedN67A02B38
import MinModulus.Generated.SHCSixNormalizedN67A02B39
import MinModulus.Generated.SHCSixNormalizedN67A02B40
import MinModulus.Generated.SHCSixNormalizedN67A02B41
import MinModulus.Generated.SHCSixNormalizedN67A02B42
import MinModulus.Generated.SHCSixNormalizedN67A02B43
import MinModulus.Generated.SHCSixNormalizedN67A02B44
import MinModulus.Generated.SHCSixNormalizedN67A02B45
import MinModulus.Generated.SHCSixNormalizedN67A02B46
import MinModulus.Generated.SHCSixNormalizedN67A02B47
import MinModulus.Generated.SHCSixNormalizedN67A02B48
import MinModulus.Generated.SHCSixNormalizedN67A02B49
import MinModulus.Generated.SHCSixNormalizedN67A02B50
import MinModulus.Generated.SHCSixNormalizedN67A02B51
import MinModulus.Generated.SHCSixNormalizedN67A02B52
import MinModulus.Generated.SHCSixNormalizedN67A02B53
import MinModulus.Generated.SHCSixNormalizedN67A02B54
import MinModulus.Generated.SHCSixNormalizedN67A02B55
import MinModulus.Generated.SHCSixNormalizedN67A02B56
import MinModulus.Generated.SHCSixNormalizedN67A02B57
import MinModulus.Generated.SHCSixNormalizedN67A02B58

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate67_a02
    (q : IncreasingFiveTail 65 (⟨2, by norm_num⟩ : Fin 61)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 67 (increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (61 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (61 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (61 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 61 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 5 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b00 q'
  · let c' : Fin (60 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (60 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (60 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 60 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 6 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b01 q'
  · let c' : Fin (59 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (59 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (59 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 59 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 7 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b02 q'
  · let c' : Fin (58 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (58 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (58 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 58 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 8 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b03 q'
  · let c' : Fin (57 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (57 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (57 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 57 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 9 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b04 q'
  · let c' : Fin (56 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (56 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (56 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 56 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 10 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b05 q'
  · let c' : Fin (55 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (55 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (55 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 55 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 11 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b06 q'
  · let c' : Fin (54 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (54 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (54 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 54 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 12 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b07 q'
  · let c' : Fin (53 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (53 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (53 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 53 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 13 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b08 q'
  · let c' : Fin (52 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (52 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (52 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 52 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 14 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b09 q'
  · let c' : Fin (51 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (51 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (51 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 51 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 15 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b10 q'
  · let c' : Fin (50 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (50 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (50 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 50 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨11, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 16 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b11 q'
  · let c' : Fin (49 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (49 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (49 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 49 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨12, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 17 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b12 q'
  · let c' : Fin (48 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (48 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (48 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 48 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨13, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 18 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b13 q'
  · let c' : Fin (47 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (47 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (47 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 47 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨14, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 19 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b14 q'
  · let c' : Fin (46 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (46 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (46 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 46 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨15, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 20 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b15 q'
  · let c' : Fin (45 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (45 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (45 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 45 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨16, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 21 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b16 q'
  · let c' : Fin (44 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (44 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (44 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 44 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨17, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 22 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b17 q'
  · let c' : Fin (43 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (43 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (43 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 43 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨18, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 23 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b18 q'
  · let c' : Fin (42 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (42 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (42 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 42 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨19, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 24 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b19 q'
  · let c' : Fin (41 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (41 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (41 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 41 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨20, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 25 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b20 q'
  · let c' : Fin (40 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (40 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (40 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 40 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨21, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 26 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b21 q'
  · let c' : Fin (39 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (39 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (39 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 39 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨22, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 27 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b22 q'
  · let c' : Fin (38 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (38 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (38 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 38 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨23, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 28 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b23 q'
  · let c' : Fin (37 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (37 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (37 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 37 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨24, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 29 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b24 q'
  · let c' : Fin (36 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (36 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (36 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 36 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨25, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 30 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b25 q'
  · let c' : Fin (35 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (35 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (35 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 35 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨26, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 31 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b26 q'
  · let c' : Fin (34 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (34 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (34 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 34 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨27, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 32 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b27 q'
  · let c' : Fin (33 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (33 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (33 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 33 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨28, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 33 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b28 q'
  · let c' : Fin (32 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (32 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (32 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 32 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨29, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 34 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b29 q'
  · let c' : Fin (31 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (31 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (31 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 31 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨30, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 35 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b30 q'
  · let c' : Fin (30 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (30 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (30 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 30 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨31, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 36 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b31 q'
  · let c' : Fin (29 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (29 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (29 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 29 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨32, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 37 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b32 q'
  · let c' : Fin (28 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (28 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (28 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 28 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨33, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 38 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b33 q'
  · let c' : Fin (27 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (27 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (27 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 27 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨34, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 39 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b34 q'
  · let c' : Fin (26 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (26 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (26 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 26 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨35, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 40 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b35 q'
  · let c' : Fin (25 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (25 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (25 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 25 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨36, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 41 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b36 q'
  · let c' : Fin (24 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (24 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (24 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 24 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨37, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 42 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b37 q'
  · let c' : Fin (23 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (23 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (23 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 23 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨38, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 43 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b38 q'
  · let c' : Fin (22 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (22 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (22 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 22 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨39, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 44 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b39 q'
  · let c' : Fin (21 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (21 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (21 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 21 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨40, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 45 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b40 q'
  · let c' : Fin (20 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (20 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (20 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 20 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨41, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 46 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b41 q'
  · let c' : Fin (19 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (19 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 19 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨42, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 47 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b42 q'
  · let c' : Fin (18 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (18 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 18 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨43, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 48 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b43 q'
  · let c' : Fin (17 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (17 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 17 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨44, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 49 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b44 q'
  · let c' : Fin (16 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (16 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 16 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨45, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 50 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b45 q'
  · let c' : Fin (15 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (15 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 15 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨46, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 51 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b46 q'
  · let c' : Fin (14 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (14 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 14 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨47, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 52 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b47 q'
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨48, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 53 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b48 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨49, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 54 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b49 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨50, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 55 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b50 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨51, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 56 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b51 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨52, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 57 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b52 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨53, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 58 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b53 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨54, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b54 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨55, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b55 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨56, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b56 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨57, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b57 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 67) ⟨(⟨2, by norm_num⟩ : Fin 61), ⟨⟨58, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 4 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate67_a02_b58 q'

end MinModulus.SHCSixCertificate.Generated
