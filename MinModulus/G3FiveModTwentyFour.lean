import MinModulus.AffineChainForest
import MinModulus.FiveModTwentyFourCertificate
import MinModulus.G3LargeQuantitativeEscape

namespace MinModulus
open Finset

/-- In modulus 24, seeing both a parity change and a change modulo three
forces a unit among the two differences and their difference. -/
theorem unit_difference_mod_twenty_four (x y : ZMod 24)
    (hx : ZMod.castHom (by decide : 2 ∣ 24) (ZMod 2) x ≠ 0)
    (hy : ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) y ≠ 0) :
    IsUnit x ∨ IsUnit y ∨ IsUnit (x-y) := by
  have h : ∀ x y : ZMod 24,
      ZMod.castHom (by decide : 2 ∣ 24) (ZMod 2) x ≠ 0 →
      ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y) := by decide
  exact h x y hx hy

/-- A valid five-tuple modulo 24 has two coordinates with unit difference.
Otherwise its translated affine span misses parity or reduction modulo three. -/
theorem exists_unit_difference_of_valid_five_mod_twenty_four
    (g : Fin 5 → ZMod 24) (hg : ValidTuple g) :
    ∃ a b, IsUnit (g b-g a) := by
  classical
  have hspan (p : ℕ) [NeZero p] (hd : p ∣ 24) (h1 : (1 : ZMod p) ≠ 0) :
      ∃ i, ZMod.castHom hd (ZMod p) (g i-g 0) ≠ 0 := by
    by_contra hn
    push Not at hn
    let φ : ZMod 24 →+ ZMod p := (ZMod.castHom hd (ZMod p)).toAddMonoidHom
    have ht : φ.ker = ⊤ :=
      subgroup_eq_top_of_valid_subbinary_translate g hg (by norm_num [ZMod.card])
        (-g 0) φ.ker (by
          intro i
          change ZMod.castHom hd (ZMod p) (g i + -g 0) = 0
          simpa only [sub_eq_add_neg] using hn i)
    have hz : φ 1=0 := AddMonoidHom.mem_ker.mp (ht ▸ AddSubgroup.mem_top 1)
    apply h1
    change (ZMod.castHom hd (ZMod p)) 1 = 0 at hz
    simpa only [map_one] using hz
  obtain ⟨a,ha⟩ := hspan 2 (by decide) (by decide)
  obtain ⟨b,hb⟩ := hspan 3 (by decide) (by decide)
  rcases unit_difference_mod_twenty_four (g a-g 0) (g b-g 0) ha hb with h | h | h
  · exact ⟨0,a,h⟩
  · exact ⟨0,b,h⟩
  · exact ⟨b,a,by simpa only [sub_sub_sub_cancel_right] using h⟩

/-- Translation, permutation and multiplication by a unit put two selected
coordinates at zero and one while preserving the full tuple's validity. -/
theorem exists_normalized_valid_five_of_unit_difference
    {N : ℕ} [NeZero N] [Nontrivial (ZMod N)] (g : Fin 5 → ZMod N) (hg : ValidTuple g)
    (a b : Fin 5) (hu : IsUnit (g b-g a)) :
    ∃ w : Fin 5 → ZMod N, ValidTuple w ∧ w 0=0 ∧ w 1=1 := by
  classical
  obtain ⟨u,hu⟩ := hu
  have hab : a ≠ b := by
    intro h
    have hz : (u : ZMod N)=0 := by simpa only [h,sub_self] using hu
    exact Units.ne_zero u hz
  let s : Equiv.Perm (Fin 5) := Equiv.swap 0 a
  let t : Fin 5 := s b
  have ht : t ≠ 0 := by
    intro h
    have hh : s b=s a := by simpa [t,s] using h
    exact hab (s.injective hh).symm
  let e : Equiv.Perm (Fin 5) := (Equiv.swap 1 t).trans s
  have he0 : e 0=a := by
    dsimp [e]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 1) ht.symm]
    simp [s]
  have he1 : e 1=b := by simp [e,t,s]
  let φ : ZMod N →+ ZMod N := {
    toFun := fun x ↦ (↑u⁻¹ : ZMod N)*x
    map_zero' := mul_zero _
    map_add' := mul_add _ }
  have hφ : Function.Injective φ := by
    intro x y h
    exact (Units.isUnit u⁻¹).mul_left_cancel h
  let w : Fin 5 → ZMod N := fun i ↦ φ (g (e i)-g a)
  refine ⟨w,validTuple_comp (validTuple_sub_const _
    (validTuple_embedding e.toEmbedding g hg) (g a)) φ hφ,?_,?_⟩
  · simp [w,he0]
  · simp [w,he1,φ,← hu]

/-- The full dimension-five exceptional G3 case. The finite check is applied
only after a proved affine normalization of the arbitrary input tuple. -/
theorem not_validTuple_five_mod_twenty_four (g : Fin 5 → ZMod 24) :
    ¬ ValidTuple g := by
  intro hg
  letI : Nontrivial (ZMod 24) := ⟨⟨0,1,by decide⟩⟩
  obtain ⟨a,b,hu⟩ := exists_unit_difference_of_valid_five_mod_twenty_four g hg
  obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_five_of_unit_difference g hg a b hu
  have heq : w = ![0,1,w 2,w 3,w 4] := by
    funext i
    fin_cases i <;> simp [h0,h1]
  rw [heq] at hw
  exact FiveModTwentyFourCertificate.not_validTuple_normalized _ _ _ hw

/-- The quantitative G3 obstruction above an explicit dimension cutoff. -/
def ExceptionalQuantitativeEscapeObstructionFrom (k : ℕ) : Prop :=
  ∀ n : ℕ, k ≤ n → 2 ^ Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2 * globalBound (n - 1)), ValidTuple g →
      (∀ (b : ZMod (2 * globalBound (n - 1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j = 2 • g i + b)).card = r →
        2 ^ ((n + r) / (r + 1) - 3) < (n + r).choose (r + 1) ∧
          n < (r + 1) ^ 2 * (Nat.log 2 n + 1) + 3 * (r + 1)) →
      False

/-- The proved five-coordinate exclusion discharges the first remaining
case of quantitative G3, leaving exactly its dimensions at least six. -/
theorem largeExceptionalQuantitativeEscapeObstruction_iff_from_six :
    LargeExceptionalQuantitativeEscapeObstruction ↔
      ExceptionalQuantitativeEscapeObstructionFrom 6 := by
  constructor
  · intro h n hn hnpow g hg hquant
    exact h n (by omega) hnpow g hg hquant
  · intro h n hn hnpow g hg hquant
    by_cases hn6 : 6 ≤ n
    · exact h n hn6 hnpow g hg hquant
    · have hn5 : n = 5 := by omega
      subst n
      exact not_validTuple_five_mod_twenty_four g hg

end MinModulus
