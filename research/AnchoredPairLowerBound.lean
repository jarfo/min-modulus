import MinModulus.G2AnchoredUnion

/-! The surviving quarter-intersection route. The small-pair hypothesis is
explicit; this file does not assert that such anchors always exist. -/
namespace MinModulus.Research
open Finset

/-- Every valid anchored cube contains a full binary cube. -/
theorem two_pow_pred_le_anchoredCube_card {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k : Fin n) :
    2 ^ (n - 1) ≤ (anchoredCube g k).card := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ m =>
    let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 k
    have he : e 0 = k := by simp [e]
    have hv : ValidTuple (fun i ↦ g (e i)) := validTuple_embedding e.toEmbedding g hg
    let R := (Finset.univ : Finset (Finset (Fin m))).image (ssum (fun i ↦ g (e i)))
    have hc : R.card = 2 ^ m := by
      dsimp only [R]
      rw [Finset.card_image_of_injective _ (ssum_injective _ hv),
        Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    have hs : R ⊆ anchoredCube g k := by
      intro x hx
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨S.image (fun j ↦ e j.succ), Finset.mem_univ _, ?_⟩
      rw [Finset.sum_image]
      · simp only [ssum, diff, he]
      · intro a _ b _ hab
        exact Fin.succ_injective _ (e.injective hab)
    simpa only [Nat.add_sub_cancel] using hc.symm.trans_le (Finset.card_le_card hs)

/-- One quarter-sized intersection suffices for the three-quarter modulus bound. -/
theorem three_quarters_le_modulus_of_anchored_pair {n N : ℕ} [NeZero N]
    (hn : 2 ≤ n) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (i j : Fin n)
    (hij : (anchoredCube g i ∩ anchoredCube g j).card ≤ 2 ^ (n - 2)) :
    3 * 2 ^ (n - 2) ≤ N := by
  have hi := two_pow_pred_le_anchoredCube_card g hg i
  have hj := two_pow_pred_le_anchoredCube_card g hg j
  have hu : (anchoredCube g i ∪ anchoredCube g j).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (anchoredCube g i ∪ anchoredCube g j)
  have hsum := Finset.card_union_add_card_inter (anchoredCube g i) (anchoredCube g j)
  have hp : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have he : n - 1 = (n - 2) + 1 := by omega
    rw [he, pow_succ, Nat.mul_comm]
  rw [hp] at hi hj
  omega

end MinModulus.Research
