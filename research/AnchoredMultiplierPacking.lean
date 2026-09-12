import research.AnchoredOverlapMultipliers

/-! Bounded multiplier exclusion packs disjoint binary slices. -/
namespace MinModulus.Research
open Finset
variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Exclude every multiplier from two through an explicit bound. -/
def NoAnchoredRelationThrough (g : Fin n → G) (k l : Fin n) (r : ℕ) : Prop :=
  ∀ M : ℕ, 2 ≤ M → M ≤ r → ∀ e : Fin n → ℤ, e k = 0 → e l = (M : ℤ) →
    (∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) →
    (∑ j, e j • (g j - g k)) ≠ 0

/-- Exclude only multiplier two. -/
abbrev NoAnchoredDoubleRelation (g : Fin n → G) (k l : Fin n) : Prop :=
  NoAnchoredRelationThrough g k l 2

/-- A bounded anchor coordinate and binary off-anchor coordinates are
injective when the corresponding multiplier relations are absent. -/
theorem bounded_anchor_binary_off_injective (g : Fin n → G) (hg : ValidTuple g)
    (k l : Fin n) (hkl : k ≠ l) (r : ℕ) (hgap : NoAnchoredRelationThrough g k l r)
    (t u : Fin (r+1)) (S T : Finset (Fin n))
    (hSk : k ∉ S) (hSl : l ∉ S) (hTk : k ∉ T) (hTl : l ∉ T)
    (hs : (∑ j ∈ S, (g j - g k)) + t.val • (g l - g k) =
      (∑ j ∈ T, (g j - g k)) + u.val • (g l - g k)) : t = u ∧ S = T := by
  let e : Fin n → ℤ := fun j ↦
    (if j ∈ S then 1 else 0) - (if j ∈ T then 1 else 0) +
      if j = l then (t.val : ℤ) - u.val else 0
  have hek : e k = 0 := by simp [e,hSk,hTk,hkl]
  have hel : e l = (t.val : ℤ) - u.val := by simp [e,hSl,hTl]
  have heb (j : Fin n) (hjl : j ≠ l) : -1 ≤ e j ∧ e j ≤ 1 := by
    dsimp only [e]
    simp only [hjl,if_false,add_zero]
    split_ifs <;> omega
  have hev : (∑ j, e j • (g j - g k)) = 0 := by
    simp only [e,add_smul,sub_smul,ite_smul,one_smul,zero_smul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_ite_mem,Finset.univ_inter,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,natCast_zsmul]
    calc
      _ = ((∑ j ∈ S, (g j - g k)) + t.val • (g l - g k)) -
          ((∑ j ∈ T, (g j - g k)) + u.val • (g l - g k)) := by simp only [Finset.sum_sub_distrib]; abel
      _ = 0 := sub_eq_zero.mpr hs
  have hupper : e l ≤ 1 := by
    by_contra hh
    have hMlo : 2 ≤ t.val-u.val := by omega
    have hMhi : t.val-u.val ≤ r := by have := t.isLt; omega
    have heM : e l = ((t.val-u.val : ℕ) : ℤ) := by omega
    exact hgap (t.val-u.val) hMlo hMhi e hek heM (fun j _ hjl ↦ heb j hjl) hev
  have hlower : -1 ≤ e l := by
    by_contra hh
    have hMlo : 2 ≤ u.val-t.val := by omega
    have hMhi : u.val-t.val ≤ r := by have := u.isLt; omega
    have heM : -e l = ((u.val-t.val : ℕ) : ℤ) := by omega
    apply hgap (u.val-t.val) hMlo hMhi (-e) (by simp [hek]) heM
    · intro j _ hjl
      have h := heb j hjl
      change -1 ≤ -e j ∧ -e j ≤ 1
      omega
    · simp only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,hev,neg_zero]
  have hezero := ternary_anchor_relation_eq_zero g hg k e hek (by
    intro j
    by_cases hjl : j = l
    · subst j; exact ⟨hlower,hupper⟩
    · exact heb j hjl) hev
  have hezl : e l = 0 := congrFun hezero l
  have htu : t = u := Fin.ext (by omega)
  refine ⟨htu,?_⟩
  ext j
  have hz := congrFun hezero j
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [e,hS,hT,htu] at hz ⊢

/-- Excluding multipliers through r packs r+1 disjoint binary slices. -/
theorem multiplier_packing_le_modulus {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (r : ℕ) (hgap : NoAnchoredRelationThrough g k l r) : (r+1) * 2^(n-2) ≤ N := by
  let F : Finset (Fin n) := Finset.univ \ {k,l}
  let B : Finset (Fin (r+1) × Finset (Fin n)) := Finset.univ.product F.powerset
  let f : Fin (r+1) × Finset (Fin n) → ZMod N := fun a ↦
    (∑ j ∈ a.2, (g j - g k)) + a.1.val • (g l - g k)
  have havoid (S : Finset (Fin n)) (hS : S ⊆ F) : k ∉ S ∧ l ∉ S := by
    constructor <;> intro hh
    · have := hS hh; simp [F] at this
    · have := hS hh; simp [F] at this
  have hinj : Set.InjOn f B := by
    intro a ha b hb he
    have hA := havoid a.2 (Finset.mem_powerset.mp (Finset.mem_product.mp ha).2)
    have hB := havoid b.2 (Finset.mem_powerset.mp (Finset.mem_product.mp hb).2)
    obtain ⟨h1,h2⟩ := bounded_anchor_binary_off_injective g hg k l hkl r hgap
      a.1 b.1 a.2 b.2 hA.1 hA.2 hB.1 hB.2 he
    exact Prod.ext h1 h2
  have hcardF : F.card = n-2 := by
    dsimp only [F]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Fintype.card_fin,Finset.card_pair hkl]
  have hcardB : B.card = (r+1) * 2^(n-2) := by
    exact (Finset.card_product (Finset.univ : Finset (Fin (r+1))) F.powerset).trans
      (by rw [Finset.card_univ,Fintype.card_fin,Finset.card_powerset,hcardF])
  have hle : (B.image f).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (B.image f)
  rwa [Finset.card_image_of_injOn hinj,hcardB] at hle


/-- In particular, excluding multiplier two gives the three-quarter bound. -/
theorem three_quarters_le_modulus_of_no_double_relation {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (hgap : NoAnchoredDoubleRelation g k l) : 3 * 2^(n-2) ≤ N := by
  simpa using multiplier_packing_le_modulus g hg k l hkl 2 hgap

/-- A modulus too small for the packing forces a bounded multiplier relation. -/
theorem exists_bounded_anchor_relation_of_small_modulus {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (r : ℕ) (hN : N < (r+1) * 2^(n-2)) :
    ∃ M : ℕ, 2 ≤ M ∧ M ≤ r ∧ ∃ e : Fin n → ℤ,
      e k = 0 ∧ e l = (M : ℤ) ∧
      (∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) ∧
      (∑ j, e j • (g j - g k)) = 0 := by
  by_contra hnone
  have hgap : NoAnchoredRelationThrough g k l r := by
    intro M hMlo hMhi e hek hel heb hev
    exact hnone ⟨M,hMlo,hMhi,e,hek,hel,heb,hev⟩
  have := multiplier_packing_le_modulus g hg k l hkl r hgap
  omega

/-- Throughout the near-extremal range N<2^n, every distinct anchor pair
admits multiplier two or three. This includes every possible G2 counterexample. -/
theorem double_or_triple_relation_of_modulus_lt_two_pow {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (hN : N < 2^n) :
    ∃ M : ℕ, (M = 2 ∨ M = 3) ∧ ∃ e : Fin n → ℤ,
      e k = 0 ∧ e l = (M : ℤ) ∧
      (∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) ∧
      (∑ j, e j • (g j - g k)) = 0 := by
  have hn : 2 ≤ n := by
    by_contra hh
    have he : k = l := Fin.ext (by have := k.isLt; have := l.isLt; omega)
    exact hkl he
  have hp : (3+1)*2^(n-2) = 2^n := by
    conv_rhs => rw [show n=(n-2)+2 by omega]
    rw [pow_add,Nat.mul_comm]
    norm_num
  obtain ⟨M,hMlo,hMhi,e,hek,hel,heb,hev⟩ :=
    exists_bounded_anchor_relation_of_small_modulus g hg k l hkl 3 (by simpa [hp] using hN)
  exact ⟨M,by omega,e,hek,hel,heb,hev⟩

end MinModulus.Research
