import MinModulus.ChainRejoinDoubleCharge

/-! Count the actual bounded coefficient corner with total weight below n.
It improves both the truncated rectangle and stars-and-bars estimates,
survives controlled continuation, and forces the binary bound for a
genuine selected arm with arbitrary other chains and outsiders. Reflection
compares a sufficiently light rectangle with twice this smaller corner.
The arbitrary-endpoint continuation/cycle integration is not asserted here;
all unrestricted conjecture gates remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- The bounded coefficient corner retains the total-weight constraint. -/
noncomputable def chainFamilyCornerCard {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) : ℕ :=
  Fintype.card {p : ∀ i, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}

/-- The corresponding partial-family error retains arbitrary unselected coordinates. -/
noncomputable def chainFamilyCornerError {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) : ℕ :=
  chainFamilyCornerCard n L*2^(n-∑ i, L i)

/-- The bounded corner is contained in the truncated rectangle. -/
theorem chain_family_corner_card_le_product
    {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) :
    chainFamilyCornerCard n L ≤ ∏ i, min n (2^(L i)) := by
  have h := Fintype.card_subtype_le (fun p : ∀ i, Fin (min n (2^(L i))) ↦ (∑ i, (p i).val) < n)
  simpa only [chainFamilyCornerCard,Fintype.card_pi,Fintype.card_fin] using h

/-- It also retains the full stars-and-bars improvement. -/
theorem chain_family_corner_card_le_binomial
    {β : Type*} [Fintype β] {n : ℕ} (hn : 0 < n) (L : β → ℕ) :
    chainFamilyCornerCard n L ≤ (n+Fintype.card β-1).choose (Fintype.card β) := by
  let C := {p : ∀ i, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let f : C → β → ℕ := fun p i ↦ (p.val i).val
  apply card_le_choose_of_injective_small_sum_profiles hn f ?_ (fun p ↦ p.property)
  intro p q he
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun he i)

/-- Shrinking every side preserves the total-weight cutoff. -/
theorem chain_family_corner_card_mono_sides
    {β : Type*} [Fintype β] {n : ℕ} (L M : β → ℕ)
    (hside : ∀ i, min n (2^(M i)) ≤ min n (2^(L i))) :
    chainFamilyCornerCard n M ≤ chainFamilyCornerCard n L := by
  let C (A : β → ℕ) := {p : ∀ i, Fin (min n (2^(A i))) // (∑ i, (p i).val) < n}
  let f : C M → C L := fun p ↦ ⟨fun i ↦ Fin.castLE (hside i) (p.val i),p.property⟩
  apply Fintype.card_le_of_injective f
  intro p q he
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun z : C L ↦ (z.val i).val) he

/-- Actual extension and splicing preserve the bounded-corner error
once the designated side is saturated. -/
theorem chain_family_corner_error_mono
    {β : Type*} [Fintype β] {n : ℕ} (L M : β → ℕ) (a : β)
    (hwide : n ≤ 2^(L a)) (ha : L a ≤ M a)
    (hother : ∀ d, d ≠ a → M d ≤ L d) (hcover : (∑ d, L d) ≤ (∑ d, M d)) :
    chainFamilyCornerError n M ≤ chainFamilyCornerError n L := by
  have hcard : chainFamilyCornerCard n M ≤ chainFamilyCornerCard n L := by
    apply chain_family_corner_card_mono_sides L M
    intro d
    by_cases hda : d=a
    · subst d
      have hM := hwide.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha)
      rw [min_eq_left hM,min_eq_left hwide]
    · exact min_le_min_left n (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hother d hda))
  exact Nat.mul_le_mul hcard (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))

/-- If a box and its coordinate reflection have combined weight below
2n, one of every reflected pair lies in the small-sum corner. -/
theorem box_card_le_twice_small_sum_corner
    {β : Type*} [Fintype β] (n : ℕ) (D : β → ℕ)
    (hbudget : (∑ i, (D i-1)) < 2*n) :
    (∏ i, D i) ≤ 2*Fintype.card {p : ∀ i, Fin (D i) // (∑ i, (p i).val) < n} := by
  let B := ∀ i, Fin (D i)
  let C : B → Prop := fun p ↦ (∑ i, (p i).val) < n
  let rev : B → B := fun p i ↦ (p i).rev
  have hrev (p : B) : rev (rev p)=p := by funext i; simp [rev]
  have hcover (p : B) : ¬ C p → C (rev p) := by
    intro hp
    have hpoint (i : β) : (p i).val+(rev p i).val=D i-1 := by
      simp only [rev,Fin.val_rev]
      have := (p i).isLt
      omega
    have hsum : (∑ i, (p i).val)+(∑ i, (rev p i).val)=∑ i, (D i-1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
    dsimp only [C] at hp ⊢
    omega
  let F : B → Bool × {p : B // C p} := fun p ↦
    if hp : C p then (true,⟨p,hp⟩) else (false,⟨rev p,hcover p hp⟩)
  have hF : Function.Injective F := by
    intro p q he
    by_cases hp : C p <;> by_cases hq : C q
    · have hh := congrArg (fun z : Bool × {p : B // C p} ↦ z.2.val) he
      simpa only [F,dif_pos hp,dif_pos hq] using hh
    · have hh := congrArg Prod.fst he
      simp only [F,dif_pos hp,dif_neg hq] at hh
      cases hh
    · have hh := congrArg Prod.fst he
      simp only [F,dif_neg hp,dif_pos hq] at hh
      cases hh
    · have hh := congrArg (fun z : Bool × {p : B // C p} ↦ rev z.2.val) he
      simpa only [F,dif_neg hp,dif_neg hq,hrev] using hh
  simpa only [B,Fintype.card_pi,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool] using
    Fintype.card_le_of_injective F hF

/-- The selected coordinate axis is contained in the bounded corner. -/
theorem selected_side_le_chain_family_corner_card
    {β : Type*} [Fintype β] {n : ℕ} (hn : 0 < n) (L : β → ℕ) (a : β) :
    min n (2^(L a)) ≤ chainFamilyCornerCard n L := by
  classical
  let C := {p : ∀ i, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let f : Fin (min n (2^(L a))) → C := fun p ↦
    ⟨fun i ↦ ⟨if i=a then p.val else 0,by
      by_cases hi : i=a
      · subst i; simpa only [if_true] using p.isLt
      · simp only [if_neg hi]
        exact lt_min hn (by positivity)⟩,by
      simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using
        lt_of_lt_of_le p.isLt (min_le_left n (2^(L a)))⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Fin.ext
    have hh := congrArg (fun z : C ↦ (z.val a).val) he
    simpa only [f,if_true] using hh
  simpa only [Fintype.card_fin,chainFamilyCornerCard] using Fintype.card_le_of_injective f hf

/-- The smaller corner charge still implies the selected width condition. -/
theorem chain_family_width_of_corner_charge
    {β : Type*} [Fintype β] {n : ℕ} (hn : 0 < n)
    (L : β → ℕ) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) : 2*n+1 ≤ 2^(L a) := by
  have hfactor : min n (2^(L a)) ≤ chainFamilyCornerError n L := by
    calc
      _ ≤ chainFamilyCornerCard n L := selected_side_le_chain_family_corner_card hn L a
      _ ≤ _ := by
        unfold chainFamilyCornerError
        simpa only [mul_one] using Nat.mul_le_mul_left (chainFamilyCornerCard n L)
          (Nat.one_le_two_pow (n:=n-∑ i, L i))
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have hbase : 0 < (2 : ℕ)^(L a-3) := by positivity
  have hwide : n ≤ 2^(L a) := by
    by_contra hh
    rw [min_eq_right (by omega : 2^(L a) ≤ n)] at hfactor
    nlinarith [hfactor.trans hcharge]
  rw [min_eq_left hwide] at hfactor
  have hncharge := hfactor.trans hcharge
  omega

/-- A reflected-pair budget controls the rectangle by twice the smaller
corner, retaining the same uncovered-coordinate factor. -/
theorem truncated_error_le_twice_corner_error
    {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ)
    (hbudget : (∑ i, (min n (2^(L i))-1)) < 2*n) :
    chainFamilyTruncatedError n L ≤ 2*chainFamilyCornerError n L := by
  have h := Nat.mul_le_mul_right (2^(n-∑ i, L i))
    (box_card_le_twice_small_sum_corner n (fun i ↦ min n (2^(L i))) hbudget)
  simpa only [chainFamilyTruncatedError,chainFamilyCornerError,chainFamilyCornerCard,mul_assoc] using h

/-- The actual bounded corner, with its sum cutoff, pays for every
collision and any genuinely avoided residues. -/
theorem bounded_corner_gap_with_avoided_set_of_valid_chain_forest
    {n : ℕ} (_hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (F : Finset G) (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) →
      (∑ i, p i • x i) ≠ z) :
    2^n+F.card ≤ Fintype.card G+chainFamilyCornerCard n L := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ (∑ i, (2^(L i)-1-(p i).val)) < n
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let dist : {p : B // C p} → β → ℕ := fun p i ↦ 2^(L i)-1-(p.val i).val
  have hdist : Function.Injective dist := by
    intro p q he
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh : 2^(L i)-1-(p.val i).val=2^(L i)-1-(q.val i).val := congrFun he i
    have := (p.val i).isLt
    have := (q.val i).isLt
    omega
  let T := {p : ∀ i, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let Fcorner : {p : B // C p} → T := fun p ↦ ⟨fun i ↦ ⟨dist p i,by
    have hsum := Finset.single_le_sum (f:=dist p) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := (p.val i).isLt
    have hn' : dist p i < n := hsum.trans_lt p.property
    exact lt_min hn' (by dsimp only [dist]; omega)⟩,p.property⟩
  have hFcorner : Function.Injective Fcorner := by
    intro p q he
    apply hdist
    funext i
    exact congrArg (fun z : T ↦ (z.val i).val) he
  have hcorner : Fintype.card {p : B // C p} ≤ chainFamilyCornerCard n L :=
    Fintype.card_le_of_injective Fcorner hFcorner
  have hR : Fintype.card R=2^n-Fintype.card {p : B // C p} := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox]
  have hi : Function.Injective f := by
    intro p q heq
    by_contra hne
    have hvalues : (fun i ↦ (p.val i).val) ≠ (fun i ↦ (q.val i).val) := by
      intro h
      apply hne
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun h i)
    rcases box_collision_meets_upper_simplex_of_valid_chain_forest L hL
        g hg E x b hchain (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val)
        (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) hvalues heq with hp | hq
    · exact p.property hp
    · exact q.property hq
  let f' : R → {z : G // z ∉ F} := fun p ↦ ⟨f p,by
    intro hp
    exact havoid (f p) hp (fun i ↦ (p.val i).val) (fun i ↦ (p.val i).isLt) rfl⟩
  have hi' : Function.Injective f' := by
    intro p q he
    exact hi (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f' hi'
  have hremain : Fintype.card {z : G // z ∉ F}=Fintype.card G-F.card := by
    rw [Fintype.card_subtype_compl (fun z : G ↦ z ∈ F)]
    simp only [Fintype.card_coe]
  rw [hR,hremain] at hh
  have hFcard : F.card ≤ Fintype.card G := Finset.card_le_univ F
  have hcorner_le : Fintype.card {p : B // C p} ≤ 2^n := by
    rw [← hbox]
    exact Fintype.card_subtype_le C
  omega

/-- Restricting to the first family retains its sum cutoff; the other
family contributes at most its entire rectangle. -/
theorem chain_family_corner_card_sum_le
    {β γ : Type*} [Fintype β] [Fintype γ] (n : ℕ) (L : β → ℕ) (M : γ → ℕ) :
    chainFamilyCornerCard n (Sum.elim L M) ≤
      chainFamilyCornerCard n L*(∏ i, min n (2^(M i))) := by
  classical
  letI : DecidableEq (β ⊕ γ) := Classical.decEq _
  let A := {p : ∀ i : β ⊕ γ, Fin (min n (2^(Sum.elim L M i))) // (∑ i, (p i).val) < n}
  let B := {p : ∀ i : β, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let D := ∀ i : γ, Fin (min n (2^(M i)))
  let f : A → B × D := fun p ↦ (⟨fun i ↦ p.val (Sum.inl i),by
    have h := p.property
    rw [Fintype.sum_sum_type] at h
    change (∑ i, (p.val (Sum.inl i)).val) < n
    omega⟩,fun i ↦ p.val (Sum.inr i))
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    funext i
    cases i with
    | inl i => exact congrArg (fun z : B × D ↦ z.1.val i) he
    | inr i => exact congrArg (fun z : B × D ↦ z.2 i) he
  have h := Fintype.card_le_of_injective f hf
  have hA : Fintype.card A=chainFamilyCornerCard n (Sum.elim L M) := by
    unfold chainFamilyCornerCard
    exact Fintype.card_congr (Equiv.refl _)
  have hB : Fintype.card B=chainFamilyCornerCard n L := by
    unfold chainFamilyCornerCard
    exact Fintype.card_congr (Equiv.refl _)
  have hD : Fintype.card D=∏ i, min n (2^(M i)) := by
    simp only [D,Fintype.card_pi,Fintype.card_fin]
  rwa [Fintype.card_prod,hA,hB,hD] at h

/-- A genuine arm supplies an avoided interval charged to the exact bounded corner. -/
theorem wide_boundary_short_interval_bounded_corner_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(2^(L a-3)) ≤ Fintype.card G+chainFamilyCornerCard n L := by
  classical
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have hnz := boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha
  let f : Fin (2^(L a-3)) → G := fun t ↦ 2^(L a) • x a+t.val • x a
  have hi : Function.Injective f := by
    intro t u he
    exact seed_interval_injective_of_wide_axis L hL g hg E x b hchain a (2^(L a-3))
      (by omega) (add_left_cancel he)
  let F := Finset.univ.image f
  have hcard : F.card=2^(L a-3) := by
    simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact short_axis_interval_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a
      (by omega) hLa hnz hgenuine t.val (by have := t.isLt; omega) p hp
  have hh := bounded_corner_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain F havoid
  simpa only [hcard] using hh


/-- One genuine arm whose larger interval pays the error forces the binary bound. -/
theorem binary_card_bound_of_genuine_arm_bounded_corner
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hcharge : chainFamilyCornerCard n L ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have hh := wide_boundary_short_interval_bounded_corner_card_bound hn L hL g hg E x b hchain
    (by omega) a ha hLa hgenuine
  omega



/-- The bounded-corner charge forces the binary bound for a genuine
selected arm, with arbitrary other chains and unselected coordinates. -/
theorem binary_card_bound_of_partial_genuine_bounded_corner
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (x : β → G)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  let C := {v : Fin n // v ∉ Set.range e}
  let M : β ⊕ C → ℕ := Sum.elim L (fun _ ↦ 1)
  have hM : ∀ i, 0 < M i := by intro i; cases i <;> simp [M,hL]
  obtain ⟨E,hE,y,hy,hc⟩ := exists_partial_chain_forest_completion L g b x e hchain
  have herror : chainFamilyCornerCard n M ≤ chainFamilyCornerError n L := by
    calc
      _ ≤ chainFamilyCornerCard n L*(∏ _i : C, min n (2^1)) :=
        chain_family_corner_card_sum_le n L (fun _ : C ↦ 1)
      _ ≤ chainFamilyCornerCard n L*(∏ _i : C, 2) := Nat.mul_le_mul_left _
        (Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun _ _ ↦ min_le_right n 2))
      _ = _ := by simp only [chainFamilyCornerError,Finset.prod_const,Finset.card_univ,
          partial_chain_forest_complement_card L e,C]
  apply binary_card_bound_of_genuine_arm_bounded_corner hn M hM g hg E y b hc (Sum.inl a)
    (chain_family_width_of_corner_charge hn L a ha hcharge) ha (herror.trans hcharge)
  intro v
  simpa only [hE,hy,M,Sum.elim_inl] using hgenuine v

end MinModulus
