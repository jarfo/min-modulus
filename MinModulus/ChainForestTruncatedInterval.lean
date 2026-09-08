import MinModulus.GlobalFewEscape

/-! Charge a genuine boundary interval against the actual truncated
corner, retaining all short arm lengths. One genuine affine chain with
arbitrary remaining coordinates forces the binary bound when its width
pays n*2^(n-m). The logarithmic half-length criterion is explicit; below
binary size every such chain has an actual continuation. -/

namespace MinModulus
open Finset

/-- Removing a single truncated upper corner makes the entire
binary box injective for EVERY actual valid chain forest. Short-arm
coordinates are retained in full; long-arm corner sides have length n.
No zero relation or classification of mixed fibres is assumed. -/
theorem truncated_corner_gap_with_avoided_set_of_valid_chain_forest
    {n : ℕ} (_hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (F : Finset G) (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) →
      (∑ i, p i • x i) ≠ z) :
    2^n+F.card ≤ Fintype.card G+∏ i, min n (2^(L i)) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ ∀ i, 2^(L i)-n ≤ (p i).val
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let CE : {p : B // C p} ≃ (∀ i, Fin (min n (2^(L i)))) :=
    { toFun := fun p i ↦ ⟨(p.val i).val-(2^(L i)-n),by
        have := (p.val i).isLt
        have := p.property i
        omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+(2^(L i)-n),by
        have := (p i).isLt
        omega⟩,fun i ↦ Nat.le_add_left _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact Nat.sub_add_cancel (p.property i)
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have hcorner : Fintype.card {p : B // C p}=∏ i, min n (2^(L i)) := by
    rw [Fintype.card_congr CE,Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hR : Fintype.card R=2^n-(∏ i, min n (2^(L i))) := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox,hcorner]
  have hi : Function.Injective f := by
    intro p q heq
    by_contra hne
    have hvalues : (fun i ↦ (p.val i).val) ≠ (fun i ↦ (q.val i).val) := by
      intro h
      apply hne
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun h i)
    rcases box_collision_meets_truncated_corner_of_valid_chain_forest L hL
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
  have hvol : (∏ i, min n (2^(L i))) ≤ 2^n := by
    rw [← hcorner,← hbox]
    exact Fintype.card_subtype_le C
  omega

/-- A strict eighth-width interval pays against the full binomial error. -/
theorem wide_boundary_short_interval_truncated_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(2^(L a-3)) ≤ Fintype.card G+(∏ i, min n (2^(L i))) := by
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
  have hh := truncated_corner_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain F havoid
  simpa only [hcard] using hh


/-- One genuine arm whose larger interval pays the error forces the binary bound. -/
theorem binary_card_bound_of_genuine_arm_truncated_error
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hcharge : (∏ i, min n (2^(L i))) ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have hh := wide_boundary_short_interval_truncated_card_bound hn L hL g hg E x b hchain
    (by omega) a ha hLa hgenuine
  omega



/-- A selected long arm alone controls the truncated corner error;
all remaining arms may be singletons. -/
theorem truncated_corner_le_single_arm_error
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hsize : (∑ i, L i)=n) (a : β) :
    (∏ i, min n (2^(L i))) ≤ n*2^(n-L a) := by
  classical
  have hs := Finset.sum_erase_add Finset.univ L (Finset.mem_univ a)
  rw [hsize] at hs
  have htail : (∑ i ∈ Finset.univ.erase a, L i)=n-L a := by omega
  have hp : (∏ i ∈ Finset.univ.erase a, min n (2^(L i))) ≤ 2^(n-L a) := by
    calc
      _ ≤ ∏ i ∈ Finset.univ.erase a, 2^(L i) := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun _ _ ↦ min_le_right _ _)
      _ = 2^(n-L a) := by rw [Finset.prod_pow_eq_pow_sum,htail]
  calc
    _ = (∏ i ∈ Finset.univ.erase a, min n (2^(L i)))*min n (2^(L a)) :=
      (Finset.prod_erase_mul Finset.univ (fun i ↦ min n (2^(L i))) (Finset.mem_univ a)).symm
    _ ≤ 2^(n-L a)*n := Nat.mul_le_mul hp (min_le_left _ _)
    _ = n*2^(n-L a) := Nat.mul_comm _ _

/-- One genuine arm whose width dominates the remaining-coordinate
cube forces the binary bound, irrespective of the total escape count. -/
theorem binary_card_bound_of_one_long_genuine_arm
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a) (hcharge : n*2^(n-L a) ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnsmall : n ≤ 2^(L a-3) := by
    have hh := Nat.mul_le_mul_left n (Nat.one_le_two_pow (n := n-L a))
    simp only [Nat.mul_one] at hh
    exact hh.trans hcharge
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  exact binary_card_bound_of_genuine_arm_truncated_error hn L hL g hg E x b hchain a
    (by omega) ha ((truncated_corner_le_single_arm_error L hsize a).trans hcharge) hgenuine

/-- A designated chain and arbitrary remaining coordinates form an
actual forest, retaining the chain as a distinguished arm. -/
theorem exists_chain_singleton_forest
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (b x : G)
    (hchain : ∀ i : Fin m, g (Fin.castAdd k i)+b=2^i.val • x) :
    ∃ L : Option (Fin k) → ℕ, (∀ a, 0 < L a) ∧ L none=m ∧
      ∃ E : (Σ a : Option (Fin k), Fin (L a)) ≃ Fin (m+k),
        (∀ i : Fin (L none), (E ⟨none,i⟩).val=i.val) ∧
        ∃ y : Option (Fin k) → G,
          ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • y a := by
  let L : Option (Fin k) → ℕ := fun a ↦ a.elim m (fun _ ↦ 1)
  have hL : ∀ a, 0 < L a := by intro a; cases a <;> simp [L,hm]
  let E : (Σ a : Option (Fin k), Fin (L a)) ≃ Fin (m+k) :=
    { toFun := fun z ↦ match z with
        | ⟨none,i⟩ => Fin.castAdd k i
        | ⟨some j,_⟩ => Fin.natAdd m j
      invFun := Fin.addCases (fun i ↦ ⟨none,i⟩) (fun j ↦ ⟨some j,⟨0,by simp [L]⟩⟩)
      left_inv := by
        intro z
        rcases z with ⟨a,i⟩
        cases a with
        | none => simp
        | some j =>
          have hi : i=(⟨0,by simp [L]⟩ : Fin (L (some j))) := by
            apply Fin.ext
            change i.val=0
            have hh : i.val < 1 := i.isLt
            omega
          subst i
          simp
      right_inv := by
        intro i
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp }
  let y : Option (Fin k) → G := fun a ↦ a.elim x (fun j ↦ g (Fin.natAdd m j)+b)
  refine ⟨L,hL,rfl,E,?_,y,?_⟩
  · intro i
    rfl
  · intro a i
    cases a with
    | none => exact hchain i
    | some j =>
      have hi : i=(⟨0,by simp [L]⟩ : Fin (L (some j))) := by
            apply Fin.ext
            change i.val=0
            have hh : i.val < 1 := i.isLt
            omega
      subst i
      simp [E,y]

/-- A single long genuine affine chain forces the binary bound with
arbitrary other coordinates; no total escape-count assumption appears. -/
theorem binary_card_bound_of_long_genuine_chain_with_arbitrary_outsiders
    {m k : ℕ} (hm : 4 ≤ m) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (m+k) → G) (hg : ValidTuple g) (b x : G)
    (hchain : ∀ i : Fin m, g (Fin.castAdd k i)+b=2^i.val • x)
    (hgenuine : ∀ v, g v ≠ 2 • g (Fin.castAdd k ⟨m-1,by omega⟩)+b)
    (hcharge : (m+k)*2^k ≤ 2^(m-3)) : 2^(m+k) ≤ Fintype.card G := by
  obtain ⟨L,hL,hLm,E,hfirst,y,hy⟩ := exists_chain_singleton_forest (by omega) g b x hchain
  apply binary_card_bound_of_one_long_genuine_arm (by omega) L hL g hg E y b hy none
    (by simpa only [hLm] using hm) (by simpa only [hLm,Nat.add_sub_cancel_left] using hcharge)
  intro v
  have he : E ⟨none,⟨L none-1,by have := hL none; omega⟩⟩=Fin.castAdd k ⟨m-1,by omega⟩ := by
    apply Fin.ext
    rw [hfirst]
    simp only [Fin.val_castAdd]
    omega
  rw [he]
  exact hgenuine v

/-- The long-chain binary bound accepts any actual embedding, without
supplying a forest, an ordering of outsiders, or a bound on escapes. -/
theorem binary_card_bound_of_embedded_long_genuine_affine_chain
    {n m : ℕ} (hm : 4 ≤ m) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b x : G) (e : Fin m ↪ Fin n)
    (hchain : ∀ i : Fin m, g (e i)+b=2^i.val • x)
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨m-1,by omega⟩)+b)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) : 2^n ≤ Fintype.card G := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact binary_card_bound_of_long_genuine_chain_with_arbitrary_outsiders hm
    (fun i ↦ g (P i)) (validTuple_embedding P.toEmbedding g hg) b x
    (by intro i; simpa only [hP] using hchain i)
    (by intro v; simpa only [hP] using hgenuine (P v))
    (by simpa only [Nat.add_sub_cancel_left] using hcharge)

/-- At a subbinary cyclic modulus, every sufficiently long affine
chain must continue to an actual coordinate. Its target is extracted,
not assumed, and all other coordinates are arbitrary. -/
theorem exists_target_of_embedded_long_chain_below_binary
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i : Fin m, g (e i)+b=2^i.val • x)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) :
    ∃ v, g v=2 • g (e ⟨m-1,by omega⟩)+b := by
  by_contra hh
  have hgen : ∀ v, g v ≠ 2 • g (e ⟨m-1,by omega⟩)+b := by simpa only [not_exists] using hh
  have hb := binary_card_bound_of_embedded_long_genuine_affine_chain hm g hg b x e hchain hgen hcharge
  rw [ZMod.card] at hb
  omega

/-- A chain exceeding half the tuple by a logarithmic margin pays the
single-arm error; the statement keeps an explicit natural-number cutoff. -/
theorem long_chain_charge_of_logarithmic_length
    {n m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) : n*2^(n-m) ≤ 2^(m-3) := by
  have hn : n ≤ 2^(Nat.log 2 n+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n).le
  calc
    _ ≤ 2^(Nat.log 2 n+1)*2^(n-m) := Nat.mul_le_mul_right _ hn
    _ = 2^(Nat.log 2 n+1+(n-m)) := (pow_add _ _ _).symm
    _ ≤ 2^(m-3) := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)

/-- A single sufficiently long genuine affine chain forces the binary
bound with arbitrary other coordinates, in every finite abelian group. -/
theorem binary_card_bound_of_logarithmically_long_genuine_affine_chain
    {n m : ℕ} (hm : 4 ≤ m) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b x : G) (e : Fin m ↪ Fin n)
    (hchain : ∀ i : Fin m, g (e i)+b=2^i.val • x)
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨m-1,by omega⟩)+b)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) : 2^n ≤ Fintype.card G := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  exact binary_card_bound_of_embedded_long_genuine_affine_chain hm g hg b x e hchain hgenuine
    (long_chain_charge_of_logarithmic_length hm hmn hlong)

/-- Below binary size, any actual affine chain passing the logarithmic
half-length cutoff must have an actual continuation somewhere in the tuple. -/
theorem exists_target_of_logarithmically_long_chain_below_binary
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i : Fin m, g (e i)+b=2^i.val • x)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) :
    ∃ v, g v=2 • g (e ⟨m-1,by omega⟩)+b := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  exact exists_target_of_embedded_long_chain_below_binary hm g hg hsub b x e hchain
    (long_chain_charge_of_logarithmic_length hm hmn hlong)

end MinModulus
