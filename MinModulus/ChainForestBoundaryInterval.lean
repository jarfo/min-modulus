import MinModulus.ChainForestLongBoundary

/-! A genuine wide boundary has an exponential interval of missing
residues along its own seed. This pays the binomial packing error and
proves the binary bound for every genuine three-chain forest from
length 67. Original critical data with at most three affine escapes
therefore give half descent in every stratum. Unrestricted G1/G2/G3
remain open; a large no-half tuple must have four escapes at every shift. -/

namespace MinModulus
open Finset

/-- A tiny positive shift beyond twice a chain width fits in the
chain's original coin budget: four top coins leave room for the tail. -/
theorem exists_binary_rep_twice_width_add_tiny
    {L v : ℕ} (hL : 4 ≤ L) (hv : 0 < v) (hsmall : v ≤ 2^(L-4)) :
    ∃ u, Supp L u ∧ val L u=2*2^L-1+v ∧ dsum L u ≤ L := by
  obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L-4) (v-1) (by omega)
  have hsL := supp_mono (by omega : L-4 ≤ L) hs
  obtain ⟨w,hws,hw,hwd⟩ := exists_binary_rep_add_two_top_coins (by omega : 0 < L) u hsL
  obtain ⟨z,hzs,hz,hzd⟩ := exists_binary_rep_add_two_top_coins (by omega : 0 < L) w hws
  refine ⟨z,hzs,?_,?_⟩
  · rw [hz,hw,val_pad (by omega : L-4 ≤ L) hs,hu]
    have hp : 0 < 2^L := by positivity
    omega
  · rw [hzd,hwd,dsum_pad (by omega : L-4 ≤ L) hs]
    omega

/-- A representation just beyond a long boundary with a strict deficit
in that same arm gives an actual full-length rival. -/
theorem not_validTuple_of_long_boundary_axis_collision
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (_hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (t : ℕ) (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (hpa : p a < t) (ht : t-p a ≤ 2^(L a-4))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x a) : ¬ ValidTuple g := by
  classical
  let X := fun i ↦ 2^(L i)-1-p i+(if i=a then 2^(L a)+t else 0)
  have hXa : X a=2*2^(L a)-1+(t-p a) := by
    simp only [X,if_true]
    have := hp a
    have h : 0 < 2^(L a) := by positivity
    omega
  have hrep : ∀ i, ∃ u, val (L i) u=X i ∧ dsum (L i) u ≤ L i := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,_,hu,hdu⟩ := exists_binary_rep_twice_width_add_tiny hLa (by omega : 0 < t-p a) ht
      exact ⟨u,hu.trans hXa.symm,hdu⟩
    · obtain ⟨u,_,hu,hdu⟩ := exists_rep_le (L i) (2^(L i)-1-p i) (by
        have h : 0 < 2^(L i) := by positivity
        omega)
      exact ⟨u,by simpa only [X,if_neg hi,add_zero] using hu,hdu⟩
  choose u hu hcost using hrep
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hlow : (∑ i, dsum (L i) (u i)) ≤ n := by
    simpa only [hsize] using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hcost i)
  have hhigh : n ≤ ∑ i, X i := by
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    rw [hXa] at hh
    have h : 0 < 2^(L a) := by positivity
    omega
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    rw [hXa]
    have h : 0 < 2^(L a) := by positivity
    omega
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hb : (∑ i, (if i=a then 2^(L a)+t else 0) • x i)=2^(L a) • x a+t • x a := by
      simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,add_nsmul]
    simp only [X,add_nsmul,Finset.sum_add_distrib,hb,← heq]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_nsmul,Nat.sub_add_cancel (by have := hp i; omega)]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hlow hhigh hneq hsum

/-- A nonzero genuine long boundary excludes an entire interval
along its OWN seed, with no second wide arm or parity hypothesis. -/
theorem axis_interval_not_in_box_of_long_genuine_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : n ≤ 2^(L a)) (hLa : 4 ≤ L a) (hnz : 2^(L a) • x a ≠ 0)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t ≤ 2^(L a-4))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x a := by
  classical
  intro heq
  have hpa : p a < t := by
    by_contra hnot
    let P := fun i ↦ if i=a then p a-t else p i
    have hP : ∀ i, P i < 2^(L i) := by
      intro i
      by_cases hi : i=a
      · subst i; simpa only [P,if_pos rfl] using (Nat.sub_le (p a) t).trans_lt (hp a)
      · simpa only [P,if_neg hi] using hp i
    have hsum : (∑ i, P i • x i)+t • x a=∑ i, p i • x i := by
      have hs : ∀ i, p i • x i=P i • x i+(if i=a then t • x a else 0) := by
        intro i
        by_cases hi : i=a
        · subst i
          simp only [P,if_pos rfl,if_true]
          rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
        · simp only [P,if_neg hi,add_zero]
      calc
        _=∑ i, (P i • x i+(if i=a then t • x a else 0)) := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        _=_ := (Finset.sum_congr rfl (fun i _ ↦ hs i)).symm
    have hrep : (∑ i, P i • x i)=2^(L a) • x a := add_right_cancel (hsum.trans heq)
    exact long_genuine_boundary_not_in_box_of_nonzero L hL g hg E x b hchain a ha hnz hgenuine P hP hrep
  exact not_validTuple_of_long_boundary_axis_collision L hL g E x b hchain a ha hLa t p hp hpa (by omega) heq hg

/-- The high part of a single wide arm makes its own short seed
interval injective, with no other long arm. -/
theorem seed_interval_injective_of_wide_axis
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (T : ℕ) (hcap : n+T ≤ 2^(L a)) :
    Function.Injective (fun t : Fin T ↦ t.val • x a) := by
  classical
  let P := fun (t : Fin T) i ↦ if i=a then n+t.val else 0
  have hp : ∀ t i, P t i < 2^(L i) := by
    intro t i
    by_cases hi : i=a
    · subst i
      simp only [P,if_true]
      have := t.isLt
      omega
    · simp only [P,if_neg hi]
      positivity
  have hs : ∀ t, n ≤ ∑ i, P t i := by
    intro t
    simp only [P,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    omega
  have heval : ∀ t, (∑ i, P t i • x i)=n • x a+t.val • x a := by
    intro t
    simp only [P,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,add_nsmul]
  intro t u he
  have hh := high_box_injective_of_valid_chain_forest L hL g hg E x b hchain (P t) (P u)
    (hp t) (hp u) (hs t) (hs u) (by rw [heval,heval]; exact congrArg (fun z ↦ n • x a+z) he)
  have ha := congrFun hh a
  simp only [P,if_true] at ha
  exact Fin.ext (by omega)

/-- A single wide genuine arm supplies exponentially many distinct
missing residues along its own axis. They pay the full binomial error. -/
theorem wide_boundary_axis_interval_charged_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(2^(L a-4)+1) ≤ Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  have hpow : 2^(L a)=16*2^(L a-4) := by
    rw [show L a=4+(L a-4) by omega,pow_add]
    norm_num
  have hnz := boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha
  let f : Fin (2^(L a-4)+1) → G := fun t ↦ 2^(L a) • x a+t.val • x a
  have hi : Function.Injective f := by
    intro t u he
    exact seed_interval_injective_of_wide_axis L hL g hg E x b hchain a (2^(L a-4)+1)
      (by omega) (add_left_cancel he)
  let F := Finset.univ.image f
  have hcard : F.card=2^(L a-4)+1 := by
    simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact axis_interval_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a
      (by omega) hLa hnz hgenuine t.val (by have := t.isLt; omega) p hp
  have hh := binomial_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain F havoid
  simpa only [hcard] using hh

/-- A single genuine arm whose boundary interval pays the binomial
error forces the binary lower bound, at arbitrary forest rank. -/
theorem binary_card_bound_of_one_genuine_large_arm
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β) ≤ 2^(L a-4)+1)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have hh := wide_boundary_axis_interval_charged_card_bound hn L hL g hg E x b hchain
    (by omega) a ha hLa hgenuine
  omega

/-- Every genuine three-chain forest of length at least 67 satisfies
the binary bound. Its largest arm alone pays the entire packing error. -/
theorem binary_card_bound_of_genuine_three_chain_forest
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hnL : n ≤ 3*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 23 ≤ L j := by omega
  have hcube : n^3 ≤ 2^(L j-4) :=
    (Nat.pow_le_pow_left hnL 3).trans (three_length_cube_le_exponential hLj)
  have hn_cube : n ≤ n^3 := by
    have h1 : 1 ≤ n*n := by nlinarith
    have hh := Nat.mul_le_mul_left n h1
    nlinarith
  have hpow : 2^(L j)=16*2^(L j-4) := by
    rw [show L j=4+(L j-4) by omega,pow_add]
    norm_num
  apply binary_card_bound_of_one_genuine_large_arm (by omega) L hL g hg E x b hchain
    j (by omega) (by omega) _ (hgenuine j)
  simp only [hr,show n+3-1=n+2 by omega]
  exact (three_chain_binomial_le_cube (by omega)).trans (hcube.trans (Nat.le_succ _))

/-- Original critical three-escape data give half descent in every
stratum once the parent length is at least 67. No chain widths, seed
parities, profile shapes or subglobal premise are supplied. -/
theorem admitsValidTuple_half_of_critical_three_escape_large
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,_,E,x,hchain,hend,hgenuine,_,_⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a t
  have hh := binary_card_bound_of_genuine_three_chain_forest (by omega) hr L hL g hg E x b hchain hgen
  rw [ZMod.card] at hh
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  omega

/-- A large critical tuple with no half child has at least FOUR actual
affine-doubling escapes for every shift. The three-escape forest branch
is eliminated, including all formerly separated profile cases. -/
theorem four_le_affine_escape_card_of_large_critical_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) (b : ZMod (2^(s+1)*q)) :
    4 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  classical
  by_contra hnot
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hA : A.card ≤ 3 := by dsimp only [A]; omega
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hnohalf (admitsValidTuple_half_of_critical_three_escape_large hq hn g hg hc A hA b hclosed)

end MinModulus
