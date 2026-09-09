import MinModulus.ForestBinaryDigits

namespace MinModulus
open Finset
open scoped Classical

/-- An actual chain digit is zero precisely when the original subset
contains no coordinate from that chain. -/
theorem forest_subset_digit_zero_iff
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U : Finset (Fin n)) (a : β) :
    (forestSubsetDigits L E U a).val=0 ↔ ∀ j : Fin (L a), E ⟨a,j⟩ ∉ U := by
  classical
  constructor
  · intro hz j hj
    have hmem : j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    have hle := Finset.single_le_sum (f:=fun j : Fin (L a) ↦ 2^j.val)
      (fun _ _ ↦ Nat.zero_le _) hmem
    change (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), 2^j.val)=0 at hz
    have hp : 0 < (2 : ℕ)^j.val := by positivity
    omega
  · intro h
    change (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), 2^j.val)=0
    apply Finset.sum_eq_zero
    intro j hj
    exact False.elim (h j (Finset.mem_filter.mp hj).2)

/-- Chain-separated explicit digits come from disjoint original subsets. -/
theorem forest_subset_disjoint_of_separated_digits
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U V : Finset (Fin n))
    (hsep : ∀ a, (forestSubsetDigits L E U a).val=0 ∨ (forestSubsetDigits L E V a).val=0) :
    Disjoint U V := by
  apply Finset.disjoint_left.mpr
  intro v hvU hvV
  obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective v
  rcases hsep a with h | h
  · exact (forest_subset_digit_zero_iff L E U a).mp h j hvU
  · exact (forest_subset_digit_zero_iff L E V a).mp h j hvV

/-- An actual oriented binary core determines one and only one small
forest profile through its coordinate differences. -/
theorem exists_unique_profile_of_binary_core
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ tupleBinaryCollisionCores g b) :
    ∃! w : ∀ a, Fin (2*(2^(L a)-1)+1), w ∈ forestCollisionProfiles n L x ∧
      ∀ a, (forestSubsetDigits L E uv.1 a).val+(w a).val=
        2^(L a)-1+(forestSubsetDigits L E uv.2 a).val := by
  classical
  obtain ⟨_,he,hcard⟩ := (Finset.mem_filter.mp huv).2
  have heval : (∑ a, (forestSubsetDigits L E uv.1 a).val • x a)=
      ∑ a, (forestSubsetDigits L E uv.2 a).val • x a := by
    rw [forest_subset_digits_sum_eq L g E x b hchain uv.1,
      forest_subset_digits_sum_eq L g E x b hchain uv.2,he]
  have hlt : (∑ a, (forestSubsetDigits L E uv.2 a).val) <
      ∑ a, (forestSubsetDigits L E uv.1 a).val :=
    (forest_subset_digit_weight_lt_iff_card_lt_of_equal_sum L hL g hg E x b hchain uv.2 uv.1 he.symm).mpr hcard
  obtain ⟨w,hw,_,hid⟩ := exists_profile_of_ordered_box_collision L hL g hg E x b hchain
    (forestSubsetDigits L E uv.1) (forestSubsetDigits L E uv.2) heval hlt
  refine ⟨w,⟨hw,hid⟩,?_⟩
  intro v hv
  funext a
  apply Fin.ext
  have h1 := hid a
  have h2 := hv.2 a
  omega

/-- The actual small profile associated with an oriented binary core. -/
noncomputable def binaryCoreForestProfile
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (uv : tupleBinaryCollisionCores g b) : forestCollisionProfiles n L x := by
  classical
  let h := exists_unique_profile_of_binary_core L hL g hg E x b hchain uv.val uv.property
  exact ⟨Classical.choose h,(Classical.choose_spec h).1.1⟩

/-- The core-to-profile map retains every actual coordinate difference. -/
theorem binary_core_forest_profile_coordinate_eq
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (uv : tupleBinaryCollisionCores g b) (a : β) :
    (forestSubsetDigits L E uv.val.1 a).val+
      ((binaryCoreForestProfile L hL g hg E x b hchain uv).val a).val=
        2^(L a)-1+(forestSubsetDigits L E uv.val.2 a).val := by
  exact (Classical.choose_spec
    (exists_unique_profile_of_binary_core L hL g hg E x b hchain uv.val uv.property)).1.2 a

/-- Every actual profile is reached by an oriented binary core through
the explicit subset-to-box digit map. -/
theorem binary_core_forest_profile_surjective
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a) :
    Function.Surjective (binaryCoreForestProfile L hL g hg E x b hchain) := by
  classical
  intro w
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ a, (2^(L a)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro a _
    have hh := Nat.lt_two_pow_self (n:=L a)
    omega
  obtain ⟨p,q,hid,he,hlt,hsep⟩ := exists_chain_separated_pair_of_profile L hdiameter x w.val w.property
  obtain ⟨U,hU⟩ := (forest_subset_digits_bijective L E).2 p
  obtain ⟨V,hV⟩ := (forest_subset_digits_bijective L E).2 q
  have heUV : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)) := by
    rw [← forest_subset_digits_sum_eq L g E x b hchain U,
      ← forest_subset_digits_sum_eq L g E x b hchain V,hU,hV]
    exact he
  have hd : Disjoint U V := forest_subset_disjoint_of_separated_digits L E U V (by
    simpa only [hU,hV] using hsep)
  have hcard : V.card < U.card :=
    (forest_subset_digit_weight_lt_iff_card_lt_of_equal_sum L hL g hg E x b hchain V U heUV.symm).mp
      (by simpa only [hU,hV] using hlt)
  let uv : tupleBinaryCollisionCores g b := ⟨(U,V),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,heUV,hcard⟩⟩
  refine ⟨uv,?_⟩
  apply Subtype.ext
  funext a
  apply Fin.ext
  have h1 := binary_core_forest_profile_coordinate_eq L hL g hg E x b hchain uv a
  change (forestSubsetDigits L E U a).val+
    ((binaryCoreForestProfile L hL g hg E x b hchain uv).val a).val=
      2^(L a)-1+(forestSubsetDigits L E V a).val at h1
  rw [hU,hV] at h1
  have h2 := hid a
  omega

/-- At the valid sharp large-midpoint boundary, the actual core-to-profile
map is a bijection between the four binary cores and the four profiles. -/
theorem binary_core_forest_profile_bijective_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    Function.Bijective (binaryCoreForestProfile L hL g hg E x b hchain) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨binary_core_forest_profile_surjective L hL g hg E x b hchain,?_⟩
  simp only [Fintype.card_coe]
  rw [binary_core_card_eq_four_at_midpoint_boundary g hg b z hmid hlarge hboundary,
    profile_card_eq_four_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary]

end MinModulus
