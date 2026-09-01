/-
# Minimal witness transversals and external escape

The heavy root's omission set is a transversal of all half-witnesses.  Shrink
it to a cardinality-minimal subtransversal.  Every vertex of a minimal
transversal has a private witness whose only omission inside the transversal
is that vertex.  Pairing this private witness with the heavy root's avoiding
escape forces, by witness combination, a shared omission outside the minimal
transversal.

This creates one certified external omission layer at every vertex of the
minimal deletion set, the first mechanism available to pay for the extra
dimensions lost by transversal deletion.
-/
import MinModulus.G1WitnessTransversalDescent

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A finite set of coordinates meeting the omission set of every witness at
`h`. -/
def WitnessOmissionTransversal
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → ℤ, Witness g h c →
    ∃ i : Fin m, i ∈ B ∧ c i = -1

/-- An inclusion-minimal witness omission transversal, expressed by failure
after erasing any one of its vertices. -/
def MinimalWitnessOmissionTransversal
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) : Prop :=
  WitnessOmissionTransversal g h B ∧
    ∀ b ∈ B, ¬ WitnessOmissionTransversal g h (B.erase b)

/-- Every finite witness omission transversal contains a cardinality-minimal,
hence inclusion-minimal, subtransversal. -/
theorem exists_minimalWitnessOmissionTransversal_subset
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hB : WitnessOmissionTransversal g h B) :
    ∃ B₀ : Finset (Fin m), B₀ ⊆ B ∧
      MinimalWitnessOmissionTransversal g h B₀ := by
  classical
  let F : Finset (Finset (Fin m)) :=
    B.powerset.filter (WitnessOmissionTransversal g h)
  have hF : F.Nonempty := by
    refine ⟨B, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Subset.rfl), hB⟩
  obtain ⟨B₀, hB₀F, hmin⟩ := Finset.exists_min_image F Finset.card hF
  have hB₀mem := Finset.mem_filter.mp hB₀F
  refine ⟨B₀, Finset.mem_powerset.mp hB₀mem.1, hB₀mem.2, ?_⟩
  intro b hb hErase
  have hEraseSub : B₀.erase b ⊆ B :=
    (Finset.erase_subset b B₀).trans (Finset.mem_powerset.mp hB₀mem.1)
  have hEraseF : B₀.erase b ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hEraseSub, hErase⟩
  have hle := hmin (B₀.erase b) hEraseF
  have hlt := Finset.card_erase_lt_of_mem hb
  omega

/-- Every vertex of a minimal transversal has a private witness: that witness
omits the vertex and no other coordinate in the transversal. -/
theorem exists_private_witness_of_minimalTransversal
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessOmissionTransversal g h B)
    {b : Fin m} (hb : b ∈ B) :
    ∃ d : Fin m → ℤ, Witness g h d ∧ d b = -1 ∧
      ∀ a ∈ B, a ≠ b → d a ≠ -1 := by
  classical
  have hnot := hmin.2 b hb
  unfold WitnessOmissionTransversal at hnot
  push Not at hnot
  obtain ⟨d, hd, havoid⟩ := hnot
  obtain ⟨i, hiB, hdi⟩ := hmin.1 d hd
  have hib : i = b := by
    by_contra hne
    exact (havoid i (Finset.mem_erase.mpr ⟨hne, hiB⟩)) hdi
  subst i
  refine ⟨d, hd, hdi, ?_⟩
  intro a ha hab
  exact havoid a (Finset.mem_erase.mpr ⟨hab, ha⟩)

/-- A private witness at `b` and any witness avoiding `b` must share an
omission outside the minimal transversal.  Otherwise witness combination
would negate the private witness, contradicting the avoiding zero at `b`. -/
theorem exists_external_common_omission_of_minimalTransversal
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessOmissionTransversal g h B)
    {b : Fin m} (hb : b ∈ B) {e : Fin m → ℤ}
    (he : Witness g h e) (heb : e b = 0) :
    ∃ d : Fin m → ℤ, ∃ z : Fin m,
      Witness g h d ∧ d b = -1 ∧ z ∉ B ∧ d z = -1 ∧ e z = -1 := by
  obtain ⟨d, hd, hdb, hdprivate⟩ :=
    exists_private_witness_of_minimalTransversal g h hmin hb
  have hcommon : ∃ z : Fin m, d z = -1 ∧ e z = -1 := by
    by_contra hnone
    have hshare : ∀ i, ¬ (d i = -1 ∧ e i = -1) := by
      intro i hi
      exact hnone ⟨i, hi⟩
    have hneg := witness_combination g hg hh hd he hshare
    have hcoeff := congrFun hneg b
    simp only [Pi.neg_apply, hdb] at hcoeff
    omega
  obtain ⟨z, hdz, hez⟩ := hcommon
  have hznot : z ∉ B := by
    intro hzB
    by_cases hzb : z = b
    · subst z
      omega
    · exact (hdprivate z hzB hzb) hdz
  exact ⟨d, z, hd, hdb, hznot, hdz, hez⟩

/-- Cyclic descent from an arbitrary omission transversal `B`: delete `B`
and retain its complement. -/
theorem exists_validTuple_half_of_omissionTransversal
    {N M : ℕ} (hN : N = 2 * M) (hM : 0 < M)
    {g : Fin m → ZMod N} (hg : ValidTuple g)
    (B : Finset (Fin m)) (hB : WitnessOmissionTransversal g (M : ZMod N) B) :
    AdmitsValidTuple (m - B.card) M := by
  let R : Finset (Fin m) := Finset.univ \ B
  let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
  have hhit : ∀ c : Fin m → ℤ, Witness g (M : ZMod N) c →
      ∃ j : Fin m, (∀ i : Fin R.card, e i ≠ j) ∧ c j ≠ 0 := by
    intro c hc
    obtain ⟨j, hjB, hcj⟩ := hB c hc
    refine ⟨j, ?_, by omega⟩
    intro i hei
    have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
    exact (Finset.mem_sdiff.mp heiR).2 (by simpa [hei] using hjB)
  have hvalidR : AdmitsValidTuple R.card M :=
    exists_validTuple_half_of_witness_transversal hN hM hg e hhit
  have hRcard : R.card = m - B.card := by
    simp [R, Finset.card_sdiff_of_subset (Finset.subset_univ B)]
  simpa [hRcard] using hvalidR

/-- Ordered minimal-transversal/external-omission pairs certified by a
private witness and a witness avoiding the transversal vertex. -/
noncomputable def minimalTransversalExternalEscapePairs
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) :
    Finset (Fin m × Fin m) := by
  classical
  exact (B ×ˢ (Finset.univ \ B)).filter (fun p ↦
    ∃ e d : Fin m → ℤ,
      Witness g h e ∧ Witness g h d ∧
        e p.1 = 0 ∧ d p.1 = -1 ∧ d p.2 = -1 ∧ e p.2 = -1)

@[simp] theorem mem_minimalTransversalExternalEscapePairs_iff
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) (b z : Fin m) :
    (b, z) ∈ minimalTransversalExternalEscapePairs g h B ↔
      b ∈ B ∧ z ∉ B ∧
        ∃ e d : Fin m → ℤ,
          Witness g h e ∧ Witness g h d ∧
            e b = 0 ∧ d b = -1 ∧ d z = -1 ∧ e z = -1 := by
  classical
  simp [minimalTransversalExternalEscapePairs, and_assoc]

/-- If every transversal vertex has an avoiding witness, the external escape
incidences project onto the entire minimal transversal. -/
theorem image_fst_minimalTransversalExternalEscapePairs_eq
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessOmissionTransversal g h B)
    (havoid : ∀ b ∈ B, ∃ e : Fin m → ℤ,
      Witness g h e ∧ e b = 0) :
    (minimalTransversalExternalEscapePairs g h B).image Prod.fst = B := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hb
    have hp' := (mem_minimalTransversalExternalEscapePairs_iff
      g h B p.1 p.2).mp hp
    simpa [← hpb] using hp'.1
  · intro hb
    obtain ⟨e, he, heb⟩ := havoid b hb
    obtain ⟨d, z, hd, hdb, hznot, hdz, hez⟩ :=
      exists_external_common_omission_of_minimalTransversal
        g hg hh hmin hb he heb
    apply Finset.mem_image.mpr
    refine ⟨(b, z), ?_, rfl⟩
    exact (mem_minimalTransversalExternalEscapePairs_iff
      g h B b z).mpr ⟨hb, hznot, e, d, he, hd, heb, hdb, hdz, hez⟩

/-- Counted external-escape consequence: at least one distinct ordered
external incidence is present for every minimal-transversal vertex. -/
theorem card_le_card_minimalTransversalExternalEscapePairs
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessOmissionTransversal g h B)
    (havoid : ∀ b ∈ B, ∃ e : Fin m → ℤ,
      Witness g h e ∧ e b = 0) :
    B.card ≤ (minimalTransversalExternalEscapePairs g h B).card := by
  let P := minimalTransversalExternalEscapePairs g h B
  have hproj : P.image Prod.fst = B :=
    image_fst_minimalTransversalExternalEscapePairs_eq
      g hg hh hmin havoid
  calc
    B.card = (P.image Prod.fst).card :=
      (congrArg Finset.card hproj).symm
    _ ≤ P.card := Finset.card_image_le

/-- The fully sharpened heavy branch: it has a minimal omission transversal
of size at least two, deleting that transversal is valid at half modulus, and
every transversal vertex sprouts a private/avoiding witness pair with a
shared omission outside the transversal. -/
def CriticalHeavyMinimalTransversalPackage
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ∃ B : Finset (Fin (n + 1)),
    MinimalWitnessOmissionTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B ∧
    2 ≤ B.card ∧
    AdmitsValidTuple (n + 1 - B.card) (2 ^ s * q) ∧
    B.card ≤ (minimalTransversalExternalEscapePairs g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B).card ∧
    ∀ b ∈ B, ∃ e d : Fin (n + 1) → ℤ, ∃ z : Fin (n + 1),
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) e ∧
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) d ∧
      e b = 0 ∧ d b = -1 ∧ z ∉ B ∧ d z = -1 ∧ e z = -1

/-- Every critical heavy omission escape yields the minimal-transversal
package. -/
theorem criticalHeavyMinimalTransversalPackage_of_escape
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalHeavyOmissionEscape g) :
    CriticalHeavyMinimalTransversalPackage g := by
  obtain ⟨c, hc, _hheavy, htrans, hesc⟩ := hescape
  let Broot : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i ↦ c i = -1)
  have hBroot : WitnessOmissionTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) Broot := by
    intro d hd
    obtain ⟨i, hci, hdi⟩ := htrans d hd
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩, hdi⟩
  obtain ⟨B, hBsub, hBmin⟩ :=
    exists_minimalWitnessOmissionTransversal_subset
      g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hBroot
  have havoid : ∀ b ∈ B, ∃ e : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) e ∧
        e b = 0 := by
    intro b hbB
    have hcb : c b = -1 :=
      (Finset.mem_filter.mp (hBsub hbB)).2
    obtain ⟨e, he, heb, _a, _hab, _hca, _hea⟩ := hesc b hcb
    exact ⟨e, he, heb⟩
  have hBtwo : 2 ≤ B.card := by
    obtain ⟨b, hbB, _⟩ := hBmin.1 c hc
    obtain ⟨e, he, heb⟩ := havoid b hbB
    obtain ⟨a, haB, hea⟩ := hBmin.1 e he
    have hab : a ≠ b := by
      intro hab
      subst a
      omega
    have hone : 1 < B.card :=
      Finset.one_lt_card.mpr ⟨a, haB, b, hbB, hab⟩
    omega
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hdelete : AdmitsValidTuple (n + 1 - B.card) (2 ^ s * q) :=
    exists_validTuple_half_of_omissionTransversal hN hM hg B hBmin.1
  have hincidence : B.card ≤
      (minimalTransversalExternalEscapePairs g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B).card :=
    card_le_card_minimalTransversalExternalEscapePairs
      g hg (half_add_half hN) hBmin havoid
  refine ⟨B, hBmin, hBtwo, hdelete, hincidence, ?_⟩
  intro b hbB
  obtain ⟨e, he, heb⟩ := havoid b hbB
  obtain ⟨d, z, hd, hdb, hznot, hdz, hez⟩ :=
    exists_external_common_omission_of_minimalTransversal
      g hg (half_add_half hN) hBmin hbB he heb
  exact ⟨e, d, z, he, hd, heb, hdb, hznot, hdz, hez⟩

end MinModulus
