/-
# Witness algebra on avoidance cycles

The coordinate cycle from `G1AvoidanceGraphCycle` can be strengthened by
retaining the witness which creates every successor.  At a transition

    x → y → z

the retained witness vanishes at `x` and omits both `y` and `z`.  Choosing
such extensions gives another non-backtracking self-map of the finite edge
space, hence a periodic orbit of length at least three carrying this local
coefficient pattern at every step.
-/
import MinModulus.G1AvoidanceGraphCycle

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- All witness data used to extend one avoidance edge.  The current witness
omits both the old and new targets, while the successor witness vanishes at
the old target and omits the new one. -/
structure WitnessAvoidanceExtension (g : Fin m → G) (h : G)
    (p : WitnessAvoidanceEdgeState g h) where
  nextTarget : Fin m
  currentWitness : Fin m → ℤ
  successorWitness : Fin m → ℤ
  current_isWitness : Witness g h currentWitness
  successor_isWitness : Witness g h successorWitness
  nextTarget_ne_source : nextTarget ≠ p.val.1
  nextTarget_ne_target : nextTarget ≠ p.val.2
  current_zero_source : currentWitness p.val.1 = 0
  current_omit_target : currentWitness p.val.2 = -1
  successor_zero_target : successorWitness p.val.2 = 0
  current_omit_nextTarget : currentWitness nextTarget = -1
  successor_omit_nextTarget : successorWitness nextTarget = -1

/-- Every avoidance edge has a witness-retaining non-backtracking extension
under failure of common touch. -/
theorem exists_witnessAvoidanceExtension
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    Nonempty (WitnessAvoidanceExtension g h p) := by
  obtain ⟨e, he, hex, hey⟩ := p.property
  obtain ⟨f, hf, hfy⟩ := exists_witness_zero_at_of_no_commonTouch
    g h hno p.val.2
  obtain ⟨z, hzx, hzy, hez, hfz⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh he hf hex hey hfy
  exact ⟨{
    nextTarget := z
    currentWitness := e
    successorWitness := f
    current_isWitness := he
    successor_isWitness := hf
    nextTarget_ne_source := hzx
    nextTarget_ne_target := hzy
    current_zero_source := hex
    current_omit_target := hey
    successor_zero_target := hfy
    current_omit_nextTarget := hez
    successor_omit_nextTarget := hfz
  }⟩

/-- A fixed choice of witness-retaining extension at every edge state. -/
noncomputable def witnessAvoidanceExtensionChoice
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    WitnessAvoidanceExtension g h p :=
  Classical.choice (exists_witnessAvoidanceExtension g hg hh hno p)

/-- The successor edge selected together with the bridge-witness data. -/
noncomputable def witnessAvoidanceBridgeNext
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    WitnessAvoidanceEdgeState g h := by
  let E := witnessAvoidanceExtensionChoice g hg hh hno p
  exact ⟨(p.val.2, E.nextTarget), E.successorWitness,
    E.successor_isWitness, E.successor_zero_target,
    E.successor_omit_nextTarget⟩

theorem witnessAvoidanceBridgeNext_fst
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceBridgeNext g hg hh hno p).val.1 = p.val.2 := by
  rfl

theorem witnessAvoidanceBridgeNext_snd_ne_fst
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceBridgeNext g hg hh hno p).val.2 ≠ p.val.1 := by
  exact (witnessAvoidanceExtensionChoice g hg hh hno p).nextTarget_ne_source

theorem witnessAvoidanceBridgeNext_snd_ne_snd
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceBridgeNext g hg hh hno p).val.2 ≠ p.val.2 := by
  exact (witnessAvoidanceExtensionChoice g hg hh hno p).nextTarget_ne_target

/-- The chosen current witness vanishes at the source and omits both the
current target and the next target. -/
theorem witnessAvoidanceBridgeNext_has_doubleOmission
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    ∃ c : Fin m → ℤ, Witness g h c ∧
      c p.val.1 = 0 ∧ c p.val.2 = -1 ∧
      c (witnessAvoidanceBridgeNext g hg hh hno p).val.2 = -1 := by
  let E := witnessAvoidanceExtensionChoice g hg hh hno p
  refine ⟨E.currentWitness, E.current_isWitness,
    E.current_zero_source, E.current_omit_target, ?_⟩
  exact E.current_omit_nextTarget

/-- A periodic bridge orbit carries a double-omission witness at every one of
its iterated edge states. -/
def IsWitnessAvoidanceBridgeCycle
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  3 ≤ d ∧
    (witnessAvoidanceBridgeNext g hg hh hno)^[d] p = p ∧
    ∀ k : ℕ, ∃ c : Fin m → ℤ, Witness g h c ∧
      c (((witnessAvoidanceBridgeNext g hg hh hno)^[k] p).val.1) = 0 ∧
      c (((witnessAvoidanceBridgeNext g hg hh hno)^[k] p).val.2) = -1 ∧
      c ((witnessAvoidanceBridgeNext g hg hh hno
        ((witnessAvoidanceBridgeNext g hg hh hno)^[k] p)).val.2) = -1

/-- Every initial avoidance edge enters a periodic bridge orbit of length at
least three, with the local `0,-1,-1` witness pattern retained at every
iterate. -/
theorem exists_witnessAvoidanceBridgeCycle
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p₀ : WitnessAvoidanceEdgeState g h) :
    ∃ p : WitnessAvoidanceEdgeState g h, ∃ d : ℕ,
      IsWitnessAvoidanceBridgeCycle g hg hh hno p d := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  obtain ⟨i, j, hij, hd, hijEq⟩ :=
    exists_nonbacktracking_edgeState_cycle g T
      (witnessAvoidanceBridgeNext_fst g hg hh hno)
      (witnessAvoidanceBridgeNext_snd_ne_fst g hg hh hno) p₀
  let p := T^[i] p₀
  let d := j - i
  have had : i + d = j := Nat.add_sub_of_le hij.le
  have hperiod : T^[d] p = p := by
    calc
      T^[d] p = T^[d + i] p₀ :=
        (Function.iterate_add_apply T d i p₀).symm
      _ = T^[i + d] p₀ := by rw [Nat.add_comm]
      _ = T^[j] p₀ := by rw [had]
      _ = p := hijEq.symm
  refine ⟨p, d, hd, hperiod, ?_⟩
  intro k
  exact witnessAvoidanceBridgeNext_has_doubleOmission g hg hh hno (T^[k] p)

/-- The genuine critical heavy branch contains a periodic avoidance cycle of
length at least three whose every step carries a `0,-1,-1` bridge witness. -/
theorem criticalGenuineHeavyTwoStepEscape_exists_bridgeCycle
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d := by
  obtain ⟨c, hc, hheavy, hno, _hstep⟩ := hescape
  obtain ⟨k, hk⟩ := hheavy
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hh := half_add_half hN
  obtain ⟨b, hcb, _⟩ :=
    exists_common_omission_of_heavyWitness g hg hh hc hk hc
  have hno' : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0 := by
    simpa [CriticalCommonTouched] using hno
  obtain ⟨e, he, heb⟩ := exists_witness_zero_at_of_no_commonTouch
    g _ hno' b
  obtain ⟨z, _hcz, hez⟩ :=
    exists_common_omission_of_heavyWitness g hg hh hc hk he
  let p₀ : WitnessAvoidanceEdgeState g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) :=
    ⟨(b, z), e, he, heb, hez⟩
  obtain ⟨p, d, hp⟩ := exists_witnessAvoidanceBridgeCycle g hg hh hno' p₀
  refine ⟨hno', p, d, ?_⟩
  simpa [hN] using hp

end MinModulus
