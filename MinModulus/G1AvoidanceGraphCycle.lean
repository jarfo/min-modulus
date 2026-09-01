/-
# Cycles in the witness-avoidance graph

Put a directed edge `x → y` when a half-witness vanishes at `x` and omits
`y`.  Under failure of common touch, every edge extends to a non-backtracking
edge `y → z`, with `z` distinct from both previous vertices.  Choosing one
extension defines a self-map of the finite edge-state space.  Its orbit must
repeat, and periods one and two are excluded by the non-backtracking rule.
Thus every genuine heavy branch contains a directed avoidance cycle of length
at least three.
-/
import MinModulus.G1GenuineHeavyEscapeIteration

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Directed witness-avoidance edge: one witness vanishes at the source and
omits the target. -/
def WitnessAvoidanceEdge (g : Fin m → G) (h : G)
    (x y : Fin m) : Prop :=
  ∃ c : Fin m → ℤ, Witness g h c ∧ c x = 0 ∧ c y = -1

/-- Global failure of common touch gives a witness vanishing at every
coordinate. -/
theorem exists_witness_zero_at_of_no_commonTouch
    (g : Fin m → G) (h : G)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0) (x : Fin m) :
    ∃ c : Fin m → ℤ, Witness g h c ∧ c x = 0 := by
  by_contra hnone
  apply hno
  refine ⟨x, ?_⟩
  intro c hc
  by_contra hcx
  exact hnone ⟨c, hc, hcx⟩

/-- Every avoidance edge extends non-backtracking under no common touch. -/
theorem witnessAvoidanceEdge_extends
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {x y : Fin m} (hxy : WitnessAvoidanceEdge g h x y) :
    ∃ z : Fin m, z ≠ x ∧ z ≠ y ∧ WitnessAvoidanceEdge g h y z := by
  obtain ⟨e, he, hex, hey⟩ := hxy
  obtain ⟨f, hf, hfy⟩ := exists_witness_zero_at_of_no_commonTouch
    g h hno y
  obtain ⟨z, hzx, hzy, hez, hfz⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh he hf hex hey hfy
  exact ⟨z, hzx, hzy, f, hf, hfy, hfz⟩

/-- Finite state space of directed avoidance edges. -/
def WitnessAvoidanceEdgeState (g : Fin m → G) (h : G) :=
  {p : Fin m × Fin m // WitnessAvoidanceEdge g h p.1 p.2}

noncomputable instance instFintypeWitnessAvoidanceEdgeState
    (g : Fin m → G) (h : G) : Fintype (WitnessAvoidanceEdgeState g h) := by
  classical
  unfold WitnessAvoidanceEdgeState
  infer_instance

/-- Choose one non-backtracking successor edge. -/
noncomputable def witnessAvoidanceEdgeNext
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    WitnessAvoidanceEdgeState g h := by
  let z := Classical.choose
    (witnessAvoidanceEdge_extends g hg hh hno p.property)
  exact ⟨(p.val.2, z),
    (Classical.choose_spec
      (witnessAvoidanceEdge_extends g hg hh hno p.property)).2.2⟩

theorem witnessAvoidanceEdgeNext_fst
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceEdgeNext g hg hh hno p).val.1 = p.val.2 := by
  rfl

theorem witnessAvoidanceEdgeNext_snd_ne_fst
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceEdgeNext g hg hh hno p).val.2 ≠ p.val.1 := by
  exact (Classical.choose_spec
    (witnessAvoidanceEdge_extends g hg hh hno p.property)).1

theorem witnessAvoidanceEdgeNext_snd_ne_snd
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) :
    (witnessAvoidanceEdgeNext g hg hh hno p).val.2 ≠ p.val.2 := by
  exact (Classical.choose_spec
    (witnessAvoidanceEdge_extends g hg hh hno p.property)).2.1

theorem witnessAvoidanceEdgeState_fst_ne_snd
    {g : Fin m → G} {h : G} (p : WitnessAvoidanceEdgeState g h) :
    p.val.1 ≠ p.val.2 := by
  obtain ⟨c, _hc, hx, hy⟩ := p.property
  intro hxy
  rw [hxy] at hx
  omega

/-- Any successor map on avoidance edges which shifts the target to the source
and never immediately backtracks has a repeated orbit segment of length at
least three. -/
theorem exists_nonbacktracking_edgeState_cycle
    (g : Fin m → G) {h : G}
    (T : WitnessAvoidanceEdgeState g h → WitnessAvoidanceEdgeState g h)
    (hfst : ∀ p, (T p).val.1 = p.val.2)
    (hback : ∀ p, (T p).val.2 ≠ p.val.1)
    (p₀ : WitnessAvoidanceEdgeState g h) :
    ∃ i j : ℕ, i < j ∧ 3 ≤ j - i ∧
      T^[i] p₀ = T^[j] p₀ := by
  have hninj : ¬ Function.Injective (fun t : ℕ ↦ T^[t] p₀) :=
    not_injective_infinite_finite _
  obtain ⟨i, j, hijEq, hijNe⟩ := Function.not_injective_iff.mp hninj
  have hcycle_of_lt : ∀ {a b : ℕ}, a < b → T^[a] p₀ = T^[b] p₀ →
      3 ≤ b - a := by
    intro a b hab heq
    let p := T^[a] p₀
    let d := b - a
    have had : a + d = b := Nat.add_sub_of_le hab.le
    have hcycle : T^[d] p = p := by
      calc
        T^[d] p = T^[d + a] p₀ :=
          (Function.iterate_add_apply T d a p₀).symm
        _ = T^[a + d] p₀ := by rw [Nat.add_comm]
        _ = T^[b] p₀ := by rw [had]
        _ = p := heq.symm
    have hdpos : 0 < d := Nat.sub_pos_of_lt hab
    have hd1 : d ≠ 1 := by
      intro hd
      have hfix : T p = p := by
        simpa [hd, Function.iterate_succ_apply] using hcycle
      have hfstEq := congrArg (fun q ↦ q.val.1) hfix
      have hnext := hfst p
      have hne := witnessAvoidanceEdgeState_fst_ne_snd p
      rw [hnext] at hfstEq
      exact hne hfstEq.symm
    have hd2 : d ≠ 2 := by
      intro hd
      have hfix : T (T p) = p := by
        simpa [hd, Function.iterate_succ_apply] using hcycle
      have hfstEq := congrArg (fun q ↦ q.val.1) hfix
      have hnext := hfst (T p)
      have hne := hback p
      rw [hnext] at hfstEq
      exact hne hfstEq
    dsimp [d] at hdpos hd1 hd2 ⊢
    omega
  rcases Nat.lt_or_gt_of_ne hijNe with hij | hji
  · exact ⟨i, j, hij, hcycle_of_lt hij hijEq, hijEq⟩
  · exact ⟨j, i, hji, hcycle_of_lt hji hijEq.symm, hijEq.symm⟩

/-- Every avoidance-edge orbit repeats with period at least three.  This is a
finite directed-cycle certificate, stated at the edge-state level. -/
theorem exists_witnessAvoidanceEdge_cycle
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p₀ : WitnessAvoidanceEdgeState g h) :
    ∃ i j : ℕ, i < j ∧ 3 ≤ j - i ∧
      (witnessAvoidanceEdgeNext g hg hh hno)^[i] p₀ =
        (witnessAvoidanceEdgeNext g hg hh hno)^[j] p₀ :=
  exists_nonbacktracking_edgeState_cycle g
    (witnessAvoidanceEdgeNext g hg hh hno)
    (witnessAvoidanceEdgeNext_fst g hg hh hno)
    (witnessAvoidanceEdgeNext_snd_ne_fst g hg hh hno) p₀

/-- The genuine critical heavy branch contains an avoidance cycle of length
at least three. -/
theorem criticalGenuineHeavyTwoStepEscape_exists_avoidanceCycle
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p₀ : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ i j : ℕ, i < j ∧ 3 ≤ j - i ∧
          (witnessAvoidanceEdgeNext g hg
            (half_add_half (by rw [pow_succ]; ring)) hno)^[i] p₀ =
          (witnessAvoidanceEdgeNext g hg
            (half_add_half (by rw [pow_succ]; ring)) hno)^[j] p₀ := by
  obtain ⟨c, hc, hheavy, hno, hstep⟩ := hescape
  obtain ⟨k, hk⟩ := hheavy
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hh := half_add_half hN
  obtain ⟨b, hcb, _⟩ :=
    exists_common_omission_of_heavyWitness g hg hh hc hk hc
  obtain ⟨e, _f, z, _w, he, _hf, _hzb, _hwb, _hwz,
      _hcz, heb, hez, _hfz, _hew, _hfw⟩ := hstep b hcb
  let p₀ : WitnessAvoidanceEdgeState g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) :=
    ⟨(b, z), e, he, heb, hez⟩
  have hno' : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0 := by
    simpa [CriticalCommonTouched] using hno
  refine ⟨hno', p₀, ?_⟩
  simpa [hN] using exists_witnessAvoidanceEdge_cycle g hg hh hno' p₀

end MinModulus
