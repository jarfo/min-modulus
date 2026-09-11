import MinModulus.PrefixCertificateLinear

namespace MinModulus.PrefixCertificate

def digitStats : ℕ → List ℕ → ℕ × ℕ × Bool
  | _, [] => (0, 0, false)
  | code, x :: p =>
      let tail := digitStats (code / 8) p
      (code % 8 + tail.1, code % 8 * x + tail.2.1,
        decide (code % 8 ≠ 1) || tail.2.2)

theorem decode_length (code k : ℕ) : (decode code k).length = k := by
  induction k generalizing code with
  | zero => rfl
  | succ k ih => simp [decode, ih]

theorem digitStats_spec (code : ℕ) (p : List ℕ) :
    digitStats code p = ((decode code p.length).sum,
      dot (decode code p.length) p,
      decide (decode code p.length ≠ List.replicate p.length 1)) := by
  induction p generalizing code with
  | nil => simp [digitStats, decode, dot]
  | cons x p ih =>
    simp [digitStats, decode, dot, ih, List.replicate_succ]

def hitsPacked (N : ℕ) (p : List ℕ) (code : ℕ) : Bool :=
  let stats := digitStats code p
  decide (stats.1 = p.length ∧ stats.2.2 = true ∧ stats.2.1 % N = p.sum % N)

theorem hits_eq_hitsPacked (N : ℕ) (p : List ℕ) (code : ℕ) :
    hits N p (decode code p.length) = hitsPacked N p code := by
  simp [hits, hitsPacked, digitStats_spec, decode_length]

def verifyPacked (N : ℕ) : ℕ → List ℕ → ℕ → Certificate → Bool
  | _, p, _, .stop code => hitsPacked N p code
  | 0, _, _, .branch _ => false
  | k + 1, p, next, .branch children =>
      decide (children.length = N - next) &&
        (children.zipIdx next).all fun (child, x) ↦
          verifyPacked N k (p ++ [x]) (x + 1) child

theorem verifyLinear_eq_verifyPacked (N k : ℕ) (p : List ℕ) (next : ℕ)
    (cert : Certificate) : verifyLinear N k p next cert = verifyPacked N k p next cert := by
  induction k generalizing p next cert with
  | zero => cases cert <;> simp [verifyLinear, verifyPacked, hits_eq_hitsPacked]
  | succ k ih =>
    cases cert <;> simp only [verifyLinear, verifyPacked, hits_eq_hitsPacked, ih]

theorem not_validTuple_of_verifyPacked {n N : ℕ} [NeZero N]
    (cert : Certificate) (hc : verifyPacked N n [0] 1 cert = true)
    (g : Fin (n + 1) → ZMod N) : ¬ ValidTuple g := by
  apply not_validTuple_of_verifyLinear cert _ g
  simpa only [verifyLinear_eq_verifyPacked] using hc

end MinModulus.PrefixCertificate
