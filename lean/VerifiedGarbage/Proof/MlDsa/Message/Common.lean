import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA, `sign_message` and `verify_message`: what every target's proof uses

Untrusted: everything here is checked by Lean. Regions at an offset within
others (`Within`); the formatted message `0 ‖ |ctx| ‖ ctx ‖ M` of a context
string of at most 255 bytes (`formatMessage_some`); and the bytes behind
equal leakage (`leakBytes_inj`).
-/

namespace VG.Proof.MlDsa.Message

open VG
open VG.Spec.MlDsa

/-! ## Regions within others -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem Within.trans {r R R' : Region} (h : Within r R) (h' : Within R R') : Within r R' := by
  obtain ⟨o, hb, hl⟩ := h
  obtain ⟨o', hb', hl'⟩ := h'
  exact ⟨o' + o, by rw [hb, hb', BitVec.add_assoc, BitVec.ofNat_add_ofNat], by omega⟩

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_self (r : Region) : Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

/-! ## Addresses -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem toNat_add_ofNat {x : Addr} {a : Nat} (h : x.toNat + a < 2 ^ 64) :
    (x + BitVec.ofNat 64 a).toNat = x.toNat + a := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt h]

/-! ## The formatted message -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes, List.range, List.range.loop]

/-- A context string of at most 255 bytes formats the message. -/
theorem formatMessage_some {ctx M : List Byte} (h : ctx.length < 256) :
    formatMessage ctx M = some ([0, BitVec.ofNat 8 ctx.length] ++ ctx ++ M) := by
  simp only [formatMessage, show ¬ ctx.length > 255 by omega, ite_false, integerToBytes_one]
  rfl

theorem formatMessage_none {ctx M : List Byte} (h : 256 ≤ ctx.length) : formatMessage ctx M = none := by
  simp only [formatMessage, show ctx.length > 255 by omega, ite_true]

/-! ## Leakage -/

theorem leakBytes_inj : ∀ {l₁ l₂ : List Byte}, leakBytes l₁ = leakBytes l₂ → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]

/-- Four pieces of the given lengths, from their leakage. -/
theorem leak4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length) (h : leakBytes (a ++ b ++ c ++ d) = leakBytes (a' ++ b' ++ c' ++ d')) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have e := leakBytes_inj h
  obtain ⟨e, e₄⟩ := List.append_inj e (by simp only [List.length_append]; omega)
  obtain ⟨e, e₃⟩ := List.append_inj e (by simp only [List.length_append]; omega)
  obtain ⟨e₁, e₂⟩ := List.append_inj e ha
  exact ⟨e₁, e₂, e₃, e₄⟩

end VG.Proof.MlDsa.Message
