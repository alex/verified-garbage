import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-DSA: bytes written one at a time, for every target

Untrusted: everything here is checked by Lean. `Written m m' o c v`: `m'` is
`m` with the `c` bytes at `o` replaced by `v 0, …, v (c - 1)`, built one
byte store at a time (`Written.nil`, `Written.snoc`), and how a loop that
writes its output `c` bytes at a time extends what it has written
(`Written.step`). (The same as ML-KEM's on x86-64, which a module of
another target may not import, with distances computed by `VG.Offset`.)
-/

namespace VG.Proof.MlDsa.Pack

open VG.WriteBytes (writeW8_apply)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- `m'` is `m` with the `c` bytes at `o` replaced by `v 0, …, v (c - 1)`. -/
def Written (m m' : Mem) (o : Addr) (c : Nat) (v : Nat → Byte) : Prop :=
  ∀ x, m' x = if (x - o).toNat < c then v (x - o).toNat else m x

theorem Written.nil (m : Mem) (o : Addr) (v : Nat → Byte) : Written m m o 0 v := fun x => by
  rw [ifn (Nat.not_lt_zero _)]

theorem Written.snoc {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : Written m m' o c v)
    (hc : c < 2 ^ 64) (b : Byte) :
    Written m (m'.writeW (o + BitVec.ofNat 64 c) b) o (c + 1) fun j => if j = c then b else v j := by
  intro x
  rw [writeW8_apply, h x]
  by_cases hx : x = o + BitVec.ofNat 64 c
  · subst hx
    rw [ifp rfl, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, ifp (by omega)]
    dsimp only
    rw [ifp rfl]
  · have : (x - o).toNat ≠ c := fun e => hx (by
      rw [← BitVec.sub_add_cancel x o, BitVec.add_comm]
      exact congrArg (o + ·) (BitVec.eq_of_toNat_eq (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc])))
    rw [ifn hx]
    by_cases hl : (x - o).toNat < c
    · rw [ifp hl, ifp (by omega)]
      dsimp only
      rw [ifn this]
    · rw [ifn hl, ifn (by omega)]

/-- Writing `c` bytes within the region `R`. -/
theorem Written.frame {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : Written m m' o c v)
    {R : Region} (hR : R.Contains o c) : Frame [R] m m' := by
  intro x hx
  rw [h x]
  split
  · rename_i hlt
    exact absurd (hR.byte hlt) (hx R (List.mem_singleton_self _))
  · rfl

theorem Written.congr {m m' : Mem} {o : Addr} {c : Nat} {v v' : Nat → Byte} (h : Written m m' o c v)
    (hv : ∀ j < c, v j = v' j) : Written m m' o c v' := by
  intro x
  rw [h x]
  split
  · rename_i hl; exact hv _ hl
  · rfl

/-- A loop that has written the first `a` bytes of its output, `val 0, …,
val (a - 1)`, then writes the next `c`. -/
theorem Written.extend {m m' : Mem} {out : Addr} {a c : Nat} {val : Nat → Byte}
    (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hlen : a + c < 2 ^ 64) :
    ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k := by
  intro k hk
  rw [hw]
  by_cases h : k < a
  · have hc : 0 < c ∨ c = 0 := by omega
    rcases hc with hc | hc
    · rw [ifn (by
        rw [Offset.add_sub_add_left]
        exact Offset.not_lt_sub_ofNat (.inl h) (by omega) hc (by omega)), hd k h]
    · rw [ifn (by omega), hd k h]
  · rw [Offset.sub_toNat out (by omega) (by omega), ifp (by omega)]
    exact congrArg val (by omega)

/-- The loop's output so far, and the frame, one step further. -/
theorem Written.step {m₀ m m' : Mem} {out : Addr} {a c len : Nat} {val : Nat → Byte}
    (hf : Frame [⟨out, len⟩] m₀ m) (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hac : a + c ≤ len)
    (hlen : len < 2 ^ 64) :
    Frame [⟨out, len⟩] m₀ m' ∧ ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k :=
  ⟨hf.trans (hw.frame (Offset.contains_base out hac (by omega))), Written.extend hd hw (by omega)⟩

end VG.Proof.MlDsa.Pack
