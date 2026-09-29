import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha1

/-!
# SHA-1: the hash value in memory

Untrusted: everything here is checked by Lean. The hash value as consecutive
32-bit words at an address (`stateAt`, `writeState`), and offsets into a
region, independently of any target.
-/

namespace VG.Proof.Sha1.StateMem

open VG
open VG.Spec.Sha1 (HashValue Word stateAt)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 5) (hk : k < 5) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 5) (hk : k < 5)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 5) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-- Five 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (4 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (4 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (4 * 3)) v[3]).writeW
    (p + BitVec.ofNat 64 (4 * 4)) v[4])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

end VG.Proof.Sha1.StateMem
