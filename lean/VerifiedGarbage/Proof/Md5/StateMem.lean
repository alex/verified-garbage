import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Md5

/-!
# MD5: the hash value in memory

The hash value as consecutive 32-bit words at an address (`stateAt`,
`writeState`), and offsets into a region, independently of any target.
-/

namespace VG.Proof.Md5.StateMem

open VG
open VG.Spec.Md5 (HashValue Word stateAt)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 4) (hk : k < 4) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 :=
  Offset.sep p (by omega) (by omega) (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 4) (hk : k < 4)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 4) → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 4) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-- Four 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (4 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (4 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (4 * 3)) v[3])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

end VG.Proof.Md5.StateMem
