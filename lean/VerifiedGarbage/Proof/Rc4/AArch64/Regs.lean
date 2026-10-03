import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Impl.Rc4.AArch64

/-!
# The table registers

Byte `k` of the table registers (`tbyte`) is lane `k % 16` of
`v(16 + k / 16)`. A four-register `tbl`/`tbx` from `v16`, `v20`, `v24` or
`v28` reads the bytes of one quarter of it.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Byte `k` of the table registers. -/
def tbyte (v : VReg → BitVec 128) (k : Nat) : BitVec 8 := vbyte (v (treg (k / 16))) (k % 16)

theorem treg_quarter : ∀ q < 4, ∀ k < 4,
    Nat.repeat VReg.succ k ([VReg.v16, .v20, .v24, .v28].getD q .v16) = treg (4 * q + k) := by
  decide

theorem treg_inj : ∀ a < 16, ∀ b < 16, treg a = treg b → a = b := by decide

theorem treg_ne : ∀ a < 16, treg a ≠ .v0 ∧ treg a ≠ .v1 ∧ treg a ≠ .v2 ∧ treg a ≠ .v3 ∧
    treg a ≠ .v4 ∧ treg a ≠ .v5 ∧ treg a ≠ .v6 ∧ treg a ≠ .v7 ∧ treg a ≠ .v8 ∧ treg a ≠ .v9 ∧
    treg a ≠ .v10 ∧ treg a ≠ .v11 ∧ treg a ≠ .v12 ∧ treg a ≠ .v13 ∧ treg a ≠ .v14 := by decide

/-- A register outside the table. -/
def NotTable (r : VReg) : Prop := ∀ a < 16, treg a ≠ r

instance (r : VReg) : Decidable (NotTable r) := inferInstanceAs (Decidable (∀ a < 16, treg a ≠ r))

theorem treg_of_ge {n : Nat} (h : 16 ≤ n) : treg n = .v16 := by
  simp only [treg, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem NotTable.ne {r : VReg} (h : NotTable r) (n : Nat) : treg n ≠ r := by
  by_cases hn : n < 16
  · exact h n hn
  · rw [treg_of_ge (by omega)]; exact h 0 (by decide)

theorem tbyte_congr {v w : VReg → BitVec 128} (h : ∀ a < 16, v (treg a) = w (treg a)) {k : Nat}
    (hk : k < 256) : tbyte v k = tbyte w k := by
  simp only [tbyte, h _ (by omega : k / 16 < 16)]

/-- The table byte that a quarter's `tbl` reads, for an index in the quarter. -/
theorem tableByte_quarter (v : VReg → BitVec 128) {q : Nat} (hq : q < 4) {idx : Nat} (hi : idx < 64) :
    tableByte v ([VReg.v16, .v20, .v24, .v28].getD q .v16) idx = tbyte v (64 * q + idx) := by
  simp only [tableByte, tbyte, treg_quarter q hq _ (by omega : idx / 16 < 4)]
  rw [show (64 * q + idx) / 16 = 4 * q + idx / 16 by omega, show (64 * q + idx) % 16 = idx % 16 by omega]

/-- The quarter of each byte, and its index there. -/
theorem xor_quarter : ∀ x < 256, ∀ q < 4,
    (x ^^^ 64 * q < 64 ↔ x / 64 = q) ∧ (x / 64 = q → x ^^^ 64 * q = x - 64 * q) := by
  decide +kernel

/-! ## The constants -/

/-- The lane numbers of quarter `q`: `16 q`, …, `16 q + 15`. -/
def laneNums (q : Nat) : BitVec 128 := ofVBytes fun e => BitVec.ofNat 8 (16 * q + e)

structure Consts (s : State) : Prop where
  lns : ∀ q < 4, s.v (VG.Impl.Rc4.AArch64.lanes q) = laneNums q
  c64 : s.v c64 = bc 64
  c128 : s.v c128 = bc 128

theorem Consts.congr {s s' : State} (h : Consts s)
    (hv : ∀ r, r = .v8 ∨ r = .v9 ∨ r = .v10 ∨ r = .v11 ∨ r = .v12 ∨ r = .v13 → s'.v r = s.v r) :
    Consts s' where
  lns q hq := by
    have : VG.Impl.Rc4.AArch64.lanes q = .v8 ∨ VG.Impl.Rc4.AArch64.lanes q = .v9 ∨
        VG.Impl.Rc4.AArch64.lanes q = .v10 ∨ VG.Impl.Rc4.AArch64.lanes q = .v11 := by
      revert q; decide
    rw [hv _ (by rcases this with h | h | h | h <;> simp [h])]; exact h.lns q hq
  c64 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c64])]; exact h.c64
  c128 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c128])]; exact h.c128

end VG.Proof.Rc4.AArch64
