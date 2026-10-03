import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

/-!
# The constants

`constants_ok`: the lane numbers 0–63 in `v8`–`v11`, and 64 and 128 in
every byte of `v12` and `v13`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem lanes0 (v : BitVec 128) :
    setLane (setLane v 64 0 0x0706050403020100#64) 64 1 0x0f0e0d0c0b0a0908#64 = laneNums 0 := by
  rw [setLane_two]
  decide

theorem lanes_next (q : Nat) :
    VArr.b16.map2 (fun _ x y => x + y) (laneNums q) (bc 16) = laneNums (q + 1) :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, laneNums, laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega

theorem dup_b16 (s : State) (r : Reg) (b : Nat) (h : s.gpr r = BitVec.ofNat 64 b) :
    (ofVBytes fun _ => (s.gpr r).setWidth 8) = bc (BitVec.ofNat 8 b) := by
  rw [h]; congr; funext _
  apply BitVec.eq_of_toNat_eq; simp

theorem bc_lit (b : BitVec 8) : (ofVBytes fun _ => b) = bc b := rfl

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t =>
      t.gpr r = v ∧ (∀ g, g ≠ r → t.gpr g = s.gpr g) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.of_runBlock ⟨_, rfl, ?_, fun g hg => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, hg]

theorem constants_ok (s : State) :
    WP isa (.block constants) s fun t =>
      Consts t ∧ (∀ v, v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 → v ≠ .v12 → v ≠ .v13 →
        t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold constants
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const64_ok s .x6 _) fun a ⟨a6, ag, av, am, ard, awr, asp⟩ => ?_
  refine WP.mono (const64_ok a .x7 _) fun b ⟨b7, bg, bv, bm, brd, bwr, bsp⟩ => ?_
  have b6 : b.gpr .x6 = 0x0706050403020100#64 := by rw [bg _ (by decide), a6]; rfl
  have b7' : b.gpr .x7 = 0x0f0e0d0c0b0a0908#64 := by rw [b7]; rfl
  have l0 : lanes 0 = .v8 := rfl
  have l1 : lanes 1 = .v9 := rfl
  have l2 : lanes 2 = .v10 := rfl
  have l3 : lanes 3 = .v11 := rfl
  have k64 : c64 = .v12 := rfl
  have k128 : c128 = .v13 := rfl
  rrun [l0, l1, l2, l3, k64, k128, b6, b7', bc_lit]
  have L0 := lanes0 (b.v .v8)
  have L1 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 0) (bc 16#8) = laneNums 1 := lanes_next 0
  have L2 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 1) (bc 16#8) = laneNums 2 := lanes_next 1
  have L3 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 2) (bc 16#8) = laneNums 3 := lanes_next 2
  refine ⟨⟨fun q hq => ?_, ?_, ?_⟩, fun v h7 h8 h9 h10 h11 h12 h13 => ?_, fun g h6 h7 => ?_,
    ?_, ?_, ?_, ?_⟩
  · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
      simp [State.setV, State.write, l0, l1, l2, l3, L0, L1, L2, L3]
  · simp [State.setV, State.write, k64]
  · simp [State.setV, State.write, k128]
  · simp [h7, h8, h9, h10, h11, h12, h13, bv, av]
  · simp [h6, h7, bg, ag]
  · simp [bm, am]
  · simp [brd, ard]
  · simp [bwr, awr]
  · simp [State.setV, State.write, bsp, asp]

end VG.Proof.Rc4.AArch64
