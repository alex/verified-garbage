import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarStep

/-! Reload verification pointers and check the complete unsigned scalar S. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) (d : Nat)
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [ld r d]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  rw [runBlock_cons, load_sc hs ha hd, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.addImm .x r r 32]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (32 : Nat) < 4096 from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  refine WP.mono (loadWords_ok s .x2 (by decide) (by rw [hp]; exact hr)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, kt⟩
  rw [scalarValue, tv, hp, decodeLE_inputWords]

theorem setZeroX10_ok (s : State) :
    WP isa (.block [.movz .w .x10 0 0]) s fun t => t.gpr .x10 = 0 ∧ Keeps [.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem carryMask_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block [.sbcs .x .x8 .x10 .x10]) s fun t =>
      (t.gpr .x8 != 0) = !s.c ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_addWithCarry, ite_true, BitVec.setWidth_eq, hz]
    cases s.c <;> decide
  · simp only [RegUpd.gpr_addWithCarry,
      show k ≠ .x8 by simpa only [List.mem_singleton] using hk, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      (t.gpr .x8 != 0) = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L) := by
  change WP isa (.block (([ld .x2 7944] : List Instr) ++
    ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr) ++
    loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) s _
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .x2) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (setZeroX10_ok b) fun z ⟨zz, kz⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok z (off sig 32) ((kz.gpr _ (by decide)).trans bp) (by
    intro d hd; rw [kz.rd, kz.wr, kb.rd, kb.wr, ka.rd, ka.wr]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok c ((kc.gpr _ (by decide)).trans zz)) fun d ⟨dc, _, _, kd⟩ => ?_
  refine WP.mono (carryMask_ok d ((kd.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans zz)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨(((((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kz (by decide))).trans (Keep.of_keeps kc (by decide))).trans
    (Keep.of_keeps kd (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.mem.trans (kd.mem.trans (kc.mem.trans (kz.mem.trans (kb.mem.trans ka.mem)))), ?_⟩
  rw [tz, dc, cv, kz.mem, kb.mem, ka.mem]
  simp only [← decide_not, Nat.not_le]

end VG.Proof.Ed25519.AArch64
