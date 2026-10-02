import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep

/-! Reload verification pointers and check the complete unsigned scalar S. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Proof.X25519.X86_64 (off Keeps ea_at ea_sc val4)

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.imm 32)]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [loadScalarWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hp, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left', scalarValue]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact (decodeLE_inputWords s.mem p).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      t.cf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L)) := by
  change WP isa (.block (([.mov .rdx (.mem (sc 7944))] : List Instr) ++
    ([.alu .add .rdx (.imm 32)] : List Instr) ++ loadScalarWords ++ scalarSubtract)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .rdx) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok b (off sig 32) bp (by
    intro d hd; rw [kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  refine WP.mono (scalarSubtract_ok c) fun t ⟨tc, _, _, kt⟩ => ?_
  refine ⟨(((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kc (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.2.1.trans (kc.2.1.trans (kb.2.1.trans ka.2.1)), ?_⟩
  rw [tc, cv, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
