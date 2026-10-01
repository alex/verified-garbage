import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.PointTable
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tablePointer_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat) :
    WP isa (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))]) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 o := by
  refine Wp.wp_mov fun a ha => Wp.wp_addi fun t ht => WP.block_nil ?_
  exact ⟨(updKeep ha).trans (updKeep ht), ht.mem.trans ha.mem, by rw [ht.gpr, ha.gpr, hc.edi]⟩

theorem pointTableWrite_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => ScalarKeep s t ∧ Frame [sub x o 128] s.mem t.mem ∧
      tablePoint t.mem x o = point (env s.mem x) 0 1 2 3 := by
  refine WP.block_append (WP.mono (tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointToTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨ka.scalar.trans ⟨kt.gpr _ (by decide), kt.gpr _ (by decide), kt.rd, kt.wr⟩,
    by rw [← ma]; exact kt.frame, by rw [ma] at vt; exact vt⟩

theorem pointTableRead_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat)
    (ho : 192 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x o ∧
      (∀ i : Slot, 4 ≤ i.val → env t.mem x i = env s.mem x i) := by
  refine WP.block_append (WP.mono (tablePointer_ok hc o) fun a ⟨ka, ma, pa⟩ => ?_)
  refine WP.mono (pointFromTable_ok (ka.ctx hc) pa ho hn) fun t ⟨kt, vt⟩ => ?_
  exact ⟨(FieldKeep.of_mem ka ma).trans (FieldKeep.of_copy kt (ka.ctx hc)),
    by rw [ma] at vt; exact vt, fun i hi => by rw [kt.high (ka.ctx hc) i hi, ma]⟩

theorem Saved.copykeep {s₀ s t : State} {x : BitVec 32} {o n : Nat} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : ScalarKeep s t) (f : Frame [sub x o n] s.mem t.mem)
    (ho : 16 ≤ o) (hn : o + n ≤ 8192) (ho' : o < 8192) : Saved s₀ x t :=
  h.of_offset hx k f ho hn ho'

end VG.Proof.Ed25519.X86
