import VerifiedGarbage.Impl.Argon2.AArch64.AddressCalls
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.AArch64.Memory

/-! Independent-address compression arguments from one fixed frame read. -/
namespace VG.Proof.Argon2.AArch64.AddressCalls
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls
open VG.Impl.Argon2.AArch64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

theorem pointer_ok (s : State) (offset : Nat) (bound : offset ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .x0 = work s + BitVec.ofNat 64 offset ∧ Divide.Keeps [.x0, .x12, .x15] s t := by
  simp only [pointer, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x0 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, keeps⟩
  refine (Instructions.addi_ok a .x0 offset (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 offset) value), ?_⟩
  exact (keeps.mono (by simp)).trans kt

theorem args_ok (s : State) (x y out : Nat) (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .x3 = work s ∧ t.gpr .x0 = work s + BitVec.ofNat 64 x ∧
      t.gpr .x1 = work s + BitVec.ofNat 64 y ∧ t.gpr .x2 = work s + BitVec.ofNat 64 out ∧
      Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s t := by
  simp only [args, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x3 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨scratch, ka⟩
  rw [← List.append_assoc (Instructions.mov .x0 .x3) (Instructions.addi .x0 x)]
  apply WP.block_append
  refine (Instructions.pointer_ok a .x0 .x3 x (by omega) (by decide) (by decide)).mono ?_
  rintro b ⟨left, kb⟩
  rw [← List.append_assoc (Instructions.mov .x1 .x3) (Instructions.addi .x1 y)]
  apply WP.block_append
  refine (Instructions.pointer_ok b .x1 .x3 y (by omega) (by decide) (by decide)).mono ?_
  rintro c ⟨right, kc⟩
  refine (Instructions.pointer_ok c .x2 .x3 out (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨output, kt⟩
  have scrB := kb.regs .x3 (by decide)
  have scrC := kc.regs .x3 (by decide)
  refine ⟨(kt.regs .x3 (by decide)).trans (scrC.trans (scrB.trans scratch)),
    (kt.regs .x0 (by decide)).trans ((kc.regs .x0 (by decide)).trans
      (left.trans (congrArg (· + BitVec.ofNat 64 x) scratch))),
    (kt.regs .x1 (by decide)).trans (right.trans (congrArg (· + BitVec.ofNat 64 y) (scrB.trans scratch))),
    output.trans (congrArg (· + BitVec.ofNat 64 out) (scrC.trans (scrB.trans scratch))), ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans
    ((kc.mono (by decide)).trans (kt.mono (by decide))))
end VG.Proof.Argon2.AArch64.AddressCalls
