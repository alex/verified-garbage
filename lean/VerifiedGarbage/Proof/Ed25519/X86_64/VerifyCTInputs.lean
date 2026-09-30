import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyContext
import VerifiedGarbage.Proof.Ed25519.X86_64.PointFromScalarCT
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks

/-! Untrusted: recover public scalar pointers from the preserved verification headers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

theorem ScalarCTPre.of_keep {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s) (kt : Keep base s t) : ScalarCTPre count base k t :=
  ⟨h.1.of_keep kt, (kt.gpr _ (by decide)).trans h.2.1,
    fun i hi => by rw [kt.rd, kt.wr]; exact h.2.2.1 i hi, h.2.2.2⟩

theorem ScalarCTPre.of_rbx {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s) (kt : RbxKeep base s t) : ScalarCTPre count base k t :=
  ⟨kt.scratch h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1,
    fun i hi => by rw [kt.rd, kt.wr]; exact h.2.2.1 i hi, h.2.2.2⟩

theorem verifyLoadScalar_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rsi (.imm 32)])
      (fun s t => ScalarCTPre 16 base (off sig 32) s ∧ ScalarCTPre 16 base (off sig 32) t) := by
  have ht : RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rsi (.imm 32)])
      (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.scratch.rdi h.2.scratch.rdi
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rsi (.imm 32)]) s
        (ScalarCTPre 16 base (off sig 32)) := by
    change WP isa (.block (([.mov .rsi (.mem (Impl.X25519.X86_64.sc 7944))] : List Instr) ++
      [.alu .add .rsi (.imm 32)])) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .rsi 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_
    refine WP.mono (add32_ok a .rsi) fun t ⟨tp, kt⟩ => ?_
    refine ⟨(h.scratch.of_keeps ka (by decide)).of_keeps kt (by decide), ?_, ?_, h.scalarFar⟩
    · rw [tp, ap, h.sigHeader]
    · intro i hi; rw [kt.2.2.1, kt.2.2.2, ka.2.2.1, ka.2.2.2]; exact h.scalarBytes i hi
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem verifyLoadChallenge_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7952))])
      (fun s t => ScalarCTPre 32 base challenge s ∧ ScalarCTPre 32 base challenge t) := by
  have ht : RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7952))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.scratch.rdi h.2.scratch.rdi
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7952))]) s (ScalarCTPre 32 base challenge) := by
    refine WP.mono (loadPointer_ok h.scratch .rsi 7952 (by decide)) fun t ⟨tp, kt⟩ => ?_
    exact ⟨h.scratch.of_keeps kt (by decide), tp.trans h.challengeHeader,
      fun i hi => by rw [kt.2.2.1, kt.2.2.2]; exact h.challengeRead i hi, h.challengeFar⟩
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ed25519.X86_64
