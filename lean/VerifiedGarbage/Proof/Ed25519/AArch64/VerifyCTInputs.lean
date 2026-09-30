import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext
import VerifiedGarbage.Proof.Ed25519.AArch64.PointFromScalarCT
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks

/-! Untrusted: recover public scalar pointers from the preserved verification headers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem ScalarCTPre.of_keep {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s) (kt : Keep base s t) : ScalarCTPre count base k t :=
  ⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1,
    fun i hi => by rw [kt.rd, kt.wr]; exact h.2.2.1 i hi, h.2.2.2⟩

theorem ScalarCTPre.of_counter {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s) (kt : CounterKeep base s t) : ScalarCTPre count base k t :=
  ⟨kt.scr h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1,
    fun i hi => by rw [kt.rd, kt.wr]; exact h.2.2.1 i hi, h.2.2.2⟩

theorem verifyLoadScalar_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x1 7944, .addImm .x .x1 .x1 32])
      (fun s t => ScalarCTPre 16 base (off sig 32) s ∧ ScalarCTPre 16 base (off sig 32) t) := by
  have ht : CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x1 7944, .addImm .x .x1 .x1 32])
      (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x1 7944, .addImm .x .x1 .x1 32]) s
        (ScalarCTPre 16 base (off sig 32)) := by
    change WP isa (.block (([ld .x1 7944] : List Instr) ++
      ([.addImm .x .x1 .x1 32] : List Instr))) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .x1 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
    refine WP.mono (add32_ok a .x1) fun t ⟨tp, kt⟩ => ?_
    refine ⟨(h.scratch.of_keeps ka (by decide)).of_keeps kt (by decide), ?_, ?_, h.scalarFar⟩
    · rw [tp, ap, h.sigHeader]
    · intro i hi; rw [kt.rd, kt.wr, ka.rd, ka.wr]; exact h.scalarBytes i hi
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem verifyLoadChallenge_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x1 7952])
      (fun s t => ScalarCTPre 32 base challenge s ∧ ScalarCTPre 32 base challenge t) := by
  have ht : CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x1 7952]) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x1 7952]) s (ScalarCTPre 32 base challenge) := by
    refine WP.mono (loadPointer_ok h.scratch .x1 7952 (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
    exact ⟨h.scratch.of_keeps kt (by decide), tp.trans h.challengeHeader,
      fun i hi => by rw [kt.rd, kt.wr]; exact h.challengeRead i hi, h.challengeFar⟩
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ed25519.AArch64
