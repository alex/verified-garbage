import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity

/-! Untrusted: canonical decoding checks y before reduction modulo p. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (low63)
open VG.Proof.X25519.X86_64 (val4 Keeps freezeB freezeB_ok mask)

theorem setLow63_ok (s : State) :
    WP isa (.block [.movImm64 .rdx low63]) s fun t => t.gpr .rdx = low63 ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem canonicalMask_ok {s : State} (n : Nat)
    (hm : s.gpr .rcx = mask (decide (Spec.X25519.P ≤ n))) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      t.zf = some (decide (n < Spec.X25519.P)) ∧ Keeps [] s t := by
  have hz : (mask (decide (Spec.X25519.P ≤ n)) == 0#64) = decide (n < Spec.X25519.P) := by
    by_cases h : Spec.X25519.P ≤ n
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ n < Spec.X25519.P)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : n < Spec.X25519.P)]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hm]
  exact ⟨hz, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = n) :
    WP isa (.block canonicalY) s fun t => t.zf = some (decide (n < Spec.X25519.P)) ∧
      Keeps [.rdx, .r12, .r13, .r14, .r15, .rax, .rcx] s t := by
  change WP isa (.block (([.movImm64 .rdx low63] : List Instr) ++ freezeB ++
    [.alu .test .rcx (.reg .rcx)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setLow63_ok s) fun a ⟨ad, ka⟩ => ?_
  have av : val4 (a.gpr .r8) (a.gpr .r9) (a.gpr .r10) (a.gpr .r11) = n := by
    rw [val4, ka.1 .r8 (by decide), ka.1 .r9 (by decide), ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
    exact hv
  rw [WP.block_append_iff]
  refine WP.mono (freezeB_ok a (by rw [av]; omega) ad) fun b ⟨bc, _, kb⟩ => ?_
  rw [av] at bc
  refine WP.mono (canonicalMask_ok n bc) fun t ⟨tz, kt⟩ => ?_
  exact ⟨tz, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Ed25519.X86_64
