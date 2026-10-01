import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Entry
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Body

/-! Correctness and ABI preservation of the complete verification operation. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)

theorem pop_rsp (B : Addr) :
    B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 21) = B + BitVec.ofNat 64 184 := by
  rw [PublicKey.add_add]

theorem verifyMessage_ok (v : Compress) {s : State} (h : verifyMessageLocal.pre s) :
    WP isa (code fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ verifyMessageLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide)
    (by show 8 * 21 ≤ _; have := h.1; omega)
    (WP.mono (body_ok v hL hc hL.message_bound)
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .r11 pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 21 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (PublicKey.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · change (popped .r11 pushRs.length u).gpr .rax = _
    rw [popped_gpr _ _ _ (by decide) (by decide), ho]
    rfl

end VG.Proof.Ed25519.X86_64.VerifyMessage
