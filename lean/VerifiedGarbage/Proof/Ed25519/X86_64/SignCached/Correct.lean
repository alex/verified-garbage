import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Entry

/-! Complete signing meets its functional contract and preserves the ABI. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
open VG.Proof.Ed25519.X86_64.PublicKey (add_add ne_cs)

theorem sign_ok (v : Compress) {s : State} (h : signLocal.pre s) :
    WP isa (code fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ signLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 31 ≤ _; have := h.1; omega)
    (WP.mono (body_ok v hL hc hL.message_bound (cached_key h))
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 31 from rfl, add_add, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (lay s).out 64 = _
    rw [popped_mem, ho]
    rfl

end VG.Proof.Ed25519.X86_64.SignCached
