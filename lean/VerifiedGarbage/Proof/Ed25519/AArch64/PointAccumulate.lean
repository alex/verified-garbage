import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! Untrusted: the scalar bit mask and the selection of the saved point. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.AArch64
