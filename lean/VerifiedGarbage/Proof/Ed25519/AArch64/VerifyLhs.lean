import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyTables
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarBatch

/-! Untrusted: compute [S]B while retaining the two decoded verification points. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyLhs_ok {s : State} {base sig : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)) :
    WP isa verifyLhs s fun t => PowersKeep base 56 7752 s t ∧
      tablePoint t.mem base 7680 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint ∧
      ∀ d, 7424 ≤ d → d + 128 ≤ 7680 → tablePoint t.mem base d = tablePoint s.mem base d := by
  rw [verifyLhs]
  apply WP.seq
  change WP isa (.block (([ld .x1 7944] : List Instr) ++
    ([.addImm .x .x1 .x1 32] : List Instr))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x1 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (add32_ok a .x1) fun b ⟨bp, kb⟩ => ?_
  rw [ap, hp] at bp
  have kap : PowersKeep base 56 7752 s a := PowersKeep.of_keeps ka (by decide)
  have kbp : PowersKeep base 56 7752 a b := PowersKeep.of_keeps kb (by decide)
  have kab := kap.trans kbp
  refine WP.seq (WP.mono (baseFromScalarVar_ok (kab.scratch hs) bp
    (by intro i hi; rw [kb.rd, kb.wr, ka.rd, ka.wr]; exact hr i hi) hf)
    fun d ⟨kd, dv, _⟩ => ?_)
  have dm : Spec.Ed25519.bytesAt b.mem (off sig 32) 32 = Spec.Ed25519.bytesAt s.mem (off sig 32) 32 := by
    rw [kb.mem, ka.mem]
  have kabd := kab.trans (kd.mono (by decide) (by decide))
  refine WP.mono (pointTableWrite_ok (kabd.scratch hs) 7680 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
  refine ⟨kabd.trans (kt.mono (by decide) (by decide)), ?_, ?_⟩
  · rw [tv, dv, dm]
  · intro o hlo hhi
    rw [kt.mem.point (by omega) (Or.inl (by omega)) (by omega),
      kd.mem.point (by omega) (Or.inr (by omega)) (by omega), kb.mem, ka.mem]

end VG.Proof.Ed25519.AArch64
