import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCombine
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.X86_64.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual

/-! Untrusted: the uncofactored equation uses every bit of the challenge digest. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

theorem verifyRhsPrepare_ok {s : State} {base challenge : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hf : ∀ i < 64, 8192 ≤ ofs base (off challenge i)) :
    WP isa verifyRhsPrepare s fun t => PowersKeep base 56 7752 s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base 7680 ∧
      point (env t.mem base) 4 5 6 7 =
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424))) := by
  rw [verifyRhsPrepare]
  refine WP.seq (WP.mono (loadPointer_ok hs .rsi 7952 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  rw [hp] at ap
  have kap : PowersKeep base 56 7752 s a := PowersKeep.of_keeps ka (by decide)
  refine WP.seq (WP.mono (pointTableRead_ok (kap.scratch hs) 7424 (by decide) (by decide)) fun b ⟨kb, bp, _⟩ => ?_)
  have kab := kap.trans (PowersKeep.of_rbx kb)
  have bi : b.gpr .rsi = challenge := (kb.gpr _ (by decide) (by decide)).trans ap
  have bm : Spec.Ed25519.bytesAt b.mem challenge 64 = Spec.Ed25519.bytesAt s.mem challenge 64 := by
    rw [outside_bytes kb.mem (by decide) hf, ka.2.1]
  refine WP.seq (WP.mono (pointFromScalar_ok (kab.scratch hs) bi 32 (by decide) (by decide)
    (by intro i hi; rw [kb.rd, kb.wr, ka.2.2.1, ka.2.2.2]; exact hr i hi) hf) fun c ⟨kc, cp, cd⟩ => ?_)
  have kabc := kab.trans (kc.mono (by decide) (by decide))
  have cp' : point (env c.mem base) 0 1 2 3 =
      Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
        (tablePoint s.mem base 7424) := by rw [cp, bp, ka.2.1, bm]
  have ct (o : Nat) (hlo : 7424 ≤ o) (hhi : o + 128 ≤ 8192) :
      tablePoint c.mem base o = tablePoint s.mem base o := by
    rw [kc.mem.point (by omega) (Or.inr (by omega)) (by omega),
      workspace_tablePoint kb.mem (by omega) (by omega), ka.2.1]
  refine WP.mono (verifyCombine_ok (kabc.scratch hs) cd) fun t ⟨kt, tl, tr⟩ => ?_
  refine ⟨kabc.trans (PowersKeep.of_rbx kt), ?_, ?_⟩
  · rw [tl, ct 7680 (by decide) (by decide)]
  · rw [tr, cp', ct 7552 (by decide) (by decide)]

theorem verifyRhs_ok {s : State} {base challenge : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hf : ∀ i < 64, 8192 ≤ ofs base (off challenge i)) :
    WP isa verifyRhs s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual (tablePoint s.mem base 7680)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyRhs]
  refine WP.seq (WP.mono (verifyRhsPrepare_ok hs hp hr hf) fun a ⟨ka, al, ar⟩ => ?_)
  refine WP.mono (pointEqual_ok (ka.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  exact ⟨ka.trans (PowersKeep.of_keep kt), by rw [tv, al, ar]⟩

end VG.Proof.Ed25519.X86_64
