import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCombine
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyChallenge
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual

/-! Untrusted: the uncofactored equation uses every bit of the challenge digest
(the bits above a challenge below `2^256` are zero). -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyRhsPrepare_ok {s : State} {base challenge : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hw : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off challenge 32) d) 8)
    (hf : ∀ i < 64, 8192 ≤ ofs base (off challenge i)) :
    WP isa verifyRhsPrepare s fun t => PowersKeep base 56 7752 s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base 7680 ∧
      point (env t.mem base) 4 5 6 7 =
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424))) := by
  rw [verifyRhsPrepare]
  refine WP.seq (WP.mono (loadPointer_ok hs .x1 7952 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  rw [hp] at ap
  have kap : PowersKeep base 56 7752 s a := PowersKeep.of_keeps ka (by decide)
  refine WP.seq (WP.mono (pointTableRead_ok (kap.scratch hs) 7424 (by decide) (by decide)) fun b ⟨kb, bp, _⟩ => ?_)
  have kab := kap.trans (PowersKeep.of_counter kb)
  have bi : b.gpr .x1 = challenge := (kb.gpr _ (by decide) (by decide)).trans ap
  have bm : Spec.Ed25519.bytesAt b.mem challenge 64 = Spec.Ed25519.bytesAt s.mem challenge 64 := by
    rw [outside_bytes kb.mem (by decide) hf, ka.mem]
  refine WP.seq (WP.mono (challengeMul_ok (kab.scratch hs) bi
    (by intro d hd; rw [kb.rd, kb.wr, ka.rd, ka.wr]; exact hw d hd)
    (by intro i hi; rw [kb.rd, kb.wr, ka.rd, ka.wr]; exact hr i hi) hf) fun c ⟨kc, cp, cd⟩ => ?_)
  have kabc := kab.trans (kc.mono (by decide) (by decide))
  have cp' : point (env c.mem base) 0 1 2 3 =
      Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
        (tablePoint s.mem base 7424) := by rw [cp, bp, ka.mem, bm]
  have ct (o : Nat) (hlo : 7424 ≤ o) (hhi : o + 128 ≤ 8192) :
      tablePoint c.mem base o = tablePoint s.mem base o := by
    rw [kc.mem.point (by omega) (Or.inr (by omega)) (by omega),
      workspace_tablePoint kb.mem (by omega) (by omega), ka.mem]
  refine WP.mono (verifyCombine_ok (kabc.scratch hs) cd) fun t ⟨kt, tl, tr⟩ => ?_
  refine ⟨kabc.trans (PowersKeep.of_counter kt), ?_, ?_⟩
  · rw [tl, ct 7680 (by decide) (by decide)]
  · rw [tr, cp', ct 7552 (by decide) (by decide)]

theorem verifyRhs_ok {s : State} {base challenge : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hw : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off challenge 32) d) 8)
    (hf : ∀ i < 64, 8192 ≤ ofs base (off challenge i)) :
    WP isa verifyRhs s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual (tablePoint s.mem base 7680)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyRhs]
  refine WP.seq (WP.mono (verifyRhsPrepare_ok hs hp hr hw hf) fun a ⟨ka, al, ar⟩ => ?_)
  refine WP.mono (pointEqual_ok (ka.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  exact ⟨ka.trans (PowersKeep.of_keep kt), by rw [tv, al, ar]⟩

end VG.Proof.Ed25519.AArch64
