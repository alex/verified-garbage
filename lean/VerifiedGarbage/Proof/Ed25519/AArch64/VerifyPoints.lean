import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyLhs
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyRhs

/-! Untrusted: compose the two scalar multiplications and the projective equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcw : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off challenge 32) d) 8)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i)) :
    WP isa verifyEquationPoints s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  refine WP.seq (WP.mono (verifyLhs_ok hs hp hr hf) fun a ⟨ka, av, ap⟩ => ?_)
  have ac : a.mem.readW (off base 7952) 64 = challenge :=
    (ka.header (by decide) (by decide) (by decide)).trans hc
  have am : Spec.Ed25519.bytesAt a.mem challenge 64 = Spec.Ed25519.bytesAt s.mem challenge 64 :=
    outside_bytes (tableFrame_work ka.mem (by decide) (by decide)) (by decide) hcf
  refine WP.mono (verifyRhs_ok (ka.scratch hs) ac
    (by intro i hi; rw [ka.rd, ka.wr]; exact hcr i hi)
    (by intro d hd; rw [ka.rd, ka.wr]; exact hcw d hd) hcf) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ka.trans kt, ?_⟩
  rw [tv, av, am, ap 7552 (by decide) (by decide), ap 7424 (by decide) (by decide)]

end VG.Proof.Ed25519.AArch64
