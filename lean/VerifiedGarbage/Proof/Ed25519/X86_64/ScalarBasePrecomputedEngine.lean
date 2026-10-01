import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs val4)

variable {fld : Arith} [EdArith fld]

/-- The encoding's value depends only on the point represented. -/
theorem encodedValue_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    encodedValue p = (a.y : Spec.X25519.Fe).val + ((a.x : Spec.X25519.Fe).val % 2) * 2 ^ 255 := by
  have hx : p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.x : Spec.X25519.Fe) := by
    show toZ (p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.x
    rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]
  have hy : p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.y : Spec.X25519.Fe) := by
    show toZ (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.y
    rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]
  simp only [encodedValue, hx, hy]
  rfl

theorem scalarBasePrecomputedEngine_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBasePrecomputedEngine fld) s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBasePrecomputedEngine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, _, bd, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (fld := fld) (kab.scratch hs) hscalar bd bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scratch (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc).trans (PowersKeep.of_rbx kt), ?_⟩
  change val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv, encodedValue_rep cp, encodedValue_rep (pointMul_rep _ basePoint_rep)]

end VG.Proof.Ed25519.X86_64
