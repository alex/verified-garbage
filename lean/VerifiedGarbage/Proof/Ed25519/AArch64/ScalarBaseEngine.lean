import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits

/-! The scalar bits, base-point multiplication, and canonical encoding compose. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem encodedValue_rep {p q : Spec.Ed25519.Point} {a : Edwards.EPoint dZ} (hp : Rep p a)
    (hq : Rep q a) : encodedValue p = encodedValue q := by
  rw [encodedValue, encodedValue, hp.affine_x, hp.affine_y, hq.affine_x, hq.affine_y]

theorem powersKeep_outside {base : Addr} {s t : State} (h : PowersKeep base 56 7368 s t) :
    Outside base 56 7368 s.mem t.mem := fun p hp => h.mem p (by omega) hp

theorem scalarBasePrepare_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBasePrepare s fun t => PowersKeep base 56 7368 s t ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
  rw [scalarBasePrepare]
  refine WP.mono (expandScalarBits_ok hs hp 32 (by decide) (by decide) hr hd) fun a ⟨ka, abits⟩ => ?_
  have kap : PowersKeep base 56 7368 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr, ka.sp,
      (TableFrame.table ka.mem).mono (by decide) (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
    · exact hr (by decide)
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at h
    rw [show 256 ^ 32 = 2 ^ (16 * 16) by decide] at h
    exact h
  exact ⟨kap, abits, hscalar⟩

theorem scalarBaseEngine_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBaseEngine s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (kab.scratch hs) (by simpa using hscalar) bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scr (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, ?_⟩
  change val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv]
  exact encodedValue_rep cp (pointMul_rep _ basePoint_rep)

end VG.Proof.Ed25519.AArch64
