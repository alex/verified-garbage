import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits

/-! Untrusted: the scalar bits, point multiplication, and canonical encoding compose. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside val4)

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem powersKeep_outside {base : Addr} {s t : State} (h : PowersKeep base 56 7368 s t) :
    Outside base 56 7368 s.mem t.mem := fun p hp => h.mem p (by omega) hp

theorem scalarBaseInit_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block scalarBaseInit) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.basePoint ∧ env t.mem base 16 = Spec.Ed25519.d := by
  rw [scalarBaseInit, WP.block_append_iff]
  refine WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldCodeWide_ok (hs.of_keep ka) (constPointOps Spec.Ed25519.basePoint))
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_⟩
  · rw [vt, constPoint_eval]
  · rw [vt, va]; rfl

theorem scalarBasePrepare_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBasePrepare s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.basePoint ∧
      env t.mem base 16 = Spec.Ed25519.d ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
  rw [scalarBasePrepare]
  refine WP.seq (WP.mono (expandScalarBits_ok hs hp 32 (by decide) (by decide) hr hd)
    fun a ⟨ka, abits⟩ => ?_)
  have kap : PowersKeep base 56 7368 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr,
      (TableFrame.table ka.mem).mono (by decide) (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
  refine WP.mono (scalarBaseInit_ok (ka.scratch hs)) fun b ⟨kb, bp, bd⟩ => ?_
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at h
    rw [show 256 ^ 32 = 2 ^ (16 * 16) by decide] at h
    exact h
  have bbits : ∀ i < 16 * 16, b.mem (off base (768 + i)) =
      BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega)]; exact abits i hi
  exact ⟨kap.trans (PowersKeep.of_keep kb), bp, bd, bbits, hscalar⟩

theorem scalarBaseEngine_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBaseEngine s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bp, bd, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (pointMultiply_ok (kab.scratch hs) 16 _ (by decide) (by decide) hscalar bd bbits)
    fun c ⟨cp, _, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scratch (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc).trans (PowersKeep.of_rbx kt), ?_⟩
  change val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv, cp, bp]

end VG.Proof.Ed25519.X86_64
