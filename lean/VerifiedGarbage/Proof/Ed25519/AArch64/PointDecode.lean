import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeLoad
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint

/-! Untrusted: canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa pointDecode s fun t => DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [eval, read_x, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter (CounterKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.AArch64
