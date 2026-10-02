import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign

/-! Canonical Ed25519 point encoding in scratch slot1. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointEncode_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧
      fe t.mem x 96 =
        (env s.mem x 1 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val +
        ((env s.mem x 0 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  refine WP.seq (WP.mono (pointAffine_ok hc) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeField_ok (ka.ctx hc) 0) fun b ⟨kb, eb, vb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok (kb.ctx (ka.ctx hc))) fun c ⟨kc, mc, sc⟩ => ?_
  rw [WP.block_append_iff]
  have cc := kc.ctx (kb.ctx (ka.ctx hc))
  refine WP.mono (freezeField_ok cc 1) fun d ⟨kd, _, vd⟩ => ?_
  have ds : d.gpr .esi = BitVec.ofNat 32 (((env a.mem x 0).val % 2) * 2 ^ 31) := by
    change fe b.mem x 64 = _ at vb
    rw [kd.keep.esi, sc, vb]
  have dy : fe d.mem x 96 = (env a.mem x 1).val := by
    rw [mc, eb] at vd
    exact vd
  refine WP.mono (encodeSign_ok (kd.ctx cc) ((env a.mem x 0).val % 2) ((env a.mem x 1).val)
    (by omega) (Nat.lt_trans (env a.mem x 1).isLt (by decide : Spec.X25519.P < 2 ^ 255)) dy ds)
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans (IKeep.of_field kb)).trans kc).trans (IKeep.of_field kd)).trans (IKeep.of_field kt), ?_⟩
  rw [vt, ax, ay]

end VG.Proof.Ed25519.X86
