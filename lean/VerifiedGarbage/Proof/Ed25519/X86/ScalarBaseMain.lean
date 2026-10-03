import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.PointMul

/-! Merged from `Proof.Ed25519.X86.ScalarBaseContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def scalarBaseLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem scalarBase_pre {s : State} (h : scalarBaseLocal.pre s) :
    ScratchPre s 2 3 ∧ InputPre s 2 1 8 ∧ OutputPre s 2 := by
  obtain ⟨rd, wr, os, ins, _, ars, ro, rs, ofit, ifit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rs⟩,
    ⟨?_, ifit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ins
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointEncode`. -/
section
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
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem baseSetup_point (e : Env) : point (evalOps baseSetupOps e) 0 1 2 3 = Spec.Ed25519.basePoint := rfl
 theorem baseSetup_d (e : Env) : evalOps baseSetupOps e 16 = Spec.Ed25519.d := rfl

theorem Saved.ikeep {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : IKeep x s t) : Saved s₀ x t :=
  h.of_offset hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem Saved.mulkeep {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (k : MulKeep x s t) : Saved s₀ x t :=
  h.of_offset hx ⟨k.edi, k.esp, k.rd, k.wr⟩ k.frame (by decide) (by decide) (by decide)

theorem pointEncode_value {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEncode s fun t => IKeep x s t ∧ Spec.Ed25519.encodeLE 32 (fe t.mem x 96) =
      Spec.Ed25519.encodePoint (point (env s.mem x) 0 1 2 3) := by
  refine WP.mono (pointEncode_ok hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_⟩
  rw [vt]; rfl

theorem scalarBase_correct {s : State} (h : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hp, hi, ho⟩ := scalarBase_pre h
  let scalar := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  have scalar_bound : scalar < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change scalar < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  simp only [scalarBase, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_))
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide)) fun b ⟨hb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  have cc := hc.ctx hp.fit hp.wr
  have dc : env c.mem (arg s 2) 16 = Spec.Ed25519.d := by rw [ec, baseSetup_d]
  have pc : point (env c.mem (arg s 2)) 0 1 2 3 = Spec.Ed25519.basePoint := by rw [ec, baseSetup_point]
  have bc : ∀ i < 16 * 16, c.mem (addr (arg s 2) (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat := by
    intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii]), scalarBit_nat]
  refine WP.seq (WP.mono (pointMultiply_ok cc scalar 16 (by decide) (by decide) scalar_bound bc dc)
    fun d ⟨kd, pd, _⟩ => ?_)
  have hd := hc.mulkeep hp.fit kd
  refine WP.seq (WP.mono (pointEncode_value (hd.ctx hp.fit hp.wr)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 96) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ve, pd, pc]
  rfl

end VG.Proof.Ed25519.X86
