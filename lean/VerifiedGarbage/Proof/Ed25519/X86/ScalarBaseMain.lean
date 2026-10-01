import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseContract
import VerifiedGarbage.Proof.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.PointEncode

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
