import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem dSetup_point (e : Env) : point (evalOps [.const 16 Spec.Ed25519.d] e) 0 1 2 3 =
    point e 0 1 2 3 := rfl

theorem pointFromInput_ok {s₀ s : State} {scidx argc i skip bytes count : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : SlicePre s₀ scidx (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : bytes ≤ 64)
    (hc0 : 0 < count) (hc32 : count ≤ 32) (hsize : 8 * bytes = 16 * count) :
    WP isa (pointFromInput i skip bytes count) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      Frame [sub (arg s₀ scidx) 24 7656] s.mem t.mem ∧
      point (env t.mem (arg s₀ scidx)) 0 1 2 3 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem
          ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes)) (point (env s.mem (arg s₀ scidx)) 0 1 2 3) ∧
      env t.mem (arg s₀ scidx) 16 = Spec.Ed25519.d := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (inputSliceBits_ok hp hi hs hia hn) fun a ⟨ha, ba, fa⟩ => ?_
  have ca := ha.ctx hp.fit hp.wr
  have ea : env a.mem (arg s₀ scidx) = env s.mem (arg s₀ scidx) :=
    table_env hp.fit fa (by decide) (by omega_using [hn])
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] ca) fun b ⟨kb, eb⟩ => ?_
  have hb := ha.ikeep hp.fit (IKeep.of_field kb)
  have cb := hb.ctx hp.fit hp.wr
  let scalar := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem
    ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes)
  have sb : scalar < 2 ^ (16 * count) := by
    have hh := decodeLE_lt (Spec.Ed25519.bytesAt s₀.mem
      ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hh
    change scalar < 256 ^ bytes at hh
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, hsize] at hh
    exact hh
  have bb : ∀ k < 16 * count, b.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8 (scalarBit scalar k).toNat := by
    intro k hk
    rw [IKeep.bit (IKeep.of_field kb) ca k (by omega_using [hk, hc32]), ba k (by omega_using [hk, hsize]), scalarBit_nat]
  refine WP.mono (pointMultiply_ok cb scalar count hc0 hc32 sb bb (by rw [eb]; rfl)) fun t ⟨kt, pt, dt⟩ => ?_
  refine ⟨hb.mulkeep hp.fit kt, ?_, ?_, dt⟩
  · exact ((frameWiden fa hp.fit (by decide) (by omega_using [hn]) (by decide)).trans
      (frameWiden kb.frame hp.fit (by decide) (by decide) (by decide))).trans
      (frameWiden kt.frame hp.fit (by decide) (by decide) (by decide))
  · rw [eb, dSetup_point, ea] at pt
    exact pt

end VG.Proof.Ed25519.X86
