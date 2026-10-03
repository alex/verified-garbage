import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (T)

theorem scalarCarry_compare {x : BitVec 32} {s t : State}
    (hv : fe t.mem x T + 2 ^ 256 * acc t = fe s.mem x scalarR + (2 ^ 256 - Spec.Ed25519.L)) :
    (t.gpr .ebx == 0) = decide (fe s.mem x scalarR < Spec.Ed25519.L) := by
  have hr := fe_lt s.mem x scalarR
  have ht := fe_lt t.mem x T
  have hL := order_bound
  have hc : acc t ≤ 1 := by omega_using [hv, hr, hL]
  have he : (t.gpr .ebx).toNat = acc t := by
    simp only [acc, v] at hc ⊢
    omega_using [hc]
  have hz : t.gpr .ebx = 0 ↔ (t.gpr .ebx).toNat = 0 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, hz, he]
  omega_using [hv, ht, hL]

theorem verifyScalar_ok {s₀ s : State}
    (hp : ScratchPre s₀ 3 4) (hi : SlicePre s₀ 3 (arg s₀ 1 + 32) 32)
    (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.block verifyScalar) s fun t => Saved s₀ (arg s₀ 3) t ∧
      t.zf = some (decide (fe s₀.mem (arg s₀ 1 + 32) 0 < Spec.Ed25519.L)) := by
  simp only [verifyScalar, List.append_assoc]
  refine WP.block_append (WP.mono (inputSliceWords_ok hp hi hs (by decide)
    (dst := 64) (by decide) (by decide) (by decide)) fun a ⟨ha, wa, _⟩ => ?_)
  have fa : fe a.mem (arg s₀ 3) scalarR = fe s₀.mem (arg s₀ 1 + 32) 0 := by
    apply num_congr
    intro k hk
    change (wd a.mem (arg s₀ 3) (64 + 4 * k)).toNat =
      (wd s₀.mem (arg s₀ 1 + BitVec.ofNat 32 32) (0 + 4 * k)).toNat
    rw [Nat.zero_add]
    exact congrArg BitVec.toNat (wa k hk)
  refine WP.block_append (WP.mono (scalarSubtract_ok (ha.ctx hp.fit hp.wr)) fun b ⟨kb, fb, vb⟩ => ?_)
  have hb := ha.of_offset hp.fit (Keep.scalar kb) fb (by decide) (by decide) (by decide)
  refine Wp.wp_test fun t kt zt => WP.block_nil ?_
  refine ⟨⟨(congrFun kt.gpr .edi).trans hb.edi, (congrFun kt.gpr .esp).trans hb.esp,
    kt.rd.trans hb.rd, kt.wr.trans hb.wr, by rw [kt.mem]; exact hb.frame,
    by rw [kt.mem]; exact hb.saved⟩, ?_⟩
  rw [zt, BitVec.and_self, scalarCarry_compare vb, fa]

end VG.Proof.Ed25519.X86
