import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YLane
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes

/-!
# ML-DSA on x86-64: the SSE2 code of the AVX2 rounding, on a register

`hbX` and `lbX` compute `hbL` and `lbL` in each doubleword of `xmm0`
(`hbX_ok`, `lbX_ok`), with the constants in `xmm8`, `xmm9`, `xmm10` (and `q`
in `xmm15`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad caddL caddV dword_caddV qV
  dword_qV)
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (gamma2s)

/-- Each doubleword of `x` is `v`. -/
def Bc (x : BitVec 128) (v : BitVec 32) : Prop := ∀ e < 4, dword x e = v

theorem bc_ofDwords (v : BitVec 32) : Bc (ofDwords v v v v) v := fun e he => by
  rcases cases4 he with rfl | rfl | rfl | rfl <;> simp

/-- The constants of `hbX`. -/
structure HbC (g : Nat) (s : State) : Prop where
  c8 : Bc (s.xmm .xmm8) (BitVec.ofNat 32 127)
  c9 : Bc (s.xmm .xmm9) (BitVec.ofNat 32 (dAdd g))
  c10 : Bc (s.xmm .xmm10) (BitVec.ofNat 32 (dMod g))

theorem dSh_32 : dSh g32 = [10] := rfl
theorem dSh_88 : dSh g88 = [1, 3, 10, 11, 13] := rfl
theorem dShift_32 : dShift g32 = 22 := rfl
theorem dShift_88 : dShift g88 = 24 := rfl

theorem hbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) :
    WP isa (.block (hbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm0) e = hbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [hbX, hfX, mulX, dSh_32, dSh_88, dShift_32, dShift_88, xmov, xb, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | assumption) only [dword_pand, dword_psrad, dword_psubd, dword_psrld,
      dword_pslld, dword_paddd, hc.c8 e he, hc.c9 e he, hc.c10 e he, BitVec.toNat_ofNat]
    rfl

theorem mul2X_32 : mul2X g32 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 19), xmov .xmm2 .xmm0,
    .xop (.shift .pslld .xmm2 9), xb .psubd .xmm1 .xmm2] := rfl

theorem mul2X_88 : mul2X g88 = [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 11)] ++ [13, 14, 15, 17].flatMap fun k =>
    [xmov .xmm2 .xmm0, .xop (.shift .pslld .xmm2 (BitVec.ofNat 8 k)), xb .paddd .xmm1 .xmm2] := rfl

theorem lbX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (lbX g)) s fun s' => (∀ e < 4, dword (s'.xmm .xmm3) e = lbL g (dword (s.xmm .xmm0) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3] s s' := by
  rcases hg with rfl | rfl <;>
  · simp only [lbX, hbX, hfX, mulX, mul2X_32, mul2X_88, dSh_32, dSh_88, dShift_32, dShift_88,
      VG.Impl.MlDsa.X86_64.Arith.vcadd, xmov, xb, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    vrun [VG.X86_64.eval_movdqa]
    refine ⟨fun e he => ?_, by xonly⟩
    simp (disch := first | decide | assumption) only [dword_pand, dword_psrad, dword_psubd, dword_psrld,
      dword_pslld, dword_paddd, hc.c8 e he, hc.c9 e he, hc.c10 e he, BitVec.toNat_ofNat, hq, dword_qV he]
    rfl

end VG.Proof.MlDsa.X86_64.Round
