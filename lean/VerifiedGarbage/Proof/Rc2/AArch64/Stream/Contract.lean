import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Streaming RC2-CBC on AArch64: the contracts the proofs use

`Spec.Rc2.cbcInitContract` and `Spec.Rc2.cbcUpdateContract` spelled out for
AArch64 (the arguments in `x0`–`x6`), with the 16-byte frame below the stack
pointer that saves `x30` around the calls. -/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64

/-- `init(key = x0, key_len = x1, effective_bits = x2, iv = x3, iv_len = x4,
ctx = x5, scratch = x6)`. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let iv : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let ctx : Region := ⟨s.gpr .x5, 144⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      stk.Disjoint key ∧ stk.Disjoint iv ∧ stk.Disjoint ctx ∧ stk.Disjoint scr ∧
      (s.gpr .x5).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) direction (s.gpr .x2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .x5) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .x0)).toNat = e.code
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

/-- `update(ctx = x0, pending_len = x1, data = x2, len = x3, out = x4,
out_len = x5, scratch = x6)` in the direction `d`. -/
def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 144⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let out : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [data] ∧ s.wr = [ctx, out, scr] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧ data.Disjoint out ∧
      data.Disjoint scr ∧ out.Disjoint scr ∧
      stk.Disjoint ctx ∧ stk.Disjoint data ∧ stk.Disjoint out ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat < 8 ∧ (s.gpr .x5).toNat = ((s.gpr .x1).toNat + (s.gpr .x3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .x0) d (s.gpr .x1).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.contextAt s'.mem (s.gpr .x0) d (((s.gpr .x1).toNat + (s.gpr .x3).toNat) % 8) = result.1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = result.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

end VG.Proof.Rc2.AArch64.Stream
