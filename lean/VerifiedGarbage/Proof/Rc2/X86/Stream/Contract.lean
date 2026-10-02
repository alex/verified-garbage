import VerifiedGarbage.Proof.Rc2.X86.Stream.Copy
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# Streaming RC2-CBC on x86 (32-bit): the contracts the proofs use

Untrusted: everything here is checked by Lean. `Spec.Rc2.cbcInitContract`
and `Spec.Rc2.cbcUpdateContract` spelled out for x86, with the arguments
only read (the taint analysis follows them in memory only while nothing that
may alias them is written): `Verified.lean` moves the proofs to the shared
contracts, which let the code write them.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let iv : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let ctx : Region := ⟨(arg s 5).setWidth 64, 144⟩
    let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 24
    s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
        (Spec.Rc2.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) direction (arg s 2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Rc2.contextAt s'.mem ((arg s 5).setWidth 64) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax)).toNat = e.code
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨(arg s 0).setWidth 64, 144⟩
    let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let out : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
    let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 40
    s.rd = [data, args] ∧ s.wr = [ctx, out, buf] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ data.Disjoint out ∧
      data.Disjoint buf ∧ out.Disjoint buf ∧
      args.Disjoint ctx ∧ args.Disjoint out ∧ args.Disjoint buf ∧
      ret.Disjoint ctx ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
      (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
      40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat < 8 ∧ (arg s 5).toNat = ((arg s 1).toNat + (arg s 3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem ((arg s 0).setWidth 64) d (arg s 1).toNat)
      (Spec.Rc2.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    Spec.Rc2.contextAt s'.mem ((arg s 0).setWidth 64) d (((arg s 1).toNat + (arg s 3).toNat) % 8) =
        result.1 ∧
      Spec.Rc2.bytesAt s'.mem ((arg s 4).setWidth 64) (arg s 5).toNat = result.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

end VG.Proof.Rc2.X86.Stream
