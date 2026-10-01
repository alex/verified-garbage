import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Sat
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def signWide : Contract isa := { signCachedLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, msg] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) }

theorem signWide_pre (s : State) (h : signWide.pre s) :
    signCachedLocal.pre (s.withRegions (signRd s) (signWr s)) := by
  simp only [signCachedLocal, signRd, signWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem signWide_implies : signWide.Implies (Spec.Ed25519.signCachedContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  sat := sat

end VG.Proof.Ed25519.X86.SignCached
