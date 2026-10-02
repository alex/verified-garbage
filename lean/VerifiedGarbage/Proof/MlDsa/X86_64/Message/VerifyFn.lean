import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims

/-!
# ML-DSA on x86-64, `verify_message`: the verification functions on `μ` it calls

Untrusted: everything here is checked by Lean. `vg_mldsa*_verify`, with any
implementation `v` of the polynomial arithmetic, is a function
`verify_message` can call (`verifyFn`): its proofs give its contract, it
never writes `rsp`, and its calls nest at most three deep, which, as whether
it writes `rsp`, is checked on the code with its primitives empty
(`verify_same`), given that theirs nest at most twice.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl)
open VG.Impl.MlDsa.X86_64.Verify (Prims callAt seqR ifOk sampled hint zOne aOne aRow samples dot row compute)
open VG.Proof.MlDsa.X86_64.Verify (P0 PrimsOk primsWith prims_okWith verify_correct verify_ct)
open VG.Spec.MlDsa

/-- `mc` holds of every primitive of `P`. -/
structure PrimsM (mc : Prog isa → Bool) (P : Prims) : Prop where
  ntt : mc P.ntt = true
  invNtt : mc P.invNtt = true
  mul : mc P.mul = true
  mulAdd : mc P.mulAdd = true
  sub : mc P.sub = true
  rejNtt : mc P.rejNtt = true
  ball : mc P.ball = true
  useHint : mc P.useHint = true
  simpleBitPack : mc P.simpleBitPack = true
  bitUnpack : mc P.bitUnpack = true
  unpackT1 : mc P.unpackT1 = true
  hintUnpack : mc P.hintUnpack = true
  normLt : mc P.normLt = true

section
variable {m mc : Prog isa → Bool} (hm : Comp m mc)
include hm

theorem Same.callAt {c : Prog isa} (hc : mc c = true) (n n' : String) (as : List (Reg × Impl.MlDsa.X86_64.Verify.Arg)) :
    Same m (callAt n c as) (callAt n' (.block []) as) :=
  Same.seq hm rfl (Same.call hm hc n n')

theorem Same.ifOk {c c' : Prog isa} (h : Same m c c') : Same m (ifOk c) (ifOk c') :=
  Same.seq hm rfl (Same.ite hm h rfl)

theorem Same.sampled {c c' : Prog isa} (h : Same m c c') (a : Impl.MlDsa.X86_64.Verify.Ptr) :
    Same m (sampled c a) (sampled c' a) :=
  Same.seq hm h rfl

variable {P : Prims} (hP : PrimsM mc P) (p : Params)
include hP

theorem verify_same : Same m (Impl.MlDsa.X86_64.Verify.verify P p) (Impl.MlDsa.X86_64.Verify.verify P0 p) := by
  have aOne : ∀ e, Same m (aOne P e) (aOne P0 e) := fun e =>
    Same.seq hm rfl (Same.sampled hm (Same.callAt hm hP.rejNtt _ _ _) _)
  have dot : ∀ r, Same m (dot P p r) (dot P0 p r) := fun r =>
    Same.seq hm (Same.callAt hm hP.mul _ _ _) (Same.seqRV hm (fun _ => Same.callAt hm hP.mulAdd _ _ _) _ _)
  have row : ∀ r, Same m (row P p r) (row P0 p r) := fun r =>
    Same.seq hm (dot r) (Same.seq hm (Same.callAt hm hP.unpackT1 _ _ _) (Same.seq hm (Same.callAt hm hP.ntt _ _ _)
      (Same.seq hm (Same.callAt hm hP.mul _ _ _) (Same.seq hm (Same.callAt hm hP.sub _ _ _)
        (Same.seq hm (Same.callAt hm hP.invNtt _ _ _) (Same.seq hm (Same.callAt hm hP.useHint _ _ _)
          (Same.callAt hm hP.simpleBitPack _ _ _)))))))
  have samples : Same m (samples P p) (samples P0 p) :=
    Same.seq hm rfl (Same.seq hm (Same.seqRV hm (fun r => Same.seqRV hm aOne _ _) _ _)
      (Same.sampled hm (Same.callAt hm hP.ball _ _ _) _))
  have compute : Same m (compute P p) (compute P0 p) :=
    Same.seq hm (Same.seqRV hm (fun _ => Same.callAt hm hP.ntt _ _ _) _ _) (Same.seq hm (Same.callAt hm hP.ntt _ _ _)
      (Same.seq hm (Same.seqRV hm row _ _) rfl))
  have zOne : ∀ i, Same m (zOne P p i) (zOne P0 p i) := fun _ =>
    Same.seq hm (Same.callAt hm hP.bitUnpack _ _ _) (Same.seq hm (Same.callAt hm hP.normLt _ _ _) rfl)
  exact Same.seq hm rfl (Same.seq hm (Same.seq hm (Same.seq hm (Same.callAt hm hP.hintUnpack _ _ _) rfl)
    (Same.ifOk hm (Same.seq hm (Same.seqRV hm zOne _ _) (Same.ifOk hm (Same.seq hm samples compute))))) rfl)

end

theorem verify0_noSp {p : Params} (h3 : Sign.Ok3 p) : noSpB (Impl.MlDsa.X86_64.Verify.verify P0 p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem verify0_depth {p : Params} (h3 : Sign.Ok3 p) :
    decide ((Impl.MlDsa.X86_64.Verify.verify P0 p).depth ≤ 3) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

/-- `mc` of every primitive, from what `PrimsOk` says of it. -/
theorem primsM_of {P : Prims} (C : PrimsOk P) {mc : Prog isa → Bool}
    (h : ∀ {c : Prog isa}, NoSp c → c.depth ≤ 2 → mc c = true) : PrimsM mc P :=
  ⟨h C.ntt.nosp C.ntt.depth, h C.invNtt.nosp C.invNtt.depth, h C.mul.nosp C.mul.depth,
    h C.mulAdd.nosp C.mulAdd.depth, h C.sub.nosp C.sub.depth, h C.rejNtt.nosp C.rejNtt.depth,
    h C.ball.nosp C.ball.depth, h C.useHint.nosp C.useHint.depth, h C.simpleBitPack.nosp C.simpleBitPack.depth,
    h C.bitUnpack.nosp C.bitUnpack.depth, h C.unpackT1.nosp C.unpackT1.depth,
    h C.hintUnpack.nosp C.hintUnpack.depth, h C.normLt.nosp C.normLt.depth⟩

/-- `vg_mldsa*_verify`, with the polynomial arithmetic of `v`. -/
theorem verifyFn (v : ArithImpl) {p : Params} (hp : p ∈ params) :
    VerifyFn p (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) p) := by
  have h3 := ok3_of hp
  have hp' : p ∈ Verify.params := hp
  have C := prims_okWith v
  exact ⟨verify_correct C hp', verify_ct C hp',
    noSp_of (Same.ok (verify_same (Comp.all _) (primsM_of C fun h _ => noSpB_of h) p) (verify0_noSp h3)),
    of_decide_eq_true (Same.ok (verify_same depthComp (primsM_of C fun _ h => decide_eq_true h) p)
      (verify0_depth h3))⟩

theorem verifyMessage_spSafe {p : Params} {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.MlDsa.X86_64.Message.verifyMessage n c p).all (fun i => !isa.writesSp i) = true := by
  generalize hq : (fun i => !isa.writesSp i) = q at hc ⊢
  have ha : Impl.Sha3.X86_64.Stream.absorb.all q = true := hq ▸ kabs_spSafe
  have hp' : Impl.Sha3.X86_64.Stream.pad.all q = true := hq ▸ kpad_spSafe
  have hs : Impl.Sha3.X86_64.Stream.squeeze.all q = true := hq ▸ ksqz_spSafe
  have hsa : ∀ as, (setArgs as).all q = true := fun as => hq ▸ setArgs_wsp as
  have hmv : ∀ a, (Arg.mov .rdi a).all q = true := fun a => hq ▸ arg_wsp .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.verifyMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.trHash, Impl.MlDsa.X86_64.Message.zeroSt,
    Impl.MlDsa.X86_64.Message.kabs, Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz,
    Impl.MlDsa.X86_64.Message.callA, Code.all, hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  subst hq
  decide

end VG.Proof.MlDsa.X86_64.Message
