import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same

/-!
# ML-DSA verification on x86-64: properties of every instruction

A property `q` of every instruction of `verify P p` (`Code.allInstrs q`) holds
if it holds of every instruction of the primitives `P` and of `verify P0 p`,
the same code with the primitives empty (`verify_q`), which the kernel
evaluates. So it never writes the stack pointer (`verify_spSafe`) if the
primitives do not. Likewise for `ctlC` (`verify_c`): it loads MXCSR only to
restore it (`verify_ctl`) if the primitives do (`ctlOk`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Spec.MlDsa

/-- The primitives, each empty. -/
def P0 : Prims := ⟨.block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [],
  .block [], .block [], .block [], .block [], .block [], ""⟩

/-- `q` holds of every instruction of the primitives `P`. -/
structure PrimsQ (q : Instr → Bool) (P : Prims) : Prop where
  ntt : P.ntt.allInstrs q = true
  invNtt : P.invNtt.allInstrs q = true
  mul : P.mul.allInstrs q = true
  mulAdd : P.mulAdd.allInstrs q = true
  sub : P.sub.allInstrs q = true
  rejNtt : P.rejNtt.allInstrs q = true
  ball : P.ball.allInstrs q = true
  useHint : P.useHint.allInstrs q = true
  simpleBitPack : P.simpleBitPack.allInstrs q = true
  bitUnpack : P.bitUnpack.allInstrs q = true
  unpackT1 : P.unpackT1.allInstrs q = true
  hintUnpack : P.hintUnpack.allInstrs q = true
  normLt : P.normLt.allInstrs q = true
  rej4 : P.rej4.allInstrs q = true

/-- `q` holds of every instruction of `c` exactly when it does of `c'`. -/
def SameQ (q : Instr → Bool) (c c' : Prog isa) : Prop := c.allInstrs q = c'.allInstrs q

section
variable {q : Instr → Bool}

theorem SameQ.seq {a a' b b' : Prog isa} (ha : SameQ q a a') (hb : SameQ q b b') :
    SameQ q (.seq a b) (.seq a' b') := by
  show (a.allInstrs q && b.allInstrs q) = (a'.allInstrs q && b'.allInstrs q)
  rw [show a.allInstrs q = a'.allInstrs q from ha, show b.allInstrs q = b'.allInstrs q from hb]

theorem SameQ.call {c : Prog isa} (hc : c.allInstrs q = true) {n n' : String} (as : List (Reg × Arg)) :
    SameQ q (callAt n c as) (callAt n' (.block []) as) := by
  show (_ && c.allInstrs q) = (_ && true)
  rw [hc]

theorem SameQ.seqR {f g : Nat → Prog isa} (h : ∀ k, SameQ q (f k) (g k)) :
    ∀ a n, SameQ q (seqR f a n) (seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => (h a).seq (SameQ.seqR h (a + 1) n)

theorem SameQ.ifOk {c c' : Prog isa} (h : SameQ q c c') : SameQ q (ifOk c) (ifOk c') := by
  refine SameQ.seq rfl ?_
  show (c.allInstrs q && _) = (c'.allInstrs q && _)
  rw [show c.allInstrs q = c'.allInstrs q from h]

theorem SameQ.sampled {c c' : Prog isa} (h : SameQ q c c') (a : Ptr) : SameQ q (sampled c a) (sampled c' a) :=
  h.seq rfl

theorem SameQ.sampled4 {c c' : Prog isa} (h : SameQ q c c') (a : Ptr) : SameQ q (sampled4 c a) (sampled4 c' a) :=
  h.seq rfl

variable {P : Prims} (hP : PrimsQ q P) (p : Params)
include hP

theorem hint_q : SameQ q (hint P p) (hint P0 p) := (SameQ.call hP.hintUnpack _).seq rfl

theorem zOne_q (i : Nat) : SameQ q (zOne P p i) (zOne P0 p i) :=
  (SameQ.call hP.bitUnpack _).seq ((SameQ.call hP.normLt _).seq rfl)

omit p in
theorem aOne_q (e : Nat) : SameQ q (aOne P e) (aOne P0 e) :=
  SameQ.seq rfl (SameQ.sampled (SameQ.call hP.rejNtt _) _)

theorem aGrp_q (r c : Nat) : SameQ q (aGrp P p r c) (aGrp P0 p r c) :=
  SameQ.seq rfl (SameQ.seq rfl (SameQ.seq rfl (SameQ.seq rfl (SameQ.sampled4 (SameQ.call hP.rej4 _) _))))

theorem aRow_q (r : Nat) : SameQ q (aRow P p r) (aRow P0 p r) := by
  refine (aGrp_q hP p r 0).seq ?_
  by_cases h : p.ℓ = 7
  · rw [ite_eq_left h, ite_eq_left h]; exact aGrp_q hP p r 3
  · rw [ite_eq_right h, ite_eq_right h]; exact SameQ.seqR (aOne_q hP) _ _

theorem samples_q : SameQ q (samples P p) (samples P0 p) :=
  SameQ.seq rfl ((SameQ.seqR (aRow_q hP p) _ _).seq (SameQ.sampled (SameQ.call hP.ball _) _))

theorem dot_q (r : Nat) : SameQ q (dot P p r) (dot P0 p r) :=
  (SameQ.call hP.mul _).seq (SameQ.seqR (fun _ => SameQ.call hP.mulAdd _) _ _)

theorem row_q (r : Nat) : SameQ q (row P p r) (row P0 p r) :=
  (dot_q hP p r).seq ((SameQ.call hP.unpackT1 _).seq ((SameQ.call hP.ntt _).seq ((SameQ.call hP.mul _).seq
    ((SameQ.call hP.sub _).seq ((SameQ.call hP.invNtt _).seq ((SameQ.call hP.useHint _).seq
      (SameQ.call hP.simpleBitPack _)))))))

theorem compute_q : SameQ q (compute P p) (compute P0 p) :=
  (SameQ.seqR (fun _ => SameQ.call hP.ntt _) _ _).seq ((SameQ.call hP.ntt _).seq
    ((SameQ.seqR (row_q hP p) _ _).seq rfl))

theorem verify_q : SameQ q (verify P p) (verify P0 p) :=
  SameQ.seq rfl (((hint_q hP p).seq (SameQ.ifOk ((SameQ.seqR (zOne_q hP p) _ _).seq
    (SameQ.ifOk ((samples_q hP p).seq (compute_q hP p)))))).seq rfl)

end

theorem verify0_sp : ∀ p ∈ params, (verify P0 p).allInstrs (fun i => !isa.writesSp i) = true := by
  decide +kernel

/-! ## MXCSR -/

/-- Every primitive of `P` loads MXCSR only to restore it. -/
structure PrimsC (P : Prims) : Prop where
  ntt : ctlOk P.ntt = true
  invNtt : ctlOk P.invNtt = true
  mul : ctlOk P.mul = true
  mulAdd : ctlOk P.mulAdd = true
  sub : ctlOk P.sub = true
  rejNtt : ctlOk P.rejNtt = true
  ball : ctlOk P.ball = true
  useHint : ctlOk P.useHint = true
  simpleBitPack : ctlOk P.simpleBitPack = true
  bitUnpack : ctlOk P.bitUnpack = true
  unpackT1 : ctlOk P.unpackT1 = true
  hintUnpack : ctlOk P.hintUnpack = true
  normLt : ctlOk P.normLt = true
  rej4 : ctlOk P.rej4 = true

/-- `ctlC` holds of `c` exactly when it does of `c'`. -/
def SameC (c c' : Prog isa) : Prop := ctlC c = ctlC c'

theorem SameC.seq {a a' b b' : Prog isa} (ha : SameC a a') (hb : SameC b b') : SameC (.seq a b) (.seq a' b') := by
  show (ctlC a && ctlC b) = (ctlC a' && ctlC b')
  rw [show ctlC a = ctlC a' from ha, show ctlC b = ctlC b' from hb]

theorem SameC.call {c : Prog isa} (hc : ctlOk c = true) {n n' : String} (as : List (Reg × Arg)) :
    SameC (callAt n c as) (callAt n' (.block []) as) := by
  show (_ && ctlOk c) = (_ && true)
  rw [hc]

theorem SameC.seqR {f g : Nat → Prog isa} (h : ∀ k, SameC (f k) (g k)) : ∀ a n, SameC (seqR f a n) (seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => (h a).seq (SameC.seqR h (a + 1) n)

theorem SameC.ifOk {c c' : Prog isa} (h : SameC c c') : SameC (ifOk c) (ifOk c') := by
  refine SameC.seq rfl ?_
  show (ctlC c && _) = (ctlC c' && _)
  rw [show ctlC c = ctlC c' from h]

theorem SameC.sampled {c c' : Prog isa} (h : SameC c c') (a : Ptr) : SameC (sampled c a) (sampled c' a) :=
  h.seq rfl

theorem SameC.sampled4 {c c' : Prog isa} (h : SameC c c') (a : Ptr) : SameC (sampled4 c a) (sampled4 c' a) :=
  h.seq rfl

section
variable {P : Prims} (hP : PrimsC P) (p : Params)
include hP

theorem verify_c : SameC (verify P p) (verify P0 p) := by
  have aOne : ∀ e, SameC (aOne P e) (aOne P0 e) := fun e =>
    SameC.seq rfl (SameC.sampled (SameC.call hP.rejNtt _) _)
  have dot : ∀ r, SameC (dot P p r) (dot P0 p r) := fun r =>
    (SameC.call hP.mul _).seq (SameC.seqR (fun _ => SameC.call hP.mulAdd _) _ _)
  have row : ∀ r, SameC (row P p r) (row P0 p r) := fun r =>
    (dot r).seq ((SameC.call hP.unpackT1 _).seq ((SameC.call hP.ntt _).seq ((SameC.call hP.mul _).seq
      ((SameC.call hP.sub _).seq ((SameC.call hP.invNtt _).seq ((SameC.call hP.useHint _).seq
        (SameC.call hP.simpleBitPack _)))))))
  have aGrp : ∀ r c, SameC (aGrp P p r c) (aGrp P0 p r c) := fun r c =>
    SameC.seq rfl (SameC.seq rfl (SameC.seq rfl (SameC.seq rfl (SameC.sampled4 (SameC.call hP.rej4 _) _))))
  have aRow : ∀ r, SameC (aRow P p r) (aRow P0 p r) := fun r => by
    refine (aGrp r 0).seq ?_
    by_cases h : p.ℓ = 7
    · rw [ite_eq_left h, ite_eq_left h]; exact aGrp r 3
    · rw [ite_eq_right h, ite_eq_right h]; exact SameC.seqR aOne _ _
  have samples : SameC (samples P p) (samples P0 p) :=
    SameC.seq rfl ((SameC.seqR aRow _ _).seq
      (SameC.sampled (SameC.call hP.ball _) _))
  have compute : SameC (compute P p) (compute P0 p) :=
    (SameC.seqR (fun _ => SameC.call hP.ntt _) _ _).seq ((SameC.call hP.ntt _).seq
      ((SameC.seqR row _ _).seq rfl))
  have zOne : ∀ i, SameC (zOne P p i) (zOne P0 p i) := fun _ =>
    (SameC.call hP.bitUnpack _).seq ((SameC.call hP.normLt _).seq rfl)
  exact SameC.seq rfl ((((SameC.call hP.hintUnpack _).seq rfl).seq (SameC.ifOk ((SameC.seqR zOne _ _).seq
    (SameC.ifOk (samples.seq compute))))).seq rfl)

end

theorem verify0_ctlC : ∀ p ∈ params, ctlC (verify P0 p) = true := by
  decide +kernel

variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params)
include C hp

theorem verify_ctl : ctlOk (verify P p) = true :=
  ctlOk_of_ctlC ((verify_c ⟨C.ntt.ctl, C.invNtt.ctl, C.mul.ctl, C.mulAdd.ctl, C.sub.ctl, C.rejNtt.ctl, C.ball.ctl,
    C.useHint.ctl, C.simpleBitPack.ctl, C.bitUnpack.ctl, C.unpackT1.ctl, C.hintUnpack.ctl,
    C.normLt.ctl, C.rej4.ctl⟩ p).trans (verify0_ctlC p hp))

theorem verify_spSafe : (verify P p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs ((verify_q ⟨Code.allInstrs_of_all C.ntt.spSafe, Code.allInstrs_of_all C.invNtt.spSafe,
    Code.allInstrs_of_all C.mul.spSafe, Code.allInstrs_of_all C.mulAdd.spSafe, Code.allInstrs_of_all C.sub.spSafe,
    Code.allInstrs_of_all C.rejNtt.spSafe, Code.allInstrs_of_all C.ball.spSafe,
    Code.allInstrs_of_all C.useHint.spSafe, Code.allInstrs_of_all C.simpleBitPack.spSafe,
    Code.allInstrs_of_all C.bitUnpack.spSafe, Code.allInstrs_of_all C.unpackT1.spSafe,
    Code.allInstrs_of_all C.hintUnpack.spSafe, Code.allInstrs_of_all C.normLt.spSafe,
    Code.allInstrs_of_all C.rej4.spSafe⟩ p).trans (verify0_sp p hp))

end VG.Proof.MlDsa.X86_64.Verify
