import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify

/-!
# ML-DSA verification on x86-64: properties of every instruction

Untrusted: everything here is checked by Lean. A property `q` of every
instruction of `verify P p` (`Code.allInstrs q`) holds if it holds of every
instruction of the primitives `P` and of `verify P0 p`, the same code with
the primitives empty (`verify_q`), which the kernel evaluates. So it never
loads MXCSR (`verify_mxcsr`) or writes the stack pointer (`verify_spSafe`)
if the primitives do not.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Spec.MlDsa

/-- The primitives, each empty. -/
def P0 : Prims := ⟨.block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [],
  .block [], .block [], .block [], .block []⟩

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

/-- `q` holds of every instruction of `c` exactly when it does of `c'`. -/
def SameQ (q : Instr → Bool) (c c' : Prog isa) : Prop := c.allInstrs q = c'.allInstrs q

section
variable {q : Instr → Bool}

theorem SameQ.seq {a a' b b' : Prog isa} (ha : SameQ q a a') (hb : SameQ q b b') :
    SameQ q (.seq a b) (.seq a' b') := by
  show (a.allInstrs q && b.allInstrs q) = (a'.allInstrs q && b'.allInstrs q)
  rw [show a.allInstrs q = a'.allInstrs q from ha, show b.allInstrs q = b'.allInstrs q from hb]

theorem SameQ.call {c : Prog isa} (hc : c.allInstrs q = true) (n : String) (as : List (Reg × Arg)) :
    SameQ q (callAt n c as) (callAt n (.block []) as) := by
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

variable {P : Prims} (hP : PrimsQ q P) (p : Params)
include hP

theorem hint_q : SameQ q (hint P p) (hint P0 p) := (SameQ.call hP.hintUnpack _ _).seq rfl

theorem zOne_q (i : Nat) : SameQ q (zOne P p i) (zOne P0 p i) :=
  (SameQ.call hP.bitUnpack _ _).seq ((SameQ.call hP.normLt _ _).seq rfl)

omit p in
theorem aOne_q (e : Nat) : SameQ q (aOne P e) (aOne P0 e) :=
  SameQ.seq rfl (SameQ.sampled (SameQ.call hP.rejNtt _ _) _)

theorem aRow_q (r : Nat) : SameQ q (aRow P p r) (aRow P0 p r) := SameQ.seqR (aOne_q hP) _ _

theorem samples_q : SameQ q (samples P p) (samples P0 p) :=
  SameQ.seq rfl ((SameQ.seqR (aRow_q hP p) _ _).seq (SameQ.sampled (SameQ.call hP.ball _ _) _))

theorem dot_q (r : Nat) : SameQ q (dot P p r) (dot P0 p r) :=
  (SameQ.call hP.mul _ _).seq (SameQ.seqR (fun _ => SameQ.call hP.mulAdd _ _) _ _)

theorem row_q (r : Nat) : SameQ q (row P p r) (row P0 p r) :=
  (dot_q hP p r).seq ((SameQ.call hP.unpackT1 _ _).seq ((SameQ.call hP.ntt _ _).seq ((SameQ.call hP.mul _ _).seq
    ((SameQ.call hP.sub _ _).seq ((SameQ.call hP.invNtt _ _).seq ((SameQ.call hP.useHint _ _).seq
      (SameQ.call hP.simpleBitPack _ _)))))))

theorem compute_q : SameQ q (compute P p) (compute P0 p) :=
  (SameQ.seqR (fun _ => SameQ.call hP.ntt _ _) _ _).seq ((SameQ.call hP.ntt _ _).seq
    ((SameQ.seqR (row_q hP p) _ _).seq rfl))

theorem verify_q : SameQ q (verify P p) (verify P0 p) :=
  SameQ.seq rfl (((hint_q hP p).seq (SameQ.ifOk ((SameQ.seqR (zOne_q hP p) _ _).seq
    (SameQ.ifOk ((samples_q hP p).seq (compute_q hP p)))))).seq rfl)

end

theorem Code.allInstrs_of_all {I C : Type} {q : I → Bool} {c : Code I C} (h : c.all q = true) :
    c.allInstrs q = true := by
  induction c with
  | block is => induction is <;> simp_all [Code.all, Code.allInstrs]
  | _ => simp_all [Code.all, Code.allInstrs]

theorem verify0_mxcsr : ∀ p ∈ params, (verify P0 p).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem verify0_sp : ∀ p ∈ params, (verify P0 p).allInstrs (fun i => !isa.writesSp i) = true := by
  decide +kernel

variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params)
include C hp

theorem verify_mxcsr : (verify P p).allInstrs (fun i => !loadsMxcsr i) = true :=
  (verify_q ⟨C.ntt.mxcsr, C.invNtt.mxcsr, C.mul.mxcsr, C.mulAdd.mxcsr, C.sub.mxcsr, C.rejNtt.mxcsr, C.ball.mxcsr,
    C.useHint.mxcsr, C.simpleBitPack.mxcsr, C.bitUnpack.mxcsr, C.unpackT1.mxcsr, C.hintUnpack.mxcsr,
    C.normLt.mxcsr⟩ p).trans (verify0_mxcsr p hp)

theorem verify_spSafe : (verify P p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs ((verify_q ⟨Code.allInstrs_of_all C.ntt.spSafe, Code.allInstrs_of_all C.invNtt.spSafe,
    Code.allInstrs_of_all C.mul.spSafe, Code.allInstrs_of_all C.mulAdd.spSafe, Code.allInstrs_of_all C.sub.spSafe,
    Code.allInstrs_of_all C.rejNtt.spSafe, Code.allInstrs_of_all C.ball.spSafe,
    Code.allInstrs_of_all C.useHint.spSafe, Code.allInstrs_of_all C.simpleBitPack.spSafe,
    Code.allInstrs_of_all C.bitUnpack.spSafe, Code.allInstrs_of_all C.unpackT1.spSafe,
    Code.allInstrs_of_all C.hintUnpack.spSafe, Code.allInstrs_of_all C.normLt.spSafe⟩ p).trans (verify0_sp p hp))

end VG.Proof.MlDsa.X86_64.Verify
