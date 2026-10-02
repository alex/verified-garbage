import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag
import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Frag
import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-DSA on x86-64: checks of code, but for the functions it calls

A check of code that composes over its structure and looks at the code of each
function called only through `mc` (`Comp m mc`: `ctlC`, with `ctlOk` of the
functions called, and `Code.allInstrs q`) gives the same result on two
programs that differ only in functions called, if it holds (`mc`) of those of
the first and the second calls empty code instead (`Same`, proven by
`same_tac` from the structure of the code). The top-level functions, written
for any implementation of the polynomial arithmetic, are checked once with
every function of it empty, so that the kernel evaluates no implementation of
it.
-/

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64

/-- `m` composes over the structure of code, and looks at the code of a
function called only through `mc`. -/
structure Comp (m mc : Prog isa → Bool) : Prop where
  seq : ∀ a b, m (.seq a b) = (m a && m b)
  ite : ∀ c t e, m (.ite c t e) = (m t && m e)
  loop : ∀ b c, m (.loop b c) = m b
  call : ∀ n b, m (.call n b) = mc b
  nil : mc (.block []) = true

theorem Comp.ctlC : Comp ctlC ctlOk :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Comp.all (q : Instr → Bool) : Comp (Code.allInstrs q) (Code.allInstrs q) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Code.allInstrs_of_all {I C : Type} {q : I → Bool} {c : Code I C} (h : c.all q = true) :
    c.allInstrs q = true := by
  induction c with
  | block is => induction is <;> simp_all [Code.all, Code.allInstrs]
  | _ => simp_all [Code.all, Code.allInstrs]

/-- `m` gives the same result on `c` and `c'`. -/
def Same (m : Prog isa → Bool) (c c' : Prog isa) : Prop := m c = m c'

section
variable {m mc : Prog isa → Bool} (hm : Comp m mc)
include hm

theorem Same.seq {a a' b b' : Prog isa} (ha : Same m a a') (hb : Same m b b') : Same m (.seq a b) (.seq a' b') := by
  unfold Same at *; rw [hm.seq, hm.seq, ha, hb]

theorem Same.ite {c : isa.Cond} {t t' e e' : Prog isa} (ht : Same m t t') (he : Same m e e') :
    Same m (.ite c t e) (.ite c t' e') := by
  unfold Same at *; rw [hm.ite, hm.ite, ht, he]

theorem Same.loop {b b' : Prog isa} {c : isa.Cond} (hb : Same m b b') : Same m (.loop b c) (.loop b' c) := by
  unfold Same at *; rw [hm.loop, hm.loop, hb]

theorem Same.call {c : Prog isa} (hc : mc c = true) (n n' : String) : Same m (.call n c) (.call n' (.block [])) := by
  unfold Same; rw [hm.call, hm.call, hc, hm.nil]

theorem Same.seqRS {f g : Nat → Prog isa} (h : ∀ k, Same m (f k) (g k)) :
    ∀ a n, Same m (Impl.MlDsa.X86_64.Sign.seqR f a n) (Impl.MlDsa.X86_64.Sign.seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => Same.seq hm (h a) (Same.seqRS h (a + 1) n)

theorem Same.seqRV {f g : Nat → Prog isa} (h : ∀ k, Same m (f k) (g k)) :
    ∀ a n, Same m (Impl.MlDsa.X86_64.Verify.seqR f a n) (Impl.MlDsa.X86_64.Verify.seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => Same.seq hm (h a) (Same.seqRV h (a + 1) n)

theorem Same.seqRK {f g : Nat → Prog isa} (h : ∀ k, Same m (f k) (g k)) :
    ∀ a n, Same m (Impl.MlKem.X86_64.seqR f a n) (Impl.MlKem.X86_64.seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => Same.seq hm (h a) (Same.seqRK h (a + 1) n)

end

/-- `m` of `a`, from that of code `b` that it gives the same result on. -/
theorem Same.ok {m : Prog isa → Bool} {a b : Prog isa} (h : Same m a b) (hb : m b = true) : m a = true :=
  Eq.trans h hb

/-- `Same m c c'` for code `c` that calls functions whose `mc` the
hypotheses state, and the same code `c'` but for empty functions in their
place: from the structure of the code. -/
macro "same_tac " hm:term : tactic =>
  `(tactic| repeat' (first
    | (apply Same.call $hm; assumption)
    | apply Same.seq $hm
    | apply Same.ite $hm
    | apply Same.loop $hm
    | (apply Same.seqRS $hm; intro)
    | (apply Same.seqRV $hm; intro)
    | (apply Same.seqRK $hm; intro)
    | rfl))

end VG.Proof.MlDsa.X86_64
