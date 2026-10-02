import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call

/-!
# ML-DSA on x86 (32-bit): code that writes `esp` only by frames and calls

`NoSp` of code built from pieces, for any code of the primitives it calls:
sequences (`NoSp.seq`, `NoSp.seqR`) and calls with their arguments
(`NoSp.callP`, `NoSp.callPR`). Code that calls no primitive is checked by
evaluation (`NoSp.of_all`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs argRs callP callPR seqR)

theorem NoSp.seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem NoSp.seqR {f : Nat → Prog isa} (h : ∀ k, NoSp (f k)) : ∀ a n, NoSp (seqR f a n)
  | _, 0 => fun i hi => by simp [Impl.MlDsa.X86.KeyGen.seqR, VG.instrs] at hi
  | a, n + 1 => NoSp.seq (h a) (NoSp.seqR h (a + 1) n)

theorem setArgs_nosp (sc : Nat) : ∀ (rs : List Reg) (as : List Arg), (∀ r ∈ rs, r ≠ .esp) →
    ∀ i ∈ setArgs sc rs as, Taint.clobbers i .esp = false
  | [], _, _, _, hi => by simp [setArgs] at hi
  | _ :: _, [], _, _, hi => by simp [setArgs] at hi
  | r :: rs, a :: as, hr, i, hi => by
    simp only [setArgs, List.mem_append] at hi
    rcases hi with hi | hi
    · have hr0 := hr r (List.mem_cons_self ..)
      cases a with
      | buf b =>
        simp only [Impl.MlDsa.X86.KeyGen.Arg.set, Impl.MlKem.X86.ptrTo] at hi
        split at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
          rcases hi with rfl | rfl <;> simp [Taint.clobbers, Taint.dst, hr0]
      | imm v =>
        simp only [Impl.MlDsa.X86.KeyGen.Arg.set, List.mem_singleton] at hi
        subst hi; simp [Taint.clobbers, Taint.dst, hr0]
    · exact setArgs_nosp sc rs as (fun r' h => hr r' (List.mem_cons_of_mem _ h)) i hi

theorem NoSp.callP {sc : Nat} {nm : String} {c : Prog isa} {as : List Arg} (hc : NoSp c) :
    NoSp (callP sc nm c as) := by
  refine NoSp.seq (fun i hi => setArgs_nosp sc argRegs as (by decide) i hi) fun i hi => ?_
  simp only [Impl.MlKem.X86.callWith, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

theorem NoSp.callPR {sc : Nat} {nm : String} {c : Prog isa} {as : List Arg} (hc : NoSp c) :
    NoSp (callPR sc nm c as) := by
  refine NoSp.seq (fun i hi => setArgs_nosp sc argRegs as (by decide) i hi) fun i hi => ?_
  simp only [Impl.MlKem.X86.callRet, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

end VG.Proof.MlDsa.X86.KeyGen
