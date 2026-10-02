import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call

/-!
# ML-DSA on AArch64: entry to a callee

What a callee's contract needs on its entry (the state of the call, with the
link registers changed), from the layout of the caller (`cpre`): the stack it
may use (`wfP_of`, `resv`), and its buffers apart from that stack and from
each other, and not wrapping around. The values of the arguments after their
moves (`Args.ptr`, `Args.imm`), the same in runs whose layout registers
agree (`SameIn.args`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Spec.MlDsa

theorem wfP_of {S sp : Nat} (h : S ≤ sp) : wfP S sp := by unfold wfP; split <;> trivial

theorem stackBelow_mem {sp : Addr} {S : Nat} {r : Region} (h : r ∈ stackBelow sp S) : r = below sp S := by
  rcases S with _ | S
  · simp [stackBelow] at h
  · simp only [stackBelow, List.mem_singleton] at h; exact h

/-- The disjointness of the callee's stack from its buffers. -/
theorem resv {S : Nat} {sp : Addr} {f : Region → List Prop} (h : ∀ r ∈ stackBelow sp S, Sig.conj (f r)) :
    Sig.conj ((stackBelow sp S).map f).flatten := by
  rcases S with _ | S
  · trivial
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact h _ (List.mem_singleton_self _)

theorem conj_cons {p : Prop} {l : List Prop} (hp : p) (hl : Sig.conj l) : Sig.conj (p :: l) :=
  Sig.conj_cons.mpr ⟨hp, hl⟩

theorem conj_nil : Sig.conj [] := trivial

/-! ## Arguments -/

theorem Args.ptr {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) {r : Reg} {p : Ptr}
    (hm : (r, Arg.ptr p) ∈ as := by simp) : s1.gpr r = pa s p := h.1.1 _ hm

theorem Args.imm {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) {r : Reg} {v : Nat}
    (hm : (r, Arg.imm v) ∈ as := by simp) : s1.gpr r = BitVec.ofNat 64 v := h.1.1 _ hm

theorem Args.r0 {r : Reg} {a : Arg} {as : List (Reg × Arg)} {s s1 : State} (h : Args ((r, a) :: as) s s1) :
    s1.gpr r = a.val s := h.1.1 _ (List.mem_cons_self ..)

theorem Args.r1 {r r1 : Reg} {a a1 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem Args.r2 {r r1 r2 : Reg} {a a1 a2 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem Args.r3 {r r1 r2 r3 : Reg} {a a1 a2 a3 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem Args.r4 {r r1 r2 r3 r4 : Reg} {a a1 a2 a3 a4 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))

theorem Args.sp {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) : s1.sp = s.sp := h.2.sp

theorem Args.mem {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) : s1.mem = s.mem := h.1.2

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem ptr_ok {p : Ptr} (h : p.1 ∈ keptRegs) : (Arg.ptr p).Ok := by
  show p.1 ∉ argRegs
  revert h; generalize p.1 = r; cases r <;> decide

theorem SameIn.args {B : List Reg} {as : List (Reg × Arg)} {x y x1 y1 : State} (h : SameIn B x y) (h1 : Args as x x1)
    (h2 : Args as y y1) {r : Reg} {p : Ptr} (hp : p.1 ∈ B) (hm : (r, Arg.ptr p) ∈ as := by simp) :
    x1.gpr r = y1.gpr r := by
  rw [h1.ptr hm, h2.ptr hm, h.pa hp]

theorem SameIn.argi {as : List (Reg × Arg)} {x y x1 y1 : State} (h1 : Args as x x1)
    (h2 : Args as y y1) {r : Reg} {v : Nat} (hm : (r, Arg.imm v) ∈ as := by simp) :
    x1.gpr r = y1.gpr r := by
  rw [h1.imm hm, h2.imm hm]

/-- The facts of a callee's precondition that the layout gives: its stack,
the disjointness of its buffers, and that they do not wrap around. -/
syntax "cpre " term:max : tactic
macro_rules
  | `(tactic| cpre $L) => `(tactic| (
      and_intros
      all_goals first
        | with_reducible rfl
        | exact True.intro
        | exact wfP_of (Lay.spS $L)
        | exact resv fun _ hr => by
            rw [stackBelow_mem hr]
            repeat' first
              | exact conj_nil
              | refine conj_cons (Lay.stkD $L (by assumption)) ?_
        | exact Lay.disj $L (by assumption)
        | exact (Lay.disj $L (by assumption)).symm
        | exact Lay.nwp $L (by assumption)
        | skip))

end VG.Proof.MlDsa.AArch64
