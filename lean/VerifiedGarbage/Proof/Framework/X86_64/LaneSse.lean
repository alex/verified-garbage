import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# x86-64: AVX2 blocks as SSE blocks on each lane

Most VEX.256 instructions act on each 128-bit lane as an SSE instruction does
on a register (see `VBinOp.sse`). For a block of them (`laneSseBlock`), what
it leaves in lane `l` of the vector registers is what the corresponding SSE
block leaves in the SSE registers of `s.proj l`, the state with lane `l` of
each vector register as its SSE register (`WP.lanes`). A proof about SSE code
then holds of each lane of the AVX2 code that does the same in both lanes.
-/

namespace VG.X86_64

/-- `s` with lane `l` of each vector register as its SSE register, and no
upper halves. -/
def State.proj (s : State) (l : Nat) : State :=
  { s with xmm := fun r => s.lane r l, ymmHi := fun _ => 0, zmmHi := fun _ => 0 }

@[simp] theorem State.proj_xmm (s : State) (l : Nat) (r : XReg) : (s.proj l).xmm r = s.lane r l := rfl
@[simp] theorem State.proj_gpr (s : State) (l : Nat) : (s.proj l).gpr = s.gpr := rfl
@[simp] theorem State.proj_mem (s : State) (l : Nat) : (s.proj l).mem = s.mem := rfl
@[simp] theorem State.proj_rd (s : State) (l : Nat) : (s.proj l).rd = s.rd := rfl
@[simp] theorem State.proj_wr (s : State) (l : Nat) : (s.proj l).wr = s.wr := rfl
@[simp] theorem State.proj_mxcsr (s : State) (l : Nat) : (s.proj l).mxcsr = s.mxcsr := rfl

/-- The SSE instructions that do to one lane what a lane-wise VEX.256
instruction does to each, if it is one: `vop d, a, b` is `movdqa d, a`
then `op d, b` (just `op d, b` if `a` is `d`; not if only `b` is). -/
def laneSseV : VOp → Option (List Instr)
  | .vbin op len d a b =>
    if len ≠ .l256 then none else
    if a = d then some [.xop (.bin op.sse d b)]
    else if b = d then none else some [.xop (.bin .movdqa d a), .xop (.bin op.sse d b)]
  | .vshift op len d a n =>
    if len ≠ .l256 then none else
    if a = d then some [.xop (.shift op d n)] else some [.xop (.bin .movdqa d a), .xop (.shift op d n)]
  | .vpshufd len d a o => if len ≠ .l256 then none else some [.xop (.pshufd d a o)]
  | .vmovdqa len d a => if len ≠ .l256 then none else some [.xop (.bin .movdqa d a)]
  | _ => none

@[inherit_doc laneSseV]
def laneSse : Instr → Option (List Instr)
  | .vop o => laneSseV o
  | _ => none

/-- The SSE block of a block of lane-wise VEX.256 instructions. -/
def laneSseBlock : List Instr → Option (List Instr)
  | [] => some []
  | i :: is => match laneSse i, laneSseBlock is with
    | some a, some b => some (a ++ b)
    | _, _ => none

theorem proj_setV256 (s : State) (d : XReg) (lo hi : BitVec 128) {l : Nat} (_hl : l < 2) :
    (s.setV .l256 d lo hi).proj l = (s.proj l).setXmm d (if l = 0 then lo else hi) := by
  cases s
  simp only [State.proj, State.setV, State.setXmm, State.lane, State.mk.injEq, and_true, true_and]
  funext r
  by_cases h : r = d <;> by_cases h0 : l = 0 <;> simp [h, h0]

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => simp [runBlock]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- What a vector instruction keeps. -/
structure VKeep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  cf : s'.cf = s.cf
  zf : s'.zf = s.zf

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VKeep s₁ s₂) (h₂ : VKeep s₂ s₃) : VKeep s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5, h₂.6.trans h₁.6,
    h₂.7.trans h₁.7⟩

theorem VKeep.setV (s : State) (len : VLen) (d : XReg) (lo hi : BitVec 128) : VKeep s (s.setV len d lo hi) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setXmm_setXmm (s : State) (d : XReg) (v w : BitVec 128) : (s.setXmm d v).setXmm d w = s.setXmm d w := by
  cases s
  simp only [State.setXmm, State.mk.injEq, and_true, true_and]
  funext r
  by_cases h : r = d <;> simp [h]

theorem lane01 {l : Nat} (hl : l < 2) : l = 0 ∨ l = 1 := by omega

theorem laneSse_ok {i : Instr} {ss : List Instr} (h : laneSse i = some ss) (s : State) :
    ∃ s', exec i s = some s' ∧ VKeep s s' ∧ ∀ l < 2, runBlock isa ss (s.proj l) = some (s'.proj l) := by
  cases i
  all_goals try (simp only [laneSse, reduceCtorEq] at h)
  rename_i o
  cases o
  all_goals try (simp only [laneSseV, reduceCtorEq] at h)
  case vbin op len d a b =>
    refine ⟨s.setV len d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)),
      rfl, VKeep.setV .., fun l hl => ?_⟩
    split at h
    · cases h
    rename_i hlen
    simp only [ne_eq, Decidable.not_not] at hlen
    subst hlen
    rw [proj_setV256 _ _ _ _ hl]
    split at h
    · subst_vars; cases h
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
      rcases lane01 hl with rfl | rfl <;> rfl
    · split at h
      · cases h
      · rename_i h1 h2; cases h
        simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
        rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ h2, setXmm_setXmm, eval_movdqa]
        rcases lane01 hl with rfl | rfl <;> rfl
  case vshift op len d a n =>
    refine ⟨s.setV len d (op.eval (s.lane a 0) n) (op.eval (s.lane a 1) n), rfl, VKeep.setV .., fun l hl => ?_⟩
    split at h
    · cases h
    rename_i hlen
    simp only [ne_eq, Decidable.not_not] at hlen
    subst hlen
    rw [proj_setV256 _ _ _ _ hl]
    split at h
    · subst_vars; cases h
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
      rcases lane01 hl with rfl | rfl <;> rfl
    · cases h
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
      rw [RegUpd.xmm_setXmm_self, setXmm_setXmm, eval_movdqa]
      rcases lane01 hl with rfl | rfl <;> rfl
  case vpshufd len d a o =>
    refine ⟨s.setV len d (shufDwords (s.lane a 0) o) (shufDwords (s.lane a 1) o), rfl, VKeep.setV ..,
      fun l hl => ?_⟩
    split at h
    · cases h
    rename_i hlen
    simp only [ne_eq, Decidable.not_not] at hlen
    subst hlen
    cases h
    rw [proj_setV256 _ _ _ _ hl]
    simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
    rcases lane01 hl with rfl | rfl <;> rfl
  case vmovdqa len d a =>
    refine ⟨s.setV len d (s.lane a 0) (s.lane a 1), rfl, VKeep.setV .., fun l hl => ?_⟩
    split at h
    · cases h
    rename_i hlen
    simp only [ne_eq, Decidable.not_not] at hlen
    subst hlen
    cases h
    rw [proj_setV256 _ _ _ _ hl]
    simp only [runBlock, exec, XOp.exec, Option.bind_some, State.proj_xmm]
    rcases lane01 hl with rfl | rfl <;> rfl

theorem laneSseBlock_ok {vs ss : List Instr} (h : laneSseBlock vs = some ss) (s : State) :
    ∃ s', runBlock isa vs s = some s' ∧ VKeep s s' ∧
      ∀ l < 2, runBlock isa ss (s.proj l) = some (s'.proj l) := by
  induction vs generalizing ss s with
  | nil =>
    simp only [laneSseBlock, Option.some.injEq] at h; subst h
    exact ⟨s, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  | cons i is ih =>
    simp only [laneSseBlock] at h
    split at h
    · rename_i a b ha hb
      cases h
      obtain ⟨s₁, e₁, k₁, p₁⟩ := laneSse_ok ha s
      obtain ⟨s₂, e₂, k₂, p₂⟩ := ih hb s₁
      refine ⟨s₂, by show (exec i s).bind _ = _; rw [e₁, Option.bind_some]; exact e₂, k₁.trans k₂,
        fun l hl => ?_⟩
      rw [runBlock_append, p₁ l hl, Option.bind_some, p₂ l hl]
    · cases h

theorem WP.runBlock_of {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q) :
    ∃ s', runBlock isa is s = some s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact ⟨s, rfl, WP.block_nil_iff.mp h⟩
  | cons i is ih =>
    obtain ⟨s₁, e₁, h₁⟩ := WP.block_cons_iff.mp h
    obtain ⟨s', e', q⟩ := ih h₁
    exact ⟨s', by rw [show runBlock isa (i :: is) s = (isa.exec i s).bind (runBlock isa is) from rfl, e₁, Option.bind_some]; exact e', q⟩

/-- A block of lane-wise VEX.256 instructions does to each lane what its SSE
block does to the SSE registers. -/
theorem WP.lanes {vs ss : List Instr} (h : laneSseBlock vs = some ss) {s : State} {Q : Nat → State → Prop}
    (hq : ∀ l < 2, WP isa (.block ss) (s.proj l) (Q l)) :
    WP isa (.block vs) s fun s' => VKeep s s' ∧ ∀ l < 2, Q l (s'.proj l) := by
  obtain ⟨s', e, k, p⟩ := laneSseBlock_ok h s
  refine WP.of_runBlock ⟨s', e, k, fun l hl => ?_⟩
  obtain ⟨t, et, qt⟩ := WP.runBlock_of (hq l hl)
  rw [p l hl, Option.some.injEq] at et
  exact et ▸ qt

end VG.X86_64
