import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Inlining verified code (ARMv7)

The inlining theory (`Proof/Framework/Inline.lean`) for ARMv7 states
(`regionModel`): running code from a state that permits more memory gives
the same result (`Exec.widen`), code never writes outside the regions its
state permits (`Exec.regions`) and never changes the stack pointer
(`Exec.sp`), and `WP.inline` combines these with the correctness part of the
inlined function's `Verified` proof.
-/

namespace VG.Arm

/-- `s`, permitted to read `rd` and write `wr` instead. -/
def State.withRegions (s : State) (rd wr : List Region) : State := { s with rd := rd, wr := wr }

@[simp] theorem State.withRegions_gpr (s : State) (rd wr) : (s.withRegions rd wr).gpr = s.gpr := rfl
@[simp] theorem State.withRegions_sp (s : State) (rd wr) : (s.withRegions rd wr).sp = s.sp := rfl
@[simp] theorem State.withRegions_mem (s : State) (rd wr) : (s.withRegions rd wr).mem = s.mem := rfl
@[simp] theorem State.withRegions_rd (s : State) (rd wr) : (s.withRegions rd wr).rd = rd := rfl
@[simp] theorem State.withRegions_wr (s : State) (rd wr) : (s.withRegions rd wr).wr = wr := rfl
@[simp] theorem State.withRegions_self (s : State) : s.withRegions s.rd s.wr = s := rfl
@[simp] theorem State.withRegions_withRegions (s : State) (rd wr rd' wr') :
    (s.withRegions rd wr).withRegions rd' wr' = s.withRegions rd' wr' := rfl

@[simp] theorem stackArg_withRegions (s : State) (rd wr) (i : Nat) :
    stackArg (s.withRegions rd wr) i = stackArg s i := rfl
@[simp] theorem stackArgAddr_withRegions (s : State) (rd wr) (i : Nat) :
    stackArgAddr (s.withRegions rd wr) i = stackArgAddr s i := rfl

/-- The register an instruction writes, if any (a frame's pop writes its
register). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .dp _ d _ _ | .adds d _ _ | .adc d _ _ | .subs d _ _ | .movw d _ | .movt d _ | .rev d _
  | .addSp d _ | .mul d _ _ | .ldr d _ _ | .ldrb d _ _ | .ldrSp d _ | .pop d _ => some d
  | .cmp .. | .str .. | .strb .. | .push _ | .alloc _ | .free _ => none

section
variable {s s' : State} {rd wr : List Region}

@[simp] theorem State.withRegions_n (s : State) (rd wr) : (s.withRegions rd wr).n = s.n := rfl
@[simp] theorem State.withRegions_z (s : State) (rd wr) : (s.withRegions rd wr).z = s.z := rfl

theorem setReg_withRegions (d : Reg) (v : BitVec 32) :
    (s.withRegions rd wr).setReg d v = (s.setReg d v).withRegions rd wr := rfl

theorem addFlags_withRegions (x y : BitVec 32) :
    addFlags (s.withRegions rd wr) x y = (addFlags s x y).withRegions rd wr := rfl

theorem subFlags_withRegions (x y : BitVec 32) :
    subFlags (s.withRegions rd wr) x y = (subFlags s x y).withRegions rd wr := rfl

theorem op2_withRegions (o : Op2) : o.eval (s.withRegions rd wr) = o.eval s := by
  cases o <;> rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | ldr t n off | ldrb t n off | ldrSp t off =>
    simp only [exec, State.load32, State.load8] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hoff
    simp only [hoff, ite_true] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_gpr,
      State.withRegions_sp, hc _ _ hi, ite_true, Option.map_some]
    rfl
  | str t n off | strb t n off =>
    simp only [exec, State.store32, State.store8] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hoff
    simp only [hoff, ite_true] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    simp only [State.withRegions_wr, State.withRegions_gpr, hw _ _ hi, ite_true]
    rfl
  | addSp d imm =>
    simp only [exec] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hi
    simp only [hi, ite_true, Option.some.injEq] at h ⊢
    subst h; rfl
  | push _ | pop _ _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec, op2_withRegions, Option.map_eq_some_iff] at h ⊢
    first
    | (obtain ⟨y, hy, rfl⟩ := h; exact ⟨y, hy, rfl⟩)
    | (simp only [Option.some.injEq] at h ⊢; subst h; rfl)

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  cases i with
  | str t n off | strb t n off =>
    simp only [exec, State.store32, State.store8] at h
    split at h <;> [skip; cases h]
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).writeW hr _ hc⟩
  | _ =>
    simp only [exec, State.load32, State.load8, Option.map_eq_some_iff] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)
    | (cases h)

theorem exec_gpr {i : Instr} {r : Reg} (hi : dstOf i ≠ some r) (h : exec i s = some s') :
    s'.gpr r = s.gpr r := by
  have hs : ∀ (t : State) (d : Reg) (v : BitVec 32), d ≠ r → (t.setReg d v).gpr r = t.gpr r :=
    fun t d v hd => by simp [State.setReg, Ne.symm hd]
  cases i <;>
  simp only [exec, State.load32, State.load8, State.store32, State.store8, Option.map_eq_some_iff] at h <;>
  (repeat' split at h) <;>
  (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
  first
  | (subst h; first | rfl | (exact hs _ _ _ fun e => hi (by simp [dstOf, e])))
  | (obtain ⟨_, _, rfl⟩ := h
     first
     | rfl
     | (exact hs _ _ _ fun e => hi (by simp [dstOf, e])))
  | (cases h)

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

/-- The registers a call changes: the link register, and the
intra-procedure-call scratch registers, which a linker veneer may change. -/
def linkRegs : List Reg := [.r12, .lr]

/-- Calls change only `linkRegs`. -/
theorem call_eq {s s' : State} (h : isa.call s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      ∀ r, r ∉ linkRegs → s'.gpr r = s.gpr r := by
  simp only [isa, call, Option.some.injEq] at h; subst h
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.setReg, hr.1, hr.2, ite_false]

theorem ret_eq {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s' = s₂ := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

/-- A frame's push adds its region at the head of `wr`, and changes no register. -/
theorem push_eq {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ n, s₁.rd = s.rd ∧ s₁.wr = ⟨State.addr s₁.sp, n⟩ :: s.wr ∧ s₁.gpr = s.gpr ∧
      s₁.sp = s.sp - BitVec.ofNat 32 n := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, dstOf j ≠ some r → s'.gpr r = s₂.gpr r) ∧ s₂.sp = s₁.sp ∧
      ∃ n, s₁.wr.head? = some ⟨State.addr s₁.sp, n⟩ ∧ s'.sp = s₂.sp + BitVec.ofNat 32 n := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  case pop r n hc =>
    refine ⟨hc.2.2.2.1, rfl, rfl, fun r' hr => ?_, hc.2.2.1, _, hc.2.2.2.2, rfl⟩
    simp only [dstOf, ne_eq, Option.some.injEq] at hr
    simp [State.setReg, Ne.symm hr]
  case free bytes hc =>
    exact ⟨hc.2.2.2.2.2.1, rfl, rfl, fun _ _ => rfl, hc.2.2.2.2.1, _, hc.2.2.2.2.2.2, rfl⟩

theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ ∀ rd wr,
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals
    split at h <;> cases h
    rename_i hc
    exact ⟨_, rfl, rfl, fun rd wr => by simp only [isa, push, State.withRegions_sp, hc, and_self, ite_true]; rfl⟩

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  case pop r n hc =>
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, hw, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.2, and_self, ite_true]
    rfl
  case free bytes hc =>
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, hw,
      hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.2, and_self, ite_true]
    rfl

/-- The permissions of ARMv7 states, for the inlining theory
(`Proof/Framework/Inline.lean`). -/
def regionModel : RegionModel isa where
  rd := State.rd
  wr := State.wr
  mem := State.mem
  withRegions := State.withRegions
  rd_with _ _ _ := rfl
  wr_with _ _ _ := rfl
  mem_with _ _ _ := rfl
  with_self _ := rfl
  with_with _ _ _ _ _ := rfl
  exec_regions h := ⟨(exec_regions h).1, (exec_regions h).2.1, (exec_regions h).2.2.2⟩
  exec_widen hc hw h := exec_widen hc hw h
  addrs_with := addrs_withRegions
  eval_with := eval_withRegions
  callAddrs_with _ _ _ := rfl
  retAddrs_with _ _ _ := rfl
  call_widen h := by
    simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  ret_widen h := by
    simp only [isa, ret] at h; split at h <;> cases h; rename_i hc
    exact ⟨rfl, rfl, fun _ _ => (ite_eq_left hc).trans rfl⟩
  push_widen := push_widen
  pop_widen h := ⟨(pop_eq h).1, (pop_eq h).2.1, (pop_eq h).2.2.1, fun _ _ hw => pop_widen h _ hw⟩
/-- Calls change no memory, and returns nothing. -/
theorem callsKeepMem : regionModel.CallsKeepMem := fun _ _ _ _ hc hr =>
  ⟨(call_eq hc).2.2.2.1, by rw [ret_eq hr]⟩

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem :=
  let ⟨r, w, f⟩ := regionModel.execBlock_regions h
  ⟨r, w, execBlock_sp h, f⟩

/-- Code never changes its permissions or the stack pointer. -/
theorem Exec.rdwr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨(regionModel.rdwr h).1, (regionModel.rdwr h).2, Exec.sp h⟩

/-- Code without frames changes memory only within the regions it may write
(a frame's push stores below the stack pointer). -/
theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noFrames = true) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem :=
  let ⟨r, w, f⟩ := regionModel.regions h hn (.inr callsKeepMem)
  ⟨r, w, Exec.sp h, f⟩

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) :=
  regionModel.widen h hc hw

theorem execBlock_gpr {is : List Instr} {r : Reg} (hc : ∀ i ∈ is, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.gpr r = s.gpr r :=
  execBlock_keep (fun s : State => s.gpr r) exec_gpr hc h

/-- A register that no instruction writes keeps its value, unless it is
one of `linkRegs` and the code calls a function. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noCalls = true ∨ r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    s'.gpr r = s.gpr r := by
  refine Exec.keep (fun s : State => s.gpr r) exec_gpr (fun hj hp hq hb => ?_) hc
    (hn.imp id fun hl _ _ _ _ hc hr hb => ?_) h
  · obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r hj, hb, hg]
  · rw [ret_eq hr, hb, (call_eq hc).2.2.2.2 r hl]

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he hn⟩

/-- Inlining verified code: from a state `s` in which the code's precondition
holds once its permissions are narrowed to `rd` and `wr`, the code
terminates in a state satisfying its postcondition and calling-convention
obligations (both on the narrowed states), which has the permissions of `s`,
differs from it in memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, dstOf i ≠ some r) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q :=
  regionModel.wp_narrow (hv _ hpre) hc hw (Code.noFrames_of_noCalls hn) (.inl hn)
    fun _ _ he hr hw hf hp => hQ _ hr hw hp.1 hf (fun _ h => Exec.gpr h he (.inl hn)) hp.2

/-- `WP.inline` for code that makes calls (but has no frames): the
registers kept are those no instruction writes, other than those a call
changes (`linkRegs`). -/
theorem WP.inlineCalls {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, dstOf i ≠ some r) → r ∉ linkRegs → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true := by decide +kernel) : WP isa c s Q :=
  regionModel.wp_narrow (hv _ hpre) hc hw hn (.inr callsKeepMem)
    fun _ _ he hr hw hf hp => hQ _ hr hw hp.1 hf (fun _ h hl => Exec.gpr h he (.inr hl)) hp.2

/-- Widening writable regions: code verified against `k` is verified against
a contract `k'` whose states permit writing regions that extend (same bases,
at least as long) the ones `k` permits (`wr s`), reading the same ones, if
`k'` asks nothing more. The code runs as it does from the narrowed state,
with the same trace and result. -/
theorem Verified.widen {c : Prog isa} {k k' : Contract isa} (h : Verified target c k)
    (wr : State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (s.withRegions s.rd (wr s)))
    (hwr : ∀ s, k'.pre s → List.Forall₂ Region.Prefix (wr s) s.wr)
    (hpost : ∀ s s', k'.pre s →
      k.post (s.withRegions s.rd (wr s)) (s'.withRegions s.rd (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (s₁.withRegions s₁.rd (wr s₁)) (s₂.withRegions s₂.rd (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified target c k' :=
  regionModel.verified_widen (T := target) (fun _ _ _ _ h => h) h wr hpre hwr hpost hpub hsat

end VG.Arm
