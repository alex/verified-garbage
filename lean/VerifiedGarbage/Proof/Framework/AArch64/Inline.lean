import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Inlining verified code (AArch64)

The inlining theory (`Proof/Framework/Inline.lean`) for AArch64 states
(`regionModel`): running code from a state that permits more memory gives
the same result (`Exec.widen`), code never writes outside the regions its
state permits (`Exec.regions`) and never changes the stack pointer
(`Exec.sp`), and `WP.inline` combines these with the correctness part of the
inlined function's `Verified` proof.
-/

namespace VG.AArch64

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

/-- The register an instruction writes, if any (a frame's pop writes its
register). -/
def dstOf : Instr → Option Reg
  | .adds _ d .. | .adcs _ d .. | .subs _ d .. | .sbcs _ d .. | .umulh d .. => some d
  | .add _ d .. | .sub _ d .. | .addImm _ d .. | .subImm _ d .. | .logic _ _ d .. | .logicRor _ _ d .. | .bicRor _ d .. | .ror _ d ..
  | .lsr _ d .. | .lsl _ d .. | .madd _ d .. | .mul _ d .. | .rev32 d _ | .rev d _ | .movz _ d ..
  | .addSp d _ | .movk _ d .. | .ldr _ d .. | .ldrb d .. | .ldrSp d _ | .pop d | .umov _ d .. => some d
  | .str .. | .strb .. | .alloc _ | .free _ | .push _ | .vop _ | .ldrq .. | .strq .. => none

section
variable {s s' : State} {rd wr : List Region}

theorem load_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : s.load a n = some v) : (s.withRegions rd wr).load a n = some v := by
  simp only [State.load] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store_widen (hc : Covers s.wr wr) {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : s.store a n v = some s') : (s.withRegions rd wr).store a n v = some (s'.withRegions rd wr) := by
  simp only [State.store] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem write_withRegions (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    (s.withRegions rd wr).write sz d v = (s.write sz d v).withRegions rd wr := rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := h
    exact ⟨a, ha, v, load_widen hc hv, rfl⟩
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := h
    exact ⟨a, ha, v, load_widen hc hv, rfl⟩
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨a, ha, store_widen hw hs⟩
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨a, ha, store_widen hw hs⟩
  | ldrq t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := h
    exact ⟨a, ha, v, load_widen hc hv, rfl⟩
  | strq t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨a, ha, store_widen hw hs⟩
  | vop op =>
    simp only [exec, Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨d, x⟩, he, rfl⟩ := h
    exact ⟨(d, x), he, rfl⟩
  | ldrSp t off =>
    simp only [exec] at h ⊢
    split at h <;> [rename_i ho; cases h]
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [ho, and_self, ite_true, State.withRegions_sp, load_widen hc hv, Option.map_some]
    rfl
  | push _ | pop _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h ⊢
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (split at h <;> [skip; cases h]
       rename_i hh; simp only [hh, ite_true, Option.some.injEq] at h ⊢; subst h; rfl)

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  cases i with
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).write hr _ hc⟩
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).write hr _ hc⟩
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | strq t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).write hr _ hc⟩
  | ldrq t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | vop op =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | ldrSp t off =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | push _ | pop _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)

theorem exec_gpr {i : Instr} {r : Reg} (hi : dstOf i ≠ some r) (h : exec i s = some s') :
    s'.gpr r = s.gpr r := by
  have hw : ∀ (t : State) sz (d : Reg) (v : BitVec sz.bits), d ≠ r → (t.write sz d v).gpr r = t.gpr r :=
    fun t sz d v hd => by simp [State.write, Ne.symm hd]
  cases i with
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact hw _ _ _ _ fun e => hi (by simp [dstOf, e])
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact hw _ _ _ _ fun e => hi (by simp [dstOf, e])
  | strq t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | ldrq t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | vop op =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, -, rfl⟩ := h
    rfl
  | ldrSp t off =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hw _ _ _ _ fun e => hi (by simp [dstOf, e])
  | push _ | pop _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h
       exact hw _ _ _ _ fun e => hi (by simp [dstOf, e]))
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h
       exact hw _ _ _ _ fun e => hi (by simp [dstOf, e]))

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

/-- The registers a call changes: the link register, and the
intra-procedure-call scratch registers, which a linker veneer may change. -/
def linkRegs : List Reg := [.x16, .x17, .x30]

/-- Calls change only `linkRegs`. -/
theorem call_eq {s s' : State} (h : isa.call s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      ∀ r, r ∉ linkRegs → s'.gpr r = s.gpr r := by
  simp only [isa, call, Option.some.injEq] at h; subst h
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

theorem ret_eq {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s' = s₂ := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

/-- A frame's push adds its region at the head of `wr`, and changes no register. -/
theorem push_eq {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ s₁.gpr = s.gpr ∧ s₁.sp = s.sp - BitVec.ofNat 64 f.len := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, dstOf j ≠ some r → s'.gpr r = s₂.gpr r) ∧ s₂.sp = s₁.sp ∧ s'.sp = s₂.sp + BitVec.ofNat 64 (s₁.wr.headD ⟨0, 0⟩).len := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  case pop r hc =>
    refine ⟨hc.2.1, rfl, rfl, fun r' hr => ?_, hc.1, ?_⟩
    · simp only [dstOf, ne_eq, Option.some.injEq] at hr
      simp [State.write, Ne.symm hr]
    · simp only [List.headD_eq_head?_getD, hc.2.2, Option.getD_some]; rfl
  case free bytes hc =>
    refine ⟨hc.2.2.2.2.1, rfl, rfl, fun _ _ => rfl, hc.2.2.2.1, ?_⟩
    simp only [List.headD_eq_head?_getD, hc.2.2.2.2.2, Option.getD_some]


theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ ∀ rd wr,
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals
    split at h <;> cases h
    rename_i hc
    exact ⟨_, rfl, rfl, fun rd wr => by simp only [isa, push, State.withRegions_sp, hc, ite_true]; rfl⟩

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  case pop r hc =>
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, hw, hc.1, hc.2.2, and_self,
      ite_true]
    rfl
  case free bytes hc =>
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, hw,
      hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.2, and_self, ite_true]
    rfl

/-- The permissions of AArch64 states, for the inlining theory
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
(a call stores nothing; a frame's push stores below the stack pointer). -/
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

/-- The registers `rs`, which no instruction of the code (without calls) writes,
are preserved: checked for all of them at once, by evaluation. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : c.allInstrs (fun i => rs.all fun r => dstOf i != some r) = true)
    (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  rw [Code.allInstrs_eq] at hc
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn)⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Instruction `i` writes none of the registers `rs`: `rs.all fun r => dstOf i != some r`
(`keeps_ofList`), with one lookup in a `RegSet` instead of a comparison of
`dstOf i` with every register of `rs`, which the kernel evaluates several
times faster. -/
def keeps (rs : RegSet Reg) (i : Instr) : Bool :=
  match dstOf i with
  | none => true
  | some d => !rs.mem d

theorem keeps_ofList (rs : List Reg) (i : Instr) :
    keeps (RegSet.ofList rs) i = rs.all fun r => dstOf i != some r := by
  unfold keeps
  cases dstOf i with
  | none => simp
  | some d =>
    rw [Bool.eq_iff_iff, Bool.not_eq_true', ← Bool.not_eq_true, List.all_eq_true]
    show ¬d ∈ RegSet.ofList rs ↔ _
    simp only [RegSet.mem_ofList, bne_iff_ne, ne_eq, Option.some.injEq]
    exact ⟨fun h r hr e => h (e ▸ hr), fun h hd => h d hd rfl⟩

/-- No instruction of `c` writes any of the registers `rs`, checked by evaluating
`keeps` on every instruction (`decide +kernel`). -/
theorem instrs_keeps {c : Prog isa} {rs : List Reg} (h : c.allInstrs (keeps (RegSet.ofList rs)) = true) :
    ((instrs c).all fun i => rs.all fun r => dstOf i != some r) = true := by
  rwa [← Code.allInstrs_eq, ← funext (keeps_ofList rs)]

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

end VG.AArch64
