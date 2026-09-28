import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Inlining verified code (ARMv7)

Untrusted: everything here is checked by Lean. As for x86-64: running code
from a state that permits more memory gives the same result (`Exec.widen`),
code never writes outside the regions its state permits (`Exec.regions`),
and `WP.inline` combines the two with the correctness part of the inlined
function's `Verified` proof.
-/

namespace VG.Arm

/-- Every access that `rs` permits, `rs'` permits. -/
def Covers (rs rs' : List Region) : Prop := ∀ a n, InRegions rs a n → InRegions rs' a n

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

/-- Sub-regions: each region of `rs` lies at some offset within a region of `rs'`. -/
theorem Covers.of_sub {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := by
  intro a n ⟨r, hr, hc⟩
  obtain ⟨r', hr', off, hb, hl⟩ := h r hr
  refine ⟨r', hr', ?_⟩
  unfold Region.Contains at *
  rw [hb] at hc
  have : (a - r'.base).toNat ≤ (a - (r'.base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - r'.base = (a - (r'.base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- The register an instruction writes, if any. -/
def dstOf : Instr → Option Reg
  | .mov d _ | .dp _ d _ _ | .adds d _ _ | .adc d _ _ | .subs d _ _ | .movw d _ | .movt d _ | .rev d _ | .ldr d _ _
  | .ldrb d _ _ | .ldrSp d _ => some d
  | .cmp .. | .str .. | .strb .. => none

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

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw, hsp, hf⟩ := exec_regions he
    obtain ⟨hr', hw', hsp', hf'⟩ := ih h2
    exact ⟨hr'.trans hr, hw'.trans hw, hsp'.trans hsp, hf.trans (hw ▸ hf')⟩

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

theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  induction h with
  | block h => exact execBlock_regions h
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩
  | call hc _ hr ih =>
    obtain ⟨r₁, w₁, p₁, m₁, -⟩ := call_eq hc
    obtain ⟨r₂, w₂, p₂, f₂⟩ := ih
    rw [ret_eq hr, r₂, w₂, p₂, r₁, w₁, p₁]
    exact ⟨rfl, rfl, rfl, m₁ ▸ w₁ ▸ f₂⟩

theorem execBlock_widen {is : List Instr} {s s' : State} {t : List Leak} {rd wr : List Region}
    (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr)
    (h : execBlock isa is s = some (s', t)) :
    execBlock isa is (s.withRegions rd wr) = some (s'.withRegions rd wr, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw', -⟩ := exec_regions he
    have := ih (s := s₁) (by rwa [hr, hw']) (by rwa [hw']) h2
    simp only [execBlock]
    rw [exec_widen hc hw he]
    simp only [this, Option.map_some, addrs_withRegions]

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) := by
  induction h with
  | block h => exact .block (execBlock_widen hc hw h)
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.regions h₁
    exact .seq (ih₁ hc hw) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | iteT hc' _ ih => exact .iteT ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | iteF hc' _ ih => exact .iteF ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | loopExit h₁ hc' ih => exact .loopExit (ih hc hw) ((eval_withRegions _ _ _ _).trans ‹_›)
  | loopNext h₁ hc' _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.regions h₁
    exact .loopNext (ih₁ hc hw) ((eval_withRegions _ _ _ _).trans ‹_›) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | @call n _ s₀ s₁ s₂ s₃ _ hc₁ _ hr ih =>
    obtain ⟨r₁, w₁, -⟩ := call_eq hc₁
    have hc' : isa.call (s₀.withRegions rd wr) = some (s₁.withRegions rd wr) := by
      simp only [isa, call, Option.some.injEq] at hc₁ ⊢; subst hc₁; rfl
    have hr' : isa.ret (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s₃.withRegions rd wr) := by
      simp only [isa, ret] at hr ⊢
      split at hr <;> cases hr
      rename_i h
      exact (ite_eq_left h).trans rfl
    have := Exec.call (name := n) hc' (ih (by rwa [r₁, w₁]) (by rwa [w₁])) hr'
    exact this

theorem execBlock_gpr {is : List Instr} {r : Reg} (hc : ∀ i ∈ is, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.gpr r = s.gpr r := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
      exec_gpr (hc i (List.mem_cons_self ..)) he]

/-- A register that no instruction writes keeps its value, unless it is
one of `linkRegs` and the code calls a function. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noCalls = true ∨ r ∉ linkRegs := by first | exact .inl (by decide) | exact .inr (by decide)) :
    s'.gpr r = s.gpr r := by
  induction h with
  | block h => exact execBlock_gpr hc h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)) (hn.imp And.right id),
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi)) (hn.imp And.left id)]
  | iteT _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) (hn.imp And.left id)
  | iteF _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) (hn.imp And.right id)
  | loopExit _ _ ih => exact ih hc hn
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hn, ih₁ hc hn]
  | call hc₁ _ hr ih =>
    rcases hn with hn | hn
    · simp [Code.noCalls] at hn
    · rw [ret_eq hr, ih hc (.inr hn), (call_eq hc₁).2.2.2.2 r hn]

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ r ∉ linkRegs := by first | exact .inl (by decide) | exact .inr (by decide)) :
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
    (hn : c.noCalls = true := by decide) : WP isa c s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl habi hf (fun r hr => Exec.gpr hr he' (.inl hn)) ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hpost

end VG.Arm
