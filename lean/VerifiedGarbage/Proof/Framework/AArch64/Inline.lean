import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Inlining verified code (AArch64)

Untrusted: everything here is checked by Lean. As for x86-64: running code
from a state that permits more memory gives the same result (`Exec.widen`),
code never writes outside the regions its state permits (`Exec.regions`),
and `WP.inline` combines the two with the correctness part of the inlined
function's `Verified` proof.
-/

namespace VG.AArch64

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

theorem Covers.append {rs rs' ts ts' : List Region} (h : Covers rs rs') (h' : Covers ts ts') :
    Covers (rs ++ ts) (rs' ++ ts') := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r', hr', hc'⟩ := h a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_left _ hr', hc'⟩
  · obtain ⟨r', hr', hc'⟩ := h' a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_right _ hr', hc'⟩

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

/-- A frame's push inserts its region into the writable regions of both
states. -/
theorem Covers.push {xs ys xs' ys' : List Region} (f : Region) (h : Covers (xs ++ ys) (xs' ++ ys')) :
    Covers (xs ++ f :: ys) (xs' ++ f :: ys') := fun a n hi =>
  (InRegions_append_cons.mp hi).elim (fun hc => InRegions_append_cons.mpr (.inl hc))
    fun hi => InRegions_append_cons.mpr (.inr (h a n hi))

/-- The register an instruction writes, if any (a frame's pop writes its
register). -/
def dstOf : Instr → Option Reg
  | .add _ d .. | .sub _ d .. | .addImm _ d .. | .subImm _ d .. | .logic _ _ d .. | .ror _ d ..
  | .lsr _ d .. | .rev32 d _ | .rev d _ | .movz _ d .. | .movk _ d .. | .ldr _ d .. | .ldrb d ..
  | .pop d => some d
  | .str .. | .strb .. | .push _ => none

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
  | push _ | pop _ => simp only [exec, reduceCtorEq] at h
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
  | push _ | pop _ => simp only [exec, reduceCtorEq] at h
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
  | push _ | pop _ => simp only [exec, reduceCtorEq] at h
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
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ s₁.gpr = s.gpr ∧ s₁.sp = s.sp - 16 := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h; exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, dstOf j ≠ some r → s'.gpr r = s₂.gpr r) ∧ s₂.sp = s₁.sp ∧ s'.sp = s₂.sp + 16 := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i r hc
  refine ⟨hc.2.1, rfl, rfl, fun r' hr => ?_, hc.1, rfl⟩
  simp only [dstOf, ne_eq, Option.some.injEq] at hr
  simp [State.write, Ne.symm hr]

theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) (rd wr : List Region) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h
  rename_i hc
  exact ⟨_, rfl, rfl, by simp only [isa, push, State.withRegions_sp, hc, ite_true]; rfl⟩

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i hc
  simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, hw, hc.1, hc.2.2, and_self,
    ite_true]
  rfl

/-- Code never changes its permissions or the stack pointer. -/
theorem Exec.rdwr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction h with
  | block h => obtain ⟨r, w, p, -⟩ := execBlock_regions h; exact ⟨r, w, p⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂.1.trans ih₁.1, ih₂.2.1.trans ih₁.2.1, ih₂.2.2.trans ih₁.2.2⟩
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ⟨ih₂.1.trans ih₁.1, ih₂.2.1.trans ih₁.2.1, ih₂.2.2.trans ih₁.2.2⟩
  | call hc _ hr ih =>
    obtain ⟨r₁, w₁, p₁, -⟩ := call_eq hc
    rw [ret_eq hr, ih.1, ih.2.1, ih.2.2, r₁, w₁, p₁]; exact ⟨rfl, rfl, rfl⟩
  | frame hp _ hq ih =>
    obtain ⟨f, r₁, w₁, -, p₁⟩ := push_eq hp
    obtain ⟨-, r₂, w₂, -, p₂, p₃⟩ := pop_eq hq
    refine ⟨r₂.trans (ih.1.trans r₁), by rw [w₂, ih.2.1, w₁]; rfl, ?_⟩
    rw [p₃, ih.2.2, p₁, BitVec.sub_add_cancel]

/-- Code without frames changes memory only within the regions it may write
(a call stores nothing; a frame's push stores below the stack pointer). -/
theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noFrames = true) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  induction h with
  | block h => exact execBlock_regions h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noFrames, Bool.and_eq_true] at hn
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁ hn.1; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂ hn.2
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩
  | iteT _ _ ih => simp only [Code.noFrames, Bool.and_eq_true] at hn; exact ih hn.1
  | iteF _ _ ih => simp only [Code.noFrames, Bool.and_eq_true] at hn; exact ih hn.2
  | loopExit _ _ ih => exact ih hn
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁ hn; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂ hn
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩
  | call hc _ hr ih =>
    obtain ⟨r₁, w₁, p₁, m₁, -⟩ := call_eq hc
    obtain ⟨r₂, w₂, p₂, f₂⟩ := ih hn
    rw [ret_eq hr, r₂, w₂, p₂, r₁, w₁, p₁]
    exact ⟨rfl, rfl, rfl, m₁ ▸ w₁ ▸ f₂⟩
  | frame => simp [Code.noFrames] at hn

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
  induction h generalizing rd wr with
  | block h => exact .block (execBlock_widen hc hw h)
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.rdwr h₁
    exact .seq (ih₁ hc hw) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | iteT hc' _ ih => exact .iteT ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | iteF hc' _ ih => exact .iteF ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | loopExit h₁ hc' ih => exact .loopExit (ih hc hw) ((eval_withRegions _ _ _ _).trans ‹_›)
  | loopNext h₁ hc' _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.rdwr h₁
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
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    obtain ⟨f, r₁, w₁, hp'⟩ := push_widen hp rd wr
    have hq' := pop_widen hq rd (wr := f :: wr) (by rw [w₁]; rfl)
    have hb := ih (rd := rd) (wr := f :: wr) (by rw [r₁, w₁]; exact Covers.push f hc)
      (by rw [w₁]; exact Covers.push (xs := []) (xs' := []) f hw)
    have := Exec.frame hp' hb hq'
    have e₁ : isa.addrs i (s₀.withRegions rd wr) = isa.addrs i s₀ := addrs_withRegions _ _ _ _
    have e₂ : isa.addrs j (s₂.withRegions rd (f :: wr)) = isa.addrs j s₂ :=
      addrs_withRegions _ _ _ _
    rw [e₁, e₂] at this
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
    (hn : c.noCalls = true ∨ r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
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
  | frame hp _ hq ih =>
    rcases hn with hn | hn
    · simp [Code.noCalls] at hn
    · obtain ⟨-, -, -, hg, -⟩ := push_eq hp
      rw [(pop_eq hq).2.2.2.1 r (hc _ (by simp [instrs])),
        ih (fun i hi => hc i (by simp [instrs, hi])) (.inr hn), hg]

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
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he (Code.noFrames_of_noCalls hn)
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl habi hf (fun r hr => Exec.gpr hr he' (.inl hn)) ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hpost

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
    (hsat : ∃ s, k'.pre s) (hn : c.noFrames = true := by decide +kernel) :
    Verified target c k' := by
  refine h.of_narrow (fun s => s.withRegions s.rd (wr s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    hpre (fun s t s₁ hs he => ?_) (fun s t s₁ hs he ha hq => ?_) hpub hsat
  · have hw : Covers (wr s) s.wr := fun _ _ => InRegions.of_prefix (hwr s hs)
    have := Exec.widen (rd := s.rd) (wr := s.wr) he (Covers.append (fun _ _ h => h) hw) hw
    rwa [State.withRegions_withRegions, State.withRegions_self] at this
  · obtain ⟨hr, hw, -⟩ := Exec.regions he hn
    simp only [State.withRegions_rd, State.withRegions_wr] at hr hw
    have : (s₁.withRegions s.rd s.wr).withRegions s.rd (wr s) = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hw]; rfl
    exact ⟨ha, hpost s _ hs (by rw [this]; exact hq)⟩

end VG.AArch64
