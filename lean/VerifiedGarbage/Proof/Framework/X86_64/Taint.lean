import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Taint tracking for x86-64

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public, whether the
(modelled) flags are public, and what is known about memory. Memory is secret
unless known otherwise: an address must be computed from public registers,
and a value loaded from memory is secret unless it comes from a *public
slot*.

Public slots let public values survive a round trip through memory, e.g.
callee-saved registers saved and restored around inlined code. They are byte
ranges of the writable regions `s.wr` (identified by index) that hold the
same bytes in both runs. To keep them sound in the presence of stores of
secrets, the analysis knows the lengths of the writable regions (`lens`,
whose regions are then pairwise disjoint and the same in both runs) and
which registers point at a known offset into which region (`bases`). A
store through such a register, at a known offset, can only change bytes of
its own region at that offset; any other store of a secret forgets every
slot.

A public 32-bit argument is public only in the low half of its register
(`lo`): `mov32` from such a register gives a public register. Only stores
keep `lo`; any other instruction forgets it, so code reads such an argument
first.
-/

namespace VG.X86_64.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- The lengths of the writable regions `s.wr`, in order; `[]` if unknown. -/
  lens : List Nat := []
  /-- `(r, i, k)`: register `r` holds the address of byte `k` of writable region `i`. -/
  bases : List (Reg × Nat × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  /-- Registers whose low 32 bits are public (a public 32-bit argument, whose
  upper half is whatever the caller left there). Only stores keep them. -/
  lo : RegSet Reg := .empty
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The registers `regs` and, if `flags`, the flags are the same in both states. -/
def AgreeRF (regs : RegSet Reg) (flags : Bool) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ regs, s₁.gpr r = s₂.gpr r) ∧
  (flags = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)

/-- What `τ` says about each state on its own. -/
def Wf (τ : T) (s : State) : Prop :=
  (τ.lens ≠ [] →
    s.wr.map Region.len = τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧ ∀ r ∈ s.wr, r.len ≤ 2 ^ 64) ∧
  (∀ p ∈ τ.bases, s.gpr p.1 = (region s p.2.1).base + BitVec.ofNat 64 p.2.2)

/-- Every slot lies within its region. -/
def SlotsOk (τ : T) : Prop := ∀ sl ∈ τ.slots, sl.2.1 + sl.2.2 ≤ τ.lens.getD sl.1 0

def SlotsAgree (τ : T) (s₁ s₂ : State) : Prop :=
  ∀ sl ∈ τ.slots, ∀ k, sl.2.1 ≤ k → k < sl.2.1 + sl.2.2 →
    s₁.mem (byteAddr s₁ sl.1 k) = s₂.mem (byteAddr s₂ sl.1 k)

structure Agree (τ : T) (s₁ s₂ : State) : Prop where
  rf : AgreeRF τ.regs τ.flags s₁ s₂
  wr : τ.lens ≠ [] → s₁.wr = s₂.wr
  wf₁ : Wf τ s₁
  wf₂ : Wf τ s₂
  ok : SlotsOk τ
  slots : SlotsAgree τ s₁ s₂
  lo : ∀ r ∈ τ.lo, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat × Nat) := τ.bases.filter (·.1 != d)

def memPub (τ : T) (m : MemOp) : Bool :=
  pub τ m.base && match m.index with
    | none => true
    | some i => pub τ i

/-- The region and offset addressed by `m`, if known. -/
def addrOf (τ : T) (m : MemOp) : Option (Nat × Nat) :=
  if m.index = none ∧ 0 ≤ m.disp then
    (τ.bases.find? (·.1 == m.base)).map fun p => (p.2.1, p.2.2 + m.disp.toNat)
  else none

/-- `w` bytes at `m` are within a public slot. -/
def slotPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  match addrOf τ m with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

/-- The addresses the operand accesses are public. -/
def srcOk (τ : T) : Src → Bool
  | .mem m => memPub τ m
  | _ => true

/-- The operand's value is public (memory operands aside). -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pub τ r
  | .imm _ => true
  | .mem _ => false

/-- The operand is a register whose low 32 bits are public. -/
def loPub (τ : T) : Src → Bool
  | .reg r => τ.lo.mem r
  | _ => false

/-- A `w`-byte memory operand reads a public slot. -/
def loadPub (τ : T) (w : Nat) : Src → Bool
  | .mem m => slotPub τ m w
  | _ => false

/-- The known region bases after `mov d, src`. -/
def movBases (τ : T) (d : Reg) : Src → List (Reg × Nat × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | _ => kill τ d

/-- The public slots after storing `w` bytes at `m`, a public value iff `p`. -/
def storeSlots (τ : T) (m : MemOp) (w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ m with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

def storeStep (τ : T) (m : MemOp) (w : Nat) (p : Bool) : Option T :=
  if memPub τ m then some { τ with slots := storeSlots τ m w p } else none

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- The known region bases after `op d, src`: a 64-bit `add` of a
non-negative immediate moves a pointer that far into its region. -/
def aluBases (τ : T) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) : List (Reg × Nat × Nat) :=
  match op, src with
  | .add, .imm v =>
    if wide && !v.msb then kill τ d ++ (τ.bases.filter (·.1 == d)).map fun p => (d, p.2.1, p.2.2 + v.toNat)
    else kill τ d
  | _, _ => kill τ d

def aluStep (τ : T) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) : Option T :=
  if srcOk τ src then
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    some { τ with
      regs := if writes op then set τ d p else τ.regs, flags := p, bases := aluBases τ op d src wide, lo := .empty }
  else none

/-- `mul r`: `rax`, `rdx` and the flags are functions of the old `rax` and
`r` (SF and ZF become undefined in both runs). -/
def mulStep (τ : T) (r : Reg) : T :=
  let p := pub τ .rax && pub τ r
  { τ with regs := if p then (τ.regs.insert .rax).insert .rdx else (τ.regs.erase .rax).erase .rdx,
           flags := p, bases := (kill τ .rax).filter (·.1 != .rdx) }

def step (τ : T) : Instr → Option T
  | .mov d src =>
    if srcOk τ src then
      some { τ with regs := set τ d (srcPub τ src || loadPub τ 8 src), bases := movBases τ d src, lo := .empty }
    else none
  | .mov32 d src =>
    if srcOk τ src then
      some { τ with
        regs := set τ d (srcPub τ src || loadPub τ 4 src || loPub τ src), bases := kill τ d, lo := .empty }
    else none
  | .store m r => storeStep τ m 8 (pub τ r)
  | .store32 m r => storeStep τ m 4 (pub τ r)
  | .store8 m r => storeStep τ m 1 (pub τ r)
  | .alu op d src => aluStep τ op d src true
  | .alu32 op d src => aluStep τ op d src false
  -- The result is a function of the old value of `d`, and so are the
  -- flags that change.
  | .shift32 _ d _ | .shift _ d _ =>
    some { τ with flags := τ.flags && pub τ d, bases := kill τ d, lo := .empty }
  | .bswap32 d | .bswap d => some { τ with bases := kill τ d, lo := .empty }
  | .movImm64 d _ => some { τ with regs := set τ d true, bases := kill τ d, lo := .empty }
  | .movzx8 d m =>
    if memPub τ m then some { τ with regs := set τ d false, bases := kill τ d, lo := .empty } else none
  -- The SSE registers are not tracked: their values are always secret, and
  -- no modelled instruction moves them into a general-purpose register or
  -- the flags.
  | .movdquLoad _ m => if memPub τ m then some τ else none
  | .movdquStore m _ => storeStep τ m 16 false
  | .xop _ | .vop _ => some τ
  | .vmovdquLoad _ _ m | .vbroadcasti128 _ m => if memPub τ m then some τ else none
  | .vmovdquStore .l128 m _ => storeStep τ m 16 false
  | .vmovdquStore .l256 m _ => storeStep τ m 32 false
  -- MXCSR is not tracked either: nothing moves it into a general-purpose
  -- register or the flags, and it is stored as a secret.
  | .stmxcsr m => storeStep τ m 4 false
  | .ldmxcsr m => if memPub τ m then some τ else none
  | .lfence => some τ
  | .mul r => some (mulStep τ r)

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  lo := τ₁.lo.inter τ₂.lo

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) && τ.lo.subset σ.lo

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := Iff.rfl

section
variable {τ : T} {s₁ s₂ : State}

theorem Agree.reg (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) : s₁.gpr r = s₂.gpr r :=
  h.rf.1 r (pub_iff.mp hr)

theorem Agree.ea (h : Agree τ s₁ s₂) {m : MemOp} (hm : memPub τ m = true) : s₁.ea m = s₂.ea m := by
  simp only [memPub, Bool.and_eq_true] at hm
  obtain ⟨hb, hi⟩ := hm
  unfold State.ea
  split <;> rename_i heq <;> rw [heq] at hi <;> simp only at hi
  · rw [h.reg hb]
  · rw [h.reg hb, h.reg hi]

theorem Agree.srcAddrs (h : Agree τ s₁ s₂) {src : Src} (hs : srcOk τ src = true) :
    X86_64.srcAddrs s₁ src = X86_64.srcAddrs s₂ src := by
  cases src <;> simp only [X86_64.srcAddrs]
  simp only [srcOk] at hs
  rw [h.ea hs]

theorem Agree.readSrc (h : Agree τ s₁ s₂) {src : Src} (hs : srcPub τ src = true) :
    readSrc s₁ src = readSrc s₂ src := by
  cases src with
  | reg r => exact congrArg some (h.reg hs)
  | imm v => rfl
  | mem m => simp [srcPub] at hs

theorem Agree.readSrc32 (h : Agree τ s₁ s₂) {src : Src} (hs : srcPub τ src = true) :
    readSrc32 s₁ src = readSrc32 s₂ src := by
  cases src with
  | reg r => exact congrArg (fun x => some (BitVec.setWidth 32 x)) (h.reg hs)
  | imm v => rfl
  | mem m => simp [srcPub] at hs

end

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    ∀ r ∈ set τ d p, (s₁.setReg d v₁).gpr r = (s₂.setReg d v₂).gpr r := by
  intro r hr
  simp only [State.setReg]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hr
    simp [hr.1, h r hr.2]

/-! ### ALU instructions, uniformly -/

/-- The result, carry and overflow of an ALU operation at width `w`. -/
def aluOut {w : Nat} (op : AluOp) (a b : BitVec w) (cf : Option Bool) :
    Option (BitVec w × Bool × Bool) :=
  match op with
  | .add => let r := a + b; some (r, 2 ^ w ≤ a.toNat + b.toNat, addOverflow a b r)
  | .adc => cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth w
    (r, 2 ^ w ≤ a.toNat + b.toNat + c.toNat, addOverflow a b r)
  | .sub | .cmp => let r := a - b; some (r, a.toNat < b.toNat, subOverflow a b r)
  | .sbb => cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth w
    (r, a.toNat < b.toNat + c.toNat, subOverflow a b r)
  | .and | .test => some (a &&& b, false, false)
  | .or => some (a ||| b, false, false)
  | .xor => some (a ^^^ b, false, false)

theorem aluOut_cf {w : Nat} {op : AluOp} (h : usesCarry op = false) (a b : BitVec w)
    (c c' : Option Bool) : aluOut op a b c = aluOut op a b c' := by
  cases op <;> simp_all [usesCarry, aluOut]

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (readSrc s src).bind fun b =>
      (aluOut op (s.gpr d) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg d r else arithFlags s r c o := by
  cases op <;> simp [execAlu, aluOut, writes, Function.comp_def]

theorem execAlu32_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu32 op d src s = (readSrc32 s src).bind fun b =>
      (aluOut op ((s.gpr d).setWidth 32) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg32 d r else arithFlags s r c o := by
  cases op <;> simp [execAlu32, aluOut, writes, Function.comp_def]

section
variable {s : State} {r : Reg} {w : Nat} {v : BitVec 64} {x : BitVec w} {c o : Bool}
@[simp] theorem arithFlags_gpr : (arithFlags s x c o).gpr = s.gpr := rfl
@[simp] theorem arithFlags_cf : (arithFlags s x c o).cf = some c := rfl
@[simp] theorem arithFlags_of : (arithFlags s x c o).of = some o := rfl
@[simp] theorem arithFlags_zf : (arithFlags s x c o).zf = some (x == 0) := rfl
@[simp] theorem arithFlags_sf : (arithFlags s x c o).sf = some x.msb := rfl
@[simp] theorem setReg_cf : (s.setReg r v).cf = s.cf := rfl
@[simp] theorem setReg_of : (s.setReg r v).of = s.of := rfl
@[simp] theorem setReg_zf : (s.setReg r v).zf = s.zf := rfl
@[simp] theorem setReg_sf : (s.setReg r v).sf = s.sf := rfl
end

theorem regs_filter {τ : T} {s₁ s₂ s₁' s₂' : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} (h₁ : ∀ r, r ≠ d → s₁'.gpr r = s₁.gpr r) (h₂ : ∀ r, r ≠ d → s₂'.gpr r = s₂.gpr r) :
    ∀ r ∈ τ.regs.erase d, s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  simp only [RegSet.mem_erase] at hr
  rw [h₁ r hr.1, h₂ r hr.1, h r hr.2]

theorem not_pub_set {τ : T} {d : Reg} {p : Bool} (hp : ¬ p = true) : set τ d p = τ.regs.erase d := by
  simp [set, hp]

/-- ALU soundness, for both widths: `wr` writes the result register. -/
theorem alu_sound {w : Nat} {τ : T} {op : AluOp} {d : Reg} {src : Src} {s₁ s₂ : State}
    {b₁ b₂ : BitVec w} {out₁ out₂ : BitVec w × Bool × Bool}
    (ha : Agree τ s₁ s₂) (get : State → BitVec w) (wr : State → BitVec w → State)
    (hget : s₁.gpr d = s₂.gpr d → get s₁ = get s₂)
    (hwr : ∀ s x r, (wr s x).gpr r = if r = d then (wr s x).gpr d else s.gpr r)
    (hwrd : ∀ s₁ s₂ x, (wr s₁ x).gpr d = (wr s₂ x).gpr d)
    (hwrf : ∀ s x, (wr s x).cf = s.cf ∧ (wr s x).zf = s.zf ∧ (wr s x).sf = s.sf ∧ (wr s x).of = s.of)
    (hb : srcPub τ src = true → b₁ = b₂)
    (ho₁ : aluOut op (get s₁) b₁ s₁.cf = some out₁) (ho₂ : aluOut op (get s₂) b₂ s₂.cf = some out₂) :
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    AgreeRF (if writes op then set τ d p else τ.regs) p
      (if writes op then wr (arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2) out₁.1
        else arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2)
      (if writes op then wr (arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) out₂.1
        else arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) := by
  intro p
  by_cases hp : p = true
  · have hp' := hp
    simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp'
    obtain ⟨⟨hd, hsp⟩, hc⟩ := hp'
    obtain rfl := hb hsp
    have hout : aluOut op (get s₁) b₁ s₁.cf = aluOut op (get s₂) b₁ s₂.cf := by
      rw [hget (ha.reg hd)]
      rcases hc with hc | hc
      · exact aluOut_cf hc _ _ _ _
      · rw [(ha.rf.2 hc).1]
    rw [hout, ho₂] at ho₁
    cases ho₁
    refine ⟨fun r hr => ?_, fun _ => ?_⟩
    · split
      · rename_i hw
        simp only [hw, ite_true] at hr
        rw [hwr _ _ r, hwr (arithFlags s₂ _ _ _) _ r]
        split
        · exact hwrd _ _ _
        · rename_i hrd
          simp only [set, hp, ite_true, RegSet.mem_insert, hrd, false_or] at hr
          simpa using ha.rf.1 r hr
      · rename_i hw
        simp only [hw, Bool.false_eq_true, ite_false] at hr ⊢
        simpa using ha.rf.1 r hr
    · split <;> simp [hwrf]
  · refine ⟨fun r hr => ?_, fun h => absurd h hp⟩
    split
    · rename_i hw
      simp only [hw, ite_true, not_pub_set hp] at hr
      refine regs_filter ha.rf.1 (fun r hr => ?_) (fun r hr => ?_) r hr <;>
        (rw [hwr]; simp [hr])
    · rename_i hw
      simp only [hw, Bool.false_eq_true, ite_false] at hr
      simpa using ha.rf.1 r hr

theorem setReg_gpr_eq (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then (s.setReg d v).gpr d else s.gpr r := by
  simp only [State.setReg]; split <;> simp_all


/-! ### Region bases, slots and memory -/

/-- Nothing about low halves is known. -/
theorem noLo {s₁ s₂ : State} : ∀ r ∈ (RegSet.empty : RegSet Reg), (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32 :=
  fun r h => absurd h (RegSet.not_mem_empty r)

theorem Agree.keep {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem)
    (hb₁ : ∀ p ∈ τ'.bases, s₁'.gpr p.1 = (region s₁' p.2.1).base + BitVec.ofNat 64 p.2.2)
    (hb₂ : ∀ p ∈ τ'.bases, s₂'.gpr p.1 = (region s₂' p.2.1).base + BitVec.ofNat 64 p.2.2)
    (hlo : ∀ r ∈ τ'.lo, (s₁'.gpr r).setWidth 32 = (s₂'.gpr r).setWidth 32) :
    Agree τ' s₁' s₂' where
  lo := hlo
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ⟨fun h => by rw [hw₁, hl]; exact ha.wf₁.1 (hl ▸ h), hb₁⟩
  wf₂ := ⟨fun h => by rw [hw₂, hl]; exact ha.wf₂.1 (hl ▸ h), hb₂⟩
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    simp only [byteAddr, region, hw₁, hw₂, hm₁, hm₂]
    exact ha.slots sl (hs ▸ h) k h₁ h₂

theorem kill_bases {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr) {d : Reg}
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) :
    ∀ p ∈ kill τ d, s'.gpr p.1 = (region s' p.2.1).base + BitVec.ofNat 64 p.2.2 := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [hg _ hp.2, hw.2 p hp.1]
  simp [region, hwr]

theorem setReg_ne {s : State} {d r : Reg} {v : BitVec 64} (h : r ≠ d) : (s.setReg d v).gpr r = s.gpr r := by
  simp [State.setReg, h]

theorem kill_setReg {τ : T} {s : State} (hw : Wf τ s) (d : Reg) (v : BitVec 64) :
    ∀ p ∈ kill τ d, (s.setReg d v).gpr p.1 = (region (s.setReg d v) p.2.1).base + BitVec.ofNat 64 p.2.2 :=
  kill_bases (s' := s.setReg d v) hw rfl fun _ h => setReg_ne h

theorem movBases_ok {τ : T} {s : State} (hw : Wf τ s) {d : Reg} {src : Src} {v : BitVec 64}
    (hv : readSrc s src = some v) :
    ∀ p ∈ movBases τ d src,
      (s.setReg d v).gpr p.1 = (region (s.setReg d v) p.2.1).base + BitVec.ofNat 64 p.2.2 := by
  cases src with
  | reg r =>
    simp only [readSrc, Option.some.injEq] at hv
    subst hv
    intro p hp
    simp only [movBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    rcases hp with hp | ⟨q, ⟨hq, rfl⟩, rfl⟩
    · exact kill_setReg hw d _ p hp
    · simp only [State.setReg, ite_true]
      exact hw.2 q hq
  | imm _ => exact kill_setReg hw d _
  | mem _ => exact kill_setReg hw d _

theorem addrOf_some {τ : T} {m : MemOp} {i d : Nat} (h : addrOf τ m = some (i, d)) :
    ∃ k, m.index = none ∧ (m.base, i, k) ∈ τ.bases ∧ m.disp = ((d - k : Nat) : Int) ∧ k ≤ d := by
  unfold addrOf at h
  split at h <;> [skip; cases h]
  rename_i hc
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hq
  have hb := List.find?_some hq
  simp only [beq_iff_eq] at hb
  refine ⟨q.2.2, hc.1, ?_, by rw [Nat.add_sub_cancel_left, Int.toNat_of_nonneg hc.2], by omega⟩
  rw [← hb]; exact hm

theorem ea_of_addrOf {τ : T} {s : State} (hw : Wf τ s) {m : MemOp} {i d : Nat}
    (h : addrOf τ m = some (i, d)) : s.ea m = byteAddr s i d := by
  obtain ⟨k, hi, hb, hd, hk⟩ := addrOf_some h
  simp only [State.ea, hi, hd, byteAddr, hw.2 _ hb]
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hk]

theorem byteAddr_add (s : State) (i d k : Nat) :
    byteAddr s i d + BitVec.ofNat 64 k = byteAddr s i (d + k) := by
  simp only [byteAddr, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

theorem lens_ne {τ : T} {i n : Nat} (h : 0 < n) (hn : n ≤ τ.lens.getD i 0) : τ.lens ≠ [] := by
  rintro h'; simp [h'] at hn; omega

/-- Slots live in regions of the same address in both runs. -/
theorem Agree.byteAddr_eq {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {sl : Nat × Nat × Nat}
    (h : sl ∈ τ.slots) {k : Nat} (hk : k < sl.2.1 + sl.2.2) :
    byteAddr s₁ sl.1 k = byteAddr s₂ sl.1 k := by
  have := ha.ok sl h
  simp only [byteAddr, region, ha.wr (lens_ne (n := sl.2.1 + sl.2.2) (by omega) this)]

/-- A load of `w` bytes from a public slot. -/
theorem Agree.load {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp} {w : Nat}
    (hp : slotPub τ m w = true) :
    ∀ k < w, s₁.mem (s₁.ea m + BitVec.ofNat 64 k) = s₂.mem (s₂.ea m + BitVec.ofNat 64 k) := by
  unfold slotPub at hp
  split at hp <;> [skip; cases hp]
  rename_i i d h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨sl, hsl, ⟨rfl, ho⟩, hd⟩ := hp
  intro k hk
  rw [ea_of_addrOf ha.wf₁ h, ea_of_addrOf ha.wf₂ h, byteAddr_add, byteAddr_add]
  exact ha.slots sl hsl _ (by omega) (by omega)

theorem Agree.readW {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp} {w : Nat}
    (hm : memPub τ m = true) (hp : slotPub τ m (w / 8) = true) :
    s₁.mem.readW (s₁.ea m) w = s₂.mem.readW (s₂.ea m) w := by
  have hl := ha.load hp
  rw [ha.ea hm] at hl ⊢
  exact Mem.readW_congr hl

theorem region_len {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) (i : Nat) :
    (region s i).len = τ.lens.getD i 0 := by
  rw [← (hw.1 hne).1]
  simp only [region, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.wr[i]? <;> rfl

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := (hw.1 hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hi' : i < s.wr.length := by rw [← hl, List.length_map] at this; exact this
  exact ⟨hi', by simp [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']⟩

/-- A store of `n` bytes at offset `d` of region `i` does not change byte `k`
of region `j`, if that is another region or outside `[d, d + n)`. -/
theorem write_other {τ : T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k)
    (V : BitVec (8 * n)) :
    s.mem.write (byteAddr s i d) n V (byteAddr s j k) = s.mem (byteAddr s j k) := by
  have hne := lens_ne (n := d + n) (by omega) hd
  obtain ⟨-, hdisj, hbound⟩ := hw.1 hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega)
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact hbound _ (List.getElem_mem _)
  have hbj : (region s j).len ≤ 2 ^ 64 := by rw [hrj]; exact hbound _ (List.getElem_mem _)
  apply Mem.write_apply
  intro hlt
  by_cases hji : j = i
  · -- The same region, at other offsets.
    subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d := by
      simp only [byteAddr]; bv_omega
    rw [h, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega)] at hlt
    rcases hsep with hsep | hsep
    · rw [Nat.mod_eq_of_lt (by omega)] at hlt; omega
    · rw [show 2 ^ 64 - d + k = (k - d) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hlt
      omega
  · -- Another region: the regions are disjoint.
    have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [show (region s i).base + BitVec.ofNat 64 d - (region s i).base = BitVec.ofNat 64 d by
        bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [show (region s j).base + BitVec.ofNat 64 k - (region s j).base = BitVec.ofNat 64 k by
        bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)

@[simp] theorem byteAddr_withMem (s : State) (m : Mem) : byteAddr { s with mem := m } = byteAddr s :=
  rfl

theorem write_same {m₁ m₂ : Mem} {A X : Addr} {n : Nat} (V : BitVec (8 * n)) (h : m₁ X = m₂ X) :
    m₁.write A n V X = m₂.write A n V X := by
  simp only [Mem.write]; split <;> [rfl; exact h]

theorem storeSlots_ok {τ : T} (hok : SlotsOk τ) (m : MemOp) (n : Nat) (p : Bool) :
    SlotsOk { τ with slots := storeSlots τ m n p } := by
  intro sl hsl
  simp only [storeSlots] at hsl
  split at hsl
  · split at hsl
    · split at hsl
      · rcases List.mem_cons.mp hsl with rfl | hsl
        · assumption
        · exact hok sl (List.mem_filter.mp hsl).1
      · exact hok sl (List.mem_filter.mp hsl).1
    · split at hsl <;> [exact hok sl hsl; cases hsl]
  · split at hsl <;> [exact hok sl hsl; cases hsl]

/-- A store of `n` bytes at `m`, of the same value in both runs if `p`. -/
theorem Agree.store {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp}
    (hm : memPub τ m = true) {n : Nat} (hn : 0 < n) {V₁ V₂ : BitVec (8 * n)} {p : Bool}
    (hv : p = true → V₁ = V₂) :
    Agree { τ with slots := storeSlots τ m n p }
      { s₁ with mem := s₁.mem.write (s₁.ea m) n V₁ } { s₂ with mem := s₂.mem.write (s₂.ea m) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁
  wf₂ := ha.wf₂
  ok := storeSlots_ok ha.ok m n p
  lo := ha.lo
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr_withMem]
    have hA := ha.ea hm
    -- Old slots, when the value is the same in both runs.
    have same : sl ∈ τ.slots → p = true →
        s₁.mem.write (s₁.ea m) n V₁ (byteAddr s₁ sl.1 k) =
          s₂.mem.write (s₂.ea m) n V₂ (byteAddr s₂ sl.1 k) := fun h hp => by
      rw [hA, hv hp, ha.byteAddr_eq h hk₂]
      exact write_same _ (ha.byteAddr_eq h hk₂ ▸ ha.slots sl h k hk₁ hk₂)
    simp only [storeSlots] at hsl
    split at hsl
    · rename_i i d had
      have e₁ := ea_of_addrOf ha.wf₁ had
      have e₂ := ea_of_addrOf ha.wf₂ had
      split at hsl
      · rename_i hfit
        have hsl' : sl = (i, d, n) ∨ (sl ∈ τ.slots ∧
            (p = true ∨ sl.1 ≠ i ∨ d + n ≤ sl.2.1 ∨ sl.2.1 + sl.2.2 ≤ d)) := by
          split at hsl
          · rcases List.mem_cons.mp hsl with h | h
            · exact .inl h
            · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq] at h
              exact .inr ⟨h.1, by tauto⟩
          · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq] at hsl
            exact .inr ⟨hsl.1, by tauto⟩
        rcases hsl' with rfl | ⟨h, hsep⟩
        · -- The new slot: the stored bytes.
          have hp : p = true := by split at hsl <;> simp_all
          simp only at hk₁ hk₂
          simp only [e₁, e₂, Mem.write, hv hp]
          have hd : ∀ s : State, byteAddr s i k - byteAddr s i d = BitVec.ofNat 64 (k - d) := by
            intro s; simp only [byteAddr]; bv_omega
          have hlt : (BitVec.ofNat 64 (k - d)).toNat < n := by
            rw [BitVec.toNat_ofNat]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
          rw [hd, hd]; simp only [hlt, ite_true]
        · by_cases hp : p = true
          · exact same h hp
          have hsep : sl.1 ≠ i ∨ k < d ∨ d + n ≤ k := by
            rcases hsep with h' | h' | h' | h'
            · exact absurd h' hp
            · exact .inl h'
            · exact .inr (.inr (by omega))
            · exact .inr (.inl (by omega))
          have hk := ha.ok sl h
          rw [e₁, e₂, write_other ha.wf₁ hn hfit (by omega) hsep,
            write_other ha.wf₂ hn hfit (by omega) hsep]
          exact ha.slots sl h k hk₁ hk₂
      · split at hsl <;> [exact same hsl ‹_›; cases hsl]
    · split at hsl <;> [exact same hsl ‹_›; cases hsl]

/-! ### Instructions that write a register -/

/-- The general-purpose register an instruction writes, if it writes exactly
one (none for stores and SSE instructions, and for `mul`, which writes two). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .movzx8 d _ | .bswap d | .shift _ d _ | .movImm64 d _ => some d
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _ | .vop _
  | .vmovdquLoad .. | .vmovdquStore .. | .vbroadcasti128 .. | .stmxcsr _ | .ldmxcsr _ | .lfence | .mul _ => none

/-- An SSE instruction on registers changes only the SSE registers. -/
theorem XOp.exec_eq (op : XOp) (s : State) : op.exec s = { s with xmm := (op.exec s).xmm } := by
  cases op <;> rfl

/-- An AVX instruction on registers changes only the vector registers. -/
theorem VOp.exec_eq (op : VOp) (s : State) :
    op.exec s = { s with xmm := (op.exec s).xmm, ymmHi := (op.exec s).ymmHi } := by
  cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl

/-- Changing only the SSE registers, which the analysis does not track. -/
theorem Agree.withXmm {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (x₁ x₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁ } { s₂ with xmm := x₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

/-- Whether an instruction may write the general-purpose register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .rax || r == .rdx
  | _ => dstOf i == some r

/-- Changing only the vector registers, which the analysis does not track. -/
theorem Agree.withVec {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (x₁ x₂ y₁ y₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁, ymmHi := y₁ } { s₂ with xmm := x₂, ymmHi := y₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

/-- Changing only MXCSR, which the analysis does not track. -/
theorem Agree.withMxcsr {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (m₁ m₂ : BitVec 32) :
    Agree τ { s₁ with mxcsr := m₁ } { s₂ with mxcsr := m₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

theorem exec_nonstore {i : Instr} {d : Reg} (hd : dstOf i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i <;> simp only [dstOf, Option.some.injEq, reduceCtorEq] at hd <;> subst hd
  case mov src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case mov32 src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case alu op src =>
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  case alu32 op src =>
    simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  case shift32 op _ n =>
    simp only [exec, execShift32] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case bswap32 =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case movzx8 m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case bswap =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case movImm64 v =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩

theorem aluBases_narrow (τ : T) (op : AluOp) (d : Reg) (src : Src) :
    aluBases τ op d src false = kill τ d := by
  unfold aluBases; split <;> simp

theorem aluBases_ok {τ : T} {s s' : State} (hw : Wf τ s) {op : AluOp} {d : Reg} {src : Src}
    (e : exec (.alu op d src) s = some s') :
    ∀ p ∈ aluBases τ op d src true, s'.gpr p.1 = (region s' p.2.1).base + BitVec.ofNat 64 p.2.2 := by
  obtain ⟨-, hwr, -, hg⟩ := exec_nonstore (d := d) rfl e
  unfold aluBases
  split
  · rename_i v
    split
    · rename_i hv
      simp only [Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      have hd : s'.gpr d = s.gpr d + BitVec.ofNat 64 v.toNat := by
        simp only [exec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
        subst e
        simp only [arithFlags, State.setFlags, State.setReg, ite_true]
        congr 1
        rw [BitVec.signExtend_eq_setWidth_of_msb_false hv]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      intro p hp
      simp only [List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
      rcases hp with hp | ⟨q, ⟨hq, hqd⟩, rfl⟩
      · exact kill_bases hw hwr hg p hp
      · simp only
        rw [hd, ← hqd, hw.2 q hq, BitVec.add_assoc, ← BitVec.ofNat_add]
        simp [region, hwr]
    · exact kill_bases hw hwr hg
  · exact kill_bases hw hwr hg

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dstOf i = some d) {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) (hlo : τ'.lo = .empty) : Agree τ' s₁' s₂' := by
  obtain ⟨-, hw₁, hm₁, hg₁⟩ := exec_nonstore hd e₁
  obtain ⟨-, hw₂, hm₂, hg₂⟩ := exec_nonstore hd e₂
  exact ha.keep hrf hl hs hw₁ hw₂ hm₁ hm₂ (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h))
    (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h)) (hlo ▸ noLo)

theorem execMul_gpr (r : Reg) (s : State) {q : Reg} (h₁ : q ≠ .rax) (h₂ : q ≠ .rdx) :
    (execMul r s).gpr q = s.gpr q := by
  simp [execMul, State.setReg, State.setFlags, h₁, h₂]

theorem mul_bases {τ : T} {s : State} (hw : Wf τ s) (r : Reg) :
    ∀ p ∈ (kill τ .rax).filter (·.1 != .rdx),
      (execMul r s).gpr p.1 = (region (execMul r s) p.2).base := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [execMul_gpr r s hp.1.2 hp.2, hw.2 p hp.1.1]; rfl

theorem Agree.mul {τ : T} {r : Reg} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) :
    Agree (mulStep τ r) (execMul r s₁) (execMul r s₂) := by
  refine ha.keep ⟨fun q hq => ?_, fun hp => ?_⟩ rfl rfl rfl rfl rfl rfl (mul_bases ha.wf₁ r)
    (mul_bases ha.wf₂ r)
  · simp only [mulStep] at hq
    by_cases hp : (pub τ .rax && pub τ r) = true
    · have hp' := hp
      simp only [Bool.and_eq_true] at hp'
      have e₁ := ha.reg hp'.1
      have e₂ := ha.reg hp'.2
      simp only [hp, ite_true, RegSet.mem_insert] at hq
      by_cases h₁ : q = .rax
      · subst h₁; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      by_cases h₂ : q = .rdx
      · subst h₂; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      simp only [h₁, h₂, false_or] at hq
      rw [execMul_gpr r s₁ h₁ h₂, execMul_gpr r s₂ h₁ h₂]; exact ha.rf.1 q hq
    · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hq
      rw [execMul_gpr r s₁ hq.2.1 hq.1, execMul_gpr r s₂ hq.2.1 hq.1]; exact ha.rf.1 q hq.2.2
  · simp only [mulStep, Bool.and_eq_true] at hp
    simp [execMul, State.setReg, State.setFlags, ha.reg hp.1, ha.reg hp.2]

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    refine ⟨ha.srcAddrs hok, ha.keep ⟨regs_set ha.rf.1 fun hp => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
      (movBases_ok ha.wf₁ hv₁) (movBases_ok ha.wf₂ hv₂) noLo⟩
    rcases Bool.or_eq_true_iff.mp hp with hp | hp
    · rw [ha.readSrc hp, hv₂] at hv₁; cases hv₁; rfl
    · cases src with
      | mem m =>
        simp only [readSrc, State.load64] at hv₁ hv₂
        split at hv₁ <;> [skip; cases hv₁]
        split at hv₂ <;> [skip; cases hv₂]
        cases hv₁; cases hv₂
        exact ha.readW (w := 64) hok hp
      | _ => simp [loadPub] at hp
  | mov32 d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    refine ⟨ha.srcAddrs hok, ha.write rfl e₁ e₂ ⟨?_, ?_⟩ rfl rfl (fun _ h => h) rfl⟩
    · simp only [exec, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
      refine regs_set ha.rf.1 fun hp => ?_
      rcases Bool.or_eq_true_iff.mp hp with hp | hp
      swap
      · cases src with
        | reg r =>
          simp only [readSrc32, Option.some.injEq] at hv₁ hv₂
          subst hv₁ hv₂
          rw [ha.lo r hp]
        | _ => simp [loPub] at hp
      rcases Bool.or_eq_true_iff.mp hp with hp | hp
      · rw [ha.readSrc32 hp, hv₂] at hv₁; cases hv₁; rfl
      · cases src with
        | mem m =>
          simp only [readSrc32, State.load32] at hv₁ hv₂
          split at hv₁ <;> [skip; cases hv₁]
          split at hv₂ <;> [skip; cases hv₂]
          cases hv₁; cases hv₂
          rw [ha.readW (w := 32) hok hp]
        | _ => simp [loadPub] at hp
    · simp only [exec, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
      exact ha.rf.2
  | store m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store64] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 8) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  | store32 m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 4) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  | store8 m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 1) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  | movdquLoad d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨by simp [addrs, ha.ea hok], ha.withXmm _ _⟩
  | movdquStore m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store128] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩
  | xop op =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    rw [XOp.exec_eq op s₁, XOp.exec_eq op s₂]
    exact ⟨rfl, ha.withXmm _ _⟩
  | vop op =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    rw [VOp.exec_eq op s₁, VOp.exec_eq op s₂]
    exact ⟨rfl, ha.withVec _ _ _ _⟩
  | vmovdquLoad len d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases len <;> simp only [exec, Option.map_eq_some_iff] at e₁ e₂ <;>
      obtain ⟨v₁, -, rfl⟩ := e₁ <;> obtain ⟨v₂, -, rfl⟩ := e₂ <;>
      exact ⟨by simp [addrs, ha.ea hok], ha.withVec _ _ _ _⟩
  | vbroadcasti128 d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨by simp [addrs, ha.ea hok], ha.withVec _ _ _ _⟩
  | vmovdquStore len m r =>
    cases len
    · simp only [step, storeStep] at hs
      split at hs <;> [skip; cases hs]
      rename_i hok; cases hs
      simp only [exec, State.store128] at e₁ e₂
      split at e₁ <;> [cases e₁; cases e₁]
      split at e₂ <;> [cases e₂; cases e₂]
      exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩
    · simp only [step, storeStep] at hs
      split at hs <;> [skip; cases hs]
      rename_i hok; cases hs
      simp only [exec, State.store256] at e₁ e₂
      split at e₁ <;> [cases e₁; cases e₁]
      split at e₂ <;> [cases e₂; cases e₂]
      exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 32) hok (by decide) fun hp => by cases hp⟩
  | stmxcsr m =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 4) hok (by decide) fun hp => by cases hp⟩
  | ldmxcsr m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, e₁⟩ := e₁; obtain ⟨v₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.withMxcsr _ _⟩
  | lfence =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨rfl, ha⟩
  | alu op d src =>
    simp only [step, aluStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    obtain ⟨-, hw₁, hm₁, -⟩ := exec_nonstore (d := d) rfl e₁
    obtain ⟨-, hw₂, hm₂, -⟩ := exec_nonstore (d := d) rfl e₂
    refine ⟨ha.srcAddrs hok, ha.keep ?_ rfl rfl hw₁ hw₂ hm₁ hm₂ (aluBases_ok ha.wf₁ e₁) (aluBases_ok ha.wf₂ e₂)
      noLo⟩
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
    exact alu_sound ha (fun s => s.gpr d) (fun s x => s.setReg d x) id
      (setReg_gpr_eq · d) (by simp [State.setReg]) (by simp)
      (fun hp => by rw [ha.readSrc hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂
  | alu32 op d src =>
    simp only [step, aluStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    refine ⟨ha.srcAddrs hok, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => by rwa [aluBases_narrow] at h) rfl⟩
    simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
    exact alu_sound ha (fun s => (s.gpr d).setWidth 32) (fun s x => s.setReg32 d x)
      (fun h => by simp only [h]) (fun s x => setReg_gpr_eq s d _) (by simp [State.setReg32, State.setReg])
      (by simp [State.setReg32])
      (fun hp => by rw [ha.readSrc32 hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂
  | shift32 op d n =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    by_cases hn : 1 ≤ n ∧ n ≤ 31
    swap; · simp [exec, execShift32, hn] at e₁
    simp only [exec, execShift32, hn, and_self, ite_true] at e₁ e₂
    refine ⟨fun r hr => ?_, fun hf => ?_⟩
    · by_cases hrd : r = d
      · subst hrd
        have := ha.rf.1 r hr
        cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg32, State.setReg, this]
      · cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg32, State.setReg, State.setFlags, hrd, ha.rf.1 r hr]
    · simp only [Bool.and_eq_true] at hf
      have hd := ha.reg hf.2
      have hfl := ha.rf.2 hf.1
      cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg32, State.setFlags, hd, hfl]
  | bswap32 d =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨fun r hr => ?_, fun hf => by simpa [State.setReg32] using ha.rf.2 hf⟩
    by_cases hrd : r = d
    · subst hrd; simp [State.setReg32, State.setReg, ha.rf.1 r hr]
    · simp [State.setReg32, State.setReg, hrd, ha.rf.1 r hr]
  | movzx8 d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    refine ⟨by simp [addrs, ha.ea hok], ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨regs_set (p := false) ha.rf.1 (fun h => by cases h), ha.rf.2⟩
  | bswap d =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨fun r hr => ?_, fun hf => by simpa using ha.rf.2 hf⟩
    by_cases hrd : r = d
    · subst hrd; simp [State.setReg, ha.rf.1 r hr]
    · simp [State.setReg, hrd, ha.rf.1 r hr]
  | shift op d n =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    by_cases hn : 1 ≤ n ∧ n ≤ 63
    swap; · simp [exec, execShift, hn] at e₁
    simp only [exec, execShift, hn, and_self, ite_true] at e₁ e₂
    refine ⟨fun r hr => ?_, fun hf => ?_⟩
    · by_cases hrd : r = d
      · subst hrd
        have := ha.rf.1 r hr
        cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg, this]
      · cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg, State.setFlags, hrd, ha.rf.1 r hr]
    · simp only [Bool.and_eq_true] at hf
      have hd := ha.reg hf.2
      have hfl := ha.rf.2 hf.1
      cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg, State.setFlags, hd, hfl]
  | movImm64 d v =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨regs_set (p := true) ha.rf.1 fun _ => rfl, by simpa using ha.rf.2⟩
  | mul r =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨rfl, ha.mul⟩

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hcf, hzf]

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (List.mem_filter.mp hp).1⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.1 (he ▸ hne)
  · simp [meet, he] at hne

theorem Wf.meet_right {τ₁ τ₂ : T} {s : State} (h : Wf τ₂ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (by simpa using (List.mem_filter.mp hp).2)⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact h.1 hne
  · simp [meet, he] at hne

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).1,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.1)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [exact h.wr hne; exact absurd rfl hne]
  wf₁ := h.wf₁.meet_left
  wf₂ := h.wf₂.meet_left
  lo r hr := h.lo r (RegSet.mem_inter.mp hr).1
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact he ▸ h.ok sl (List.mem_filter.mp hsl).1
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (List.mem_filter.mp hsl).1; cases hsl]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).2,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.2)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [rename_i he; exact absurd rfl hne]
    exact h.wr (he ▸ hne)
  wf₁ := h.wf₁.meet_right
  wf₂ := h.wf₂.meet_right
  lo r hr := h.lo r (RegSet.mem_inter.mp hr).2
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact h.ok sl (by simpa using (List.mem_filter.mp hsl).2)
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (by simpa using (List.mem_filter.mp hsl).2); cases hsl]

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hlo⟩ := hle
  refine ⟨⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hr h'), fun hf' => h.rf.2 ?_⟩, fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.1 (hl ▸ hne), fun p hp => h.wf₁.2 p (hb p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.1 (hl ▸ hne), fun p hp => h.wf₂.2 p (hb p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl),
    fun r hr' => h.lo r (RegSet.mem_of_subset hlo hr')⟩
  rcases hf with hf | hf
  · simp [hf'] at hf
  · exact hf

end VG.X86_64.Taint

namespace VG.X86_64

namespace Taint

/-- A call stores its return address, which may differ between the runs, at
`rsp - 8`, which is not known to be outside the writable regions: `rsp` must
be public, and every slot is forgotten. -/
def callStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, slots := [], lo := .empty } else none

/-- A return loads its return address from `[rsp]` and moves `rsp`. -/
def retStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, lo := .empty } else none

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : callStep τ = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [callStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have hsp := ha.reg hp
  refine ⟨by simp [hsp], ⟨⟨fun r hr => ?_, ha.rf.2⟩, ha.wr, ⟨ha.wf₁.1, ?_⟩, ⟨ha.wf₂.1, ?_⟩, ?_, ?_, noLo⟩⟩
  · by_cases h : r = .rsp
    · subst h; simp [State.setReg, hsp]
    · simp only [State.setReg, h, ite_false]; exact ha.rf.1 r hr
  · exact kill_bases (s' := s₁.setReg .rsp (s₁.gpr .rsp - 8)) ha.wf₁ rfl fun _ h => setReg_ne h
  · exact kill_bases (s' := s₂.setReg .rsp (s₂.gpr .rsp - 8)) ha.wf₂ rfl fun _ h => setReg_ne h
  · intro sl h; simp at h
  · intro sl h; simp at h

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : retStep τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  simp only [retStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have hsp := ha.reg hp
  refine ⟨by simp [hsp], ha.keep ⟨fun r hr => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
    (kill_setReg ha.wf₁ _ _) (kill_setReg ha.wf₂ _ _) noLo⟩
  by_cases h : r = .rsp
  · subst h; simp [State.setReg, hsp]
  · simp only [State.setReg, h, ite_false]; exact ha.rf.1 r hr

end Taint

/-- Taint tracking for x86-64. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.le
  le_sound := Taint.le_sound
  call := Taint.callStep
  call_sound := Taint.call_sound
  ret := Taint.retStep
  ret_sound := Taint.ret_sound
  -- Frames are not analysed yet.
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := { regs := RegSet.ofList rs, flags := false }

theorem Taint.agree_ofRegs {rs : List Reg} {s₁ s₂ : State}
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Taint.Agree (Taint.ofRegs rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo := noLo

end VG.X86_64
