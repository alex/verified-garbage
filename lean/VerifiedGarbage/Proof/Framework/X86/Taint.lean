import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.KernelList
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.TCB.X86.Target

/-!
# Taint tracking for x86 (32-bit)

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public, whether the
flags are public, and what is known about memory. Memory is secret unless
known otherwise: an address must be computed from public registers, and a
value loaded from memory is secret unless it comes from a *public slot* or
from the read-only stack arguments.

As on x86-64 (`VG.X86_64.Taint`), public slots let public values survive a
round trip through memory. They are byte ranges of the writable regions
`s.wr` (identified by index) that hold the same bytes in both runs. To keep
them sound in the presence of stores of secrets, the analysis knows lower
bounds on the lengths of the writable regions (`lens`, whose regions are then
pairwise disjoint, the same in both runs, and within the 32-bit address space;
a bound of `0` means the length is unknown and the region has no slots) and
which registers point at a known offset before the base address of which
region (`bases`). A store through such a register can only change bytes of
its own region at the store's offset; any other store of a secret forgets
every slot.

With only seven usable registers, pointers also round-trip through memory:
`wbases` records which words of the writable regions hold the base address
of which region, so that a register loaded from one is known to point there.
Any store at an unknown address forgets them.

The first `argLen` bytes at the stack pointer on entry (the return address,
then the arguments of code that may only read them) are outside every
writable region, so no store changes them, and at the same address in both
runs; those from the fifth on (the arguments) are public, and `argBases`
records which of their words are the base address of a writable region. No
instruction may write `esp`.

## Calls and frames

Only calls and returns and the pushes and pops of frames move `esp`. The
analysis knows the stack between `esp` and the stack pointer on entry
exactly (`stk`): from `esp` up, the frames (each a writable region: the
innermost the first of `s.wr`, and so on) and the return addresses of the
calls under way. So it knows where the arguments are (above all of it) and
the base address of every frame (relative to `esp`, in `bases`), and code
may keep public values and pointers in a frame, as in any writable region:
a frame's push makes each register it stores that is public a public slot,
and each that holds the base address of a region a base-address word. That
is how a caller passes the arguments of a call, which the callee reads from
`[esp + 4]` on as its own.

To keep the other writable regions apart from the frames and from the return
addresses, the analysis knows that the `room` bytes below the stack pointer
on entry lie outside every writable region but the frames (the stack a
contract's `stack` reserves), and that calls and frames stay within them.
The register a frame's pop loads is secret.
-/

namespace VG.X86.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order (`0` if
  unknown); `[]` if nothing is known about the regions. -/
  lens : List Nat := []
  /-- `(r, i, k)`: `r + k` is the base address of writable region `i`. -/
  bases : List (Reg × Nat × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  /-- `(j, o, i)`: the word at offset `o` of writable region `j` is the base address
  of writable region `i`. -/
  wbases : List (Nat × Nat × Nat) := []
  /-- The first `argLen` bytes at `esp` are never written, and those from `esp + 4` on are public. -/
  argLen : Nat := 0
  /-- `(o, i)`: the word at `o` bytes above the stack pointer on entry is the base address
  of writable region `i`. -/
  argBases : List (Nat × Nat) := []
  /-- The stack between `esp` and the stack pointer on entry, from `esp` up: a frame of
  `n` bytes (`some n`), which is one of the writable regions, or a return address (`none`). -/
  stk : List (Option Nat) := []
  /-- The `room` bytes below the stack pointer on entry lie outside every writable region
  but the frames of `stk`. -/
  room : Nat := 0
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The address of byte `k` above `esp`. -/
def argByte (s : State) (k : Nat) : Addr := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k

/-- The size of an item of the stack: a frame of `n` bytes, or a return address. -/
def itemSize : Option Nat → Nat
  | some n => n
  | none => 4

/-- The size of the stack `stk`: how far `esp` is below the stack pointer on entry. -/
def depth : List (Option Nat) → Nat
  | [] => 0
  | x :: xs => itemSize x + depth xs

/-- The frames of the stack `xs`, the first at offset `o` above `esp` and the
writable region `j`: each frame's region, offset and size. -/
def frameList : List (Option Nat) → Nat → Nat → List (Nat × Nat × Nat)
  | [], _, _ => []
  | some n :: xs, j, o => (j, o, n) :: frameList xs (j + 1) (o + n)
  | none :: xs, j, o => frameList xs j (o + 4)

/-- The number of frames of the stack. -/
def nframes : List (Option Nat) → Nat
  | [] => 0
  | some _ :: xs => nframes xs + 1
  | none :: xs => nframes xs

/-- The registers `regs` and, if `flags`, the flags are the same in both states. -/
def AgreeRF (regs : RegSet Reg) (flags : Bool) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ regs, s₁.gpr r = s₂.gpr r) ∧
  (flags = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)

/-- What `τ` says about each state on its own. -/
structure Wf (τ : T) (s : State) : Prop where
  lens : τ.lens ≠ [] →
    List.Forall₂ (fun r l => l ≤ r.len) s.wr τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  bases : ∀ p ∈ τ.bases, addr (s.gpr p.1) p.2.2 = (region s p.2.1).base
  wbases : ∀ p ∈ τ.wbases, p.2.1 + 4 ≤ τ.lens.getD p.1 0 ∧
    addr (s.mem.readW (byteAddr s p.1 p.2.1) 32) 0 = (region s p.2.2).base
  args : 0 < τ.argLen →
    (s.gpr .esp).toNat + depth τ.stk + τ.argLen ≤ 2 ^ 32 ∧
      ∀ r ∈ s.wr, Region.Disjoint ⟨argByte s (depth τ.stk), τ.argLen⟩ r
  argBases : ∀ p ∈ τ.argBases, p.1 + 4 ≤ τ.argLen ∧
    addr (s.mem.readW (addr (s.gpr .esp) (depth τ.stk + p.1)) 32) 0 = (region s p.2).base
  stk : (s.gpr .esp).toNat + depth τ.stk < 2 ^ 32
  frames : ∀ p ∈ frameList τ.stk 0 0, s.wr[p.1]? = some ⟨addr (s.gpr .esp) p.2.1, p.2.2⟩
  room : 0 < τ.room → τ.room ≤ (s.gpr .esp).toNat + depth τ.stk ∧
    ∀ r ∈ s.wr.drop (nframes τ.stk),
      Region.Disjoint ⟨argByte s (depth τ.stk) - BitVec.ofNat 64 τ.room, τ.room⟩ r

/-- What `Wf` says about a state on entry (with an empty stack), with the
arguments at `esp`. -/
structure WfEntry (τ : T) (s : State) : Prop where
  lens : τ.lens ≠ [] →
    List.Forall₂ (fun r l => l ≤ r.len) s.wr τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  bases : ∀ p ∈ τ.bases, addr (s.gpr p.1) p.2.2 = (region s p.2.1).base
  wbases : ∀ p ∈ τ.wbases, p.2.1 + 4 ≤ τ.lens.getD p.1 0 ∧
    addr (s.mem.readW (byteAddr s p.1 p.2.1) 32) 0 = (region s p.2.2).base
  args : 0 < τ.argLen →
    (s.gpr .esp).toNat + τ.argLen ≤ 2 ^ 32 ∧
      ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, τ.argLen⟩ r
  argBases : ∀ p ∈ τ.argBases, p.1 + 4 ≤ τ.argLen ∧
    addr (s.mem.readW (addr (s.gpr .esp) p.1) 32) 0 = (region s p.2).base

/-- The abstract state on entry: no calls or frames yet, and `room` bytes
below `esp` (those the contract reserves for the stack, `Sig.contract`'s
`stack`) outside every writable region. -/
theorem Wf.entryRoom {τ : T} {s : State} (hstk : τ.stk = []) (h : WfEntry τ s)
    (hroom : 0 < τ.room → τ.room ≤ (s.gpr .esp).toNat ∧
      ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ.room, τ.room⟩ r) :
    Wf τ s where
  lens := h.lens
  bases := h.bases
  wbases := h.wbases
  args hpos := by
    rw [hstk, depth, argByte, BitVec.add_zero, Nat.add_zero]
    exact h.args hpos
  argBases p hp := by rw [hstk, depth, Nat.zero_add]; exact h.argBases p hp
  stk := by rw [hstk, depth, Nat.add_zero]; exact (s.gpr .esp).isLt
  frames p hp := by rw [hstk] at hp; cases hp
  room hpos := by
    rw [hstk, depth, nframes, Nat.add_zero, List.drop_zero, argByte, BitVec.add_zero]
    exact hroom hpos

theorem Wf.entry {τ : T} {s : State} (hstk : τ.stk = []) (hroom : τ.room = 0) (h : WfEntry τ s) :
    Wf τ s :=
  Wf.entryRoom hstk h fun h => by omega

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
  sp : 0 < τ.argLen → s₁.gpr .esp = s₂.gpr .esp
  argMem : ∀ k, 4 ≤ k → k < τ.argLen →
    s₁.mem (argByte s₁ (depth τ.stk + k)) = s₂.mem (argByte s₂ (depth τ.stk + k))

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat × Nat) := τ.bases.filter (·.1 != d)

/-- The address `m` accesses is public. -/
def memPub (τ : T) (m : MemOp) : Bool := pub τ m.base

/-- The region and offset addressed by `m`, if known. -/
def addrOf (τ : T) (m : MemOp) : Option (Nat × Nat) :=
  (τ.bases.find? fun p => p.1 == m.base && p.2.2 ≤ m.disp).map fun p => (p.2.1, m.disp - p.2.2)

/-- `w` bytes at `m` are within a public slot. -/
def slotPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  match addrOf τ m with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

/-- `w` bytes at `m` are within the stack arguments. -/
def argPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  m.base == .esp && depth τ.stk + 4 ≤ m.disp && m.disp + w ≤ depth τ.stk + τ.argLen

/-- The addresses the operand accesses are public. -/
def srcOk (τ : T) : Src → Bool
  | .mem m => memPub τ m
  | _ => true

/-- The operand's value is public (memory operands aside). -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pub τ r
  | .imm _ => true
  | .mem _ => false

/-- A word memory operand is public. -/
def loadPub (τ : T) : Src → Bool
  | .mem m => slotPub τ m 4 || argPub τ m 4
  | _ => false

/-- The regions whose base address a word loaded from `m` is. -/
def loadBases (τ : T) (m : MemOp) : List Nat :=
  (match addrOf τ m with
    | some (j, o) => (τ.wbases.filter fun p => p.1 == j && p.2.1 == o).map (·.2.2)
    | none => []) ++
  (if m.base == .esp then (τ.argBases.filter (depth τ.stk + ·.1 == m.disp)).map (·.2) else [])

/-- The known region bases after `mov d, src`. -/
def movBases (τ : T) (d : Reg) : Src → List (Reg × Nat × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | .mem m => kill τ d ++ (loadBases τ m).map fun i => (d, i, 0)
  | .imm _ => kill τ d

/-- The regions whose base address register `r` holds. -/
def regBases (τ : T) (r : Reg) : List Nat :=
  (τ.bases.filter fun p => p.1 == r && p.2.2 == 0).map (·.2.1)

/-- The public slots after storing `w` bytes at `m`, a public value iff `p`. -/
def storeSlots (τ : T) (m : MemOp) (w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ m with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

/-- The known base-address words after storing `w` bytes at `m`, the base
address of each region in `nb`. -/
def storeWbases (τ : T) (m : MemOp) (w : Nat) (nb : List Nat) : List (Nat × Nat × Nat) :=
  match addrOf τ m with
  | some (j, d) =>
    if d + w ≤ τ.lens.getD j 0 then
      (τ.wbases.filter fun p => p.1 != j || d + w ≤ p.2.1 || p.2.1 + 4 ≤ d) ++ nb.map fun i => (j, d, i)
    else []
  | none => []

def storeStep (τ : T) (m : MemOp) (w : Nat) (p : Bool) (nb : List Nat) : Option T :=
  if memPub τ m then some { τ with slots := storeSlots τ m w p, wbases := storeWbases τ m w nb }
  else none

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- `mul r`: `eax`, `edx` and the flags are functions of the old `eax` and
`r` (SF and ZF become undefined in both runs). -/
def mulStep (τ : T) (r : Reg) : T :=
  let p := pub τ .eax && pub τ r
  { τ with regs := if p then (τ.regs.insert .eax).insert .edx else (τ.regs.erase .eax).erase .edx,
           flags := p, bases := (kill τ .eax).filter (·.1 != .edx) }

def step (τ : T) : Instr → Option T
  | .mov d src =>
    if d != .esp && srcOk τ src then
      some { τ with regs := set τ d (srcPub τ src || loadPub τ src), bases := movBases τ d src }
    else none
  | .store m r => storeStep τ m 4 (pub τ r) (regBases τ r)
  | .alu op d src =>
    if d != .esp && srcOk τ src then
      let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
      some { τ with regs := if writes op then set τ d p else τ.regs, flags := p, bases := kill τ d }
    else none
  -- The result is a function of the old value of `d`, and so are the
  -- flags that change.
  | .shift _ d _ =>
    if d != .esp then some { τ with flags := τ.flags && pub τ d, bases := kill τ d } else none
  | .bswap d => if d != .esp then some { τ with bases := kill τ d } else none
  | .movzx8 d m =>
    if d != .esp && memPub τ m then some { τ with regs := set τ d false, bases := kill τ d } else none
  | .store8 m r => storeStep τ m 1 (pub τ r.reg) []
  | .mul r => some (mulStep τ r)
  -- Frames are not analysed yet.
  | .push _ | .pop .. | .movdquLoad .. | .movdquStore .. | .xop _ => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  wbases := if τ₁.lens = τ₂.lens then τ₁.wbases.filter (τ₂.wbases.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen ∧ τ₁.stk = τ₂.stk then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen ∧ τ₁.stk = τ₂.stk then
    τ₁.argBases.filter (τ₂.argBases.contains ·) else []
  stk := if τ₁.stk = τ₂.stk then τ₁.stk else []
  room := if τ₁.stk = τ₂.stk then min τ₁.room τ₂.room else 0

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) &&
    τ.wbases.all (σ.wbases.contains ·) && τ.argLen == σ.argLen &&
    τ.argBases.all (σ.argBases.contains ·) && τ.stk == σ.stk && decide (τ.room ≤ σ.room)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := Iff.rfl

section
variable {τ : T} {s₁ s₂ : State}

theorem Agree.reg (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) : s₁.gpr r = s₂.gpr r :=
  h.rf.1 r (pub_iff.mp hr)

theorem Agree.ea (h : Agree τ s₁ s₂) {m : MemOp} (hm : memPub τ m = true) : s₁.ea m = s₂.ea m := by
  simp only [State.ea, h.reg hm]

theorem Agree.srcAddrs (h : Agree τ s₁ s₂) {src : Src} (hs : srcOk τ src = true) :
    X86.srcAddrs s₁ src = X86.srcAddrs s₂ src := by
  cases src <;> simp only [X86.srcAddrs]
  simp only [srcOk] at hs
  rw [h.ea hs]

end

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 32} (hv : p = true → v₁ = v₂) :
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

theorem setReg_ne {s : State} {d r : Reg} {v : BitVec 32} (h : r ≠ d) : (s.setReg d v).gpr r = s.gpr r := by
  simp [State.setReg, h]

/-! ### Region addresses -/

theorem addrOf_some {τ : T} {m : MemOp} {i d : Nat} (h : addrOf τ m = some (i, d)) :
    ∃ k, (m.base, i, k) ∈ τ.bases ∧ k ≤ m.disp ∧ d = m.disp - k := by
  unfold addrOf at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hq
  have hb := List.find?_some hq
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  exact ⟨q.2.2, by rw [← hb.1]; exact hm, hb.2, rfl⟩

theorem lens_ne {τ : T} {i n : Nat} (h : 0 < n) (hn : n ≤ τ.lens.getD i 0) : τ.lens ≠ [] := by
  rintro h'; simp [h'] at hn; omega

theorem forall₂_length {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) : rs.length = ls.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall₂_getD {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) (i : Nat) : ls.getD i 0 ≤ (rs.getD i ⟨0, 0⟩).len := by
  induction h generalizing i with
  | nil => simp
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem region_len {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) (i : Nat) :
    τ.lens.getD i 0 ≤ (region s i).len :=
  forall₂_getD (hw.lens hne).1 i

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := (hw.lens hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hi' : i < s.wr.length := by rw [← forall₂_length hl] at this; exact this
  exact ⟨hi', by simp [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']⟩

/-- Region `i` lies within the 32-bit address space. -/
theorem region_bound {τ : T} {s : State} (hw : Wf τ s) {i : Nat} (hi : 0 < τ.lens.getD i 0) :
    (region s i).base.toNat + τ.lens.getD i 0 ≤ 2 ^ 32 := by
  have hne := lens_ne hi (Nat.le_refl _)
  obtain ⟨hi', hr⟩ := region_mem hw hne hi
  have := region_len hw hne i
  rw [hr] at this ⊢
  have := (hw.lens hne).2.2 _ (List.getElem_mem hi')
  omega

/-- `[x + d]`, for `x + k` the base address `b` of a region containing byte `d - k`. -/
theorem addr_offset {x : BitVec 32} {k d : Nat} {b : Addr} (e : addr x k = b) (hk : k ≤ d)
    (hb : b.toNat + (d - k) < 2 ^ 32) : addr x d = b + BitVec.ofNat 64 (d - k) := by
  have e' := congrArg BitVec.toNat e
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at e'
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem ea_of_addrOf {τ : T} {s : State} (hw : Wf τ s) {m : MemOp} {i d : Nat}
    (h : addrOf τ m = some (i, d)) (hd : d < τ.lens.getD i 0) :
    s.ea m = byteAddr s i d := by
  obtain ⟨k, hb, hk, rfl⟩ := addrOf_some h
  have hbd := region_bound hw (i := i) (by omega)
  have e := hw.bases _ hb
  exact addr_offset e hk (by omega)

theorem byteAddr_add (s : State) (i d k : Nat) :
    byteAddr s i d + BitVec.ofNat 64 k = byteAddr s i (d + k) := by
  simp only [byteAddr, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

/-- Slots live in regions of the same address in both runs. -/
theorem Agree.byteAddr_eq {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {j : Nat} {n : Nat}
    (hn : 0 < n) (hj : n ≤ τ.lens.getD j 0) (k : Nat) :
    byteAddr s₁ j k = byteAddr s₂ j k := by
  simp only [byteAddr, region, ha.wr (lens_ne hn hj)]

/-- A load of a word from a public slot. -/
theorem Agree.readW {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp}
    (hp : slotPub τ m 4 = true) : s₁.mem.readW (s₁.ea m) 32 = s₂.mem.readW (s₂.ea m) 32 := by
  unfold slotPub at hp
  split at hp <;> [skip; cases hp]
  rename_i i d h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨sl, hsl, ⟨rfl, ho⟩, hd⟩ := hp
  have hok := ha.ok sl hsl
  rw [ea_of_addrOf ha.wf₁ h (by omega), ea_of_addrOf ha.wf₂ h (by omega),
    ha.byteAddr_eq (n := sl.2.1 + sl.2.2) (by omega) hok d]
  refine Mem.readW_congr fun k hk => ?_
  rw [byteAddr_add]
  have := ha.slots sl hsl (d + k) (by omega) (by omega)
  rwa [ha.byteAddr_eq (n := sl.2.1 + sl.2.2) (by omega) hok (d + k)] at this

/-- The word `o` bytes above the stack pointer on entry, byte by byte. -/
theorem argWord {τ : T} {s : State} (hw : Wf τ s) {o : Nat} (ho : o + 4 ≤ τ.argLen) (k : Nat) :
    addr (s.gpr .esp) (depth τ.stk + o) + BitVec.ofNat 64 k = argByte s (depth τ.stk + o + k) := by
  have := (hw.args (by omega)).1
  rw [addr_eq (by omega), argByte, BitVec.ofNat_add (depth τ.stk + o) k, BitVec.add_assoc]

/-- A load of a word from the stack arguments. -/
theorem Agree.readArg {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp}
    (hp : argPub τ m 4 = true) : s₁.mem.readW (s₁.ea m) 32 = s₂.mem.readW (s₂.ea m) 32 := by
  simp only [argPub, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨hb, h4⟩, ho⟩ := hp
  have hsp := ha.sp (by omega)
  show s₁.mem.readW (addr (s₁.gpr m.base) m.disp) 32 = s₂.mem.readW (addr (s₂.gpr m.base) m.disp) 32
  obtain ⟨b, d⟩ := m
  obtain ⟨o, rfl⟩ : ∃ o, d = depth τ.stk + o := ⟨d - depth τ.stk, by simp only at h4; omega⟩
  simp only at hb ho h4 ⊢
  rw [hb, hsp]
  refine Mem.readW_congr fun k hk => ?_
  have := ha.argMem (o + k) (by omega) (by omega)
  rw [← Nat.add_assoc] at this
  rwa [← argWord ha.wf₁ (o := o) (by omega), ← argWord ha.wf₂ (o := o) (by omega), hsp] at this

/-! ### Keeping what is known about memory -/

theorem Wf.keep {τ τ' : T} {s s' : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) (hsp : s'.gpr .esp = s.gpr .esp)
    (hb : ∀ p ∈ τ'.bases, addr (s'.gpr p.1) p.2.2 = (region s' p.2.1).base)
    (hstk : τ'.stk = τ.stk := by rfl) (hroom : τ'.room = τ.room := by rfl) : Wf τ' s' where
  lens h := by rw [hwr, hl]; exact hw.lens (hl ▸ h)
  bases := hb
  wbases p h := by
    rw [hl]
    simp only [byteAddr, region, hwr, hm]
    exact hw.wbases p (hwb ▸ h)
  args h := by simp only [argByte, hwr, hsp, hargs, hstk]; exact hw.args (hargs ▸ h)
  argBases p h := by
    rw [hargs, hsp, hm, hstk]
    simp only [region, hwr]
    exact hw.argBases p (hab ▸ h)
  stk := by rw [hsp, hstk]; exact hw.stk
  frames p h := by rw [hwr, hsp]; exact hw.frames p (hstk ▸ h)
  room h := by simp only [argByte, hwr, hsp, hstk, hroom]; exact hw.room (hroom ▸ h)

theorem Agree.keep {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem)
    (hsp₁ : s₁'.gpr .esp = s₁.gpr .esp) (hsp₂ : s₂'.gpr .esp = s₂.gpr .esp)
    (hb₁ : ∀ p ∈ τ'.bases, addr (s₁'.gpr p.1) p.2.2 = (region s₁' p.2.1).base)
    (hb₂ : ∀ p ∈ τ'.bases, addr (s₂'.gpr p.1) p.2.2 = (region s₂' p.2.1).base)
    (hstk : τ'.stk = τ.stk := by rfl) (hroom : τ'.room = τ.room := by rfl) :
    Agree τ' s₁' s₂' where
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ha.wf₁.keep hl hwb hargs hab hw₁ hm₁ hsp₁ hb₁ hstk hroom
  wf₂ := ha.wf₂.keep hl hwb hargs hab hw₂ hm₂ hsp₂ hb₂ hstk hroom
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    simp only [byteAddr, region, hw₁, hw₂, hm₁, hm₂]
    exact ha.slots sl (hs ▸ h) k h₁ h₂
  sp h := by rw [hsp₁, hsp₂]; exact ha.sp (hargs ▸ h)
  argMem k h4 hk := by
    simp only [argByte, hsp₁, hsp₂, hm₁, hm₂, hstk]
    exact ha.argMem k h4 (hargs ▸ hk)

theorem kill_bases {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr) {d : Reg}
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) :
    ∀ p ∈ kill τ d, addr (s'.gpr p.1) p.2.2 = (region s' p.2.1).base := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [hg _ hp.2, hw.bases p hp.1]
  simp [region, hwr]

/-! ### Stores -/

/-- A store of `n` bytes at offset `d` of region `i` does not change byte `k`
of region `j`, if that is another region or outside `[d, d + n)`. -/
theorem write_other {τ : T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k)
    (V : BitVec (8 * n)) :
    s.mem.write (byteAddr s i d) n V (byteAddr s j k) = s.mem (byteAddr s j k) := by
  have hne := lens_ne (n := d + n) (by omega) hd
  obtain ⟨-, hdisj, -⟩ := hw.lens hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega)
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi := region_bound hw (i := i) (by omega)
  have hbj := region_bound hw (i := j) (by omega)
  apply Mem.write_apply
  intro hlt
  by_cases hji : j = i
  · subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d :=
      Offset.add_sub_add_left _ _ _
    exact Offset.not_lt_sub_ofNat hsep (by omega) hn (by omega) (h ▸ hlt)
  · have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)

theorem write_same {m₁ m₂ : Mem} {A X : Addr} {n : Nat} (V : BitVec (8 * n)) (h : m₁ X = m₂ X) :
    m₁.write A n V X = m₂.write A n V X := by
  simp only [Mem.write]; split <;> [rfl; exact h]

theorem storeSlots_ok {τ : T} (hok : SlotsOk τ) (m : MemOp) (w : Nat) (p : Bool) (wb : List (Nat × Nat × Nat)) :
    SlotsOk { τ with slots := storeSlots τ m w p, wbases := wb } := by
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

/-- A write within a writable region leaves the stack arguments alone. -/
theorem write_arg {τ : T} {s : State} (hw : Wf τ s) {A : Addr} {n : Nat} (hA : InRegions s.wr A n)
    (V : BitVec (8 * n)) {k : Nat} (hk : k < τ.argLen) :
    s.mem.write A n V (argByte s (depth τ.stk + k)) = s.mem (argByte s (depth τ.stk + k)) := by
  obtain ⟨hsp, hd⟩ := hw.args (by omega)
  obtain ⟨r, hr, hc⟩ := hA
  apply Mem.write_apply
  intro hlt
  refine hd r hr _ ?_ (hc.byte hlt)
  simp only [Region.Contains, argByte]
  rw [Offset.add_ofNat_add_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A store at a known offset of a region leaves the base-address words it does not overlap alone. -/
theorem readW_other {τ : T} {s : State} (hw : Wf τ s) {i d n j o : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (ho : o + 4 ≤ τ.lens.getD j 0) (hsep : j ≠ i ∨ d + n ≤ o ∨ o + 4 ≤ d)
    (V : BitVec (8 * n)) :
    (s.mem.write (byteAddr s i d) n V).readW (byteAddr s j o) 32 = s.mem.readW (byteAddr s j o) 32 := by
  refine Mem.readW_congr fun t ht => ?_
  rw [byteAddr_add]
  exact write_other hw hn hd (by omega) (by omega) V

/-- What `τ` says about a state stays true after a store of `n` bytes at `m` in
a writable region, with the slots and base-address words of `storeStep`. -/
theorem Wf.store {τ : T} {s : State} (hw : Wf τ s) {m : MemOp} {n : Nat} (hn : 0 < n)
    (hA : InRegions s.wr (s.ea m) n) (V : BitVec (8 * n)) (p : Bool) {nb : List Nat}
    (hnb : ∀ i ∈ nb, 4 ≤ n ∧ addr ((s.mem.write (s.ea m) n V).readW (s.ea m) 32) 0 = (region s i).base) :
    Wf { τ with slots := storeSlots τ m n p, wbases := storeWbases τ m n nb }
      { s with mem := s.mem.write (s.ea m) n V } where
  lens h := hw.lens h
  bases p h := hw.bases p h
  wbases q h := by
    simp only [storeWbases] at h
    split at h <;> [skip; cases h]
    rename_i j d had
    split at h <;> [skip; cases h]
    rename_i hfit
    have e := ea_of_addrOf hw had (by omega)
    rcases List.mem_append.mp h with h | h
    · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at h
      obtain ⟨h, hsep⟩ := h
      obtain ⟨hq, hv⟩ := hw.wbases q h
      refine ⟨hq, ?_⟩
      show addr ((s.mem.write (s.ea m) n V).readW (byteAddr s q.1 q.2.1) 32) 0 = (region s q.2.2).base
      rw [e, readW_other hw hn hfit hq hsep V]
      exact hv
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      obtain ⟨h4, hv⟩ := hnb i hi
      refine ⟨by simp only; omega, ?_⟩
      show addr ((s.mem.write (s.ea m) n V).readW (byteAddr s j d) 32) 0 = (region s i).base
      rw [← e]
      exact hv
  args h := hw.args h
  argBases q h := by
    obtain ⟨hq, he⟩ := hw.argBases q h
    refine ⟨hq, ?_⟩
    simp only [region] at he ⊢
    rw [← he]
    refine congrArg (addr · 0) ?_
    refine Mem.readW_congr fun k hk => ?_
    rw [argWord hw hq, Nat.add_assoc]
    exact write_arg hw hA V (by omega)
  stk := hw.stk
  frames := hw.frames
  room := hw.room

/-- A store of `n` bytes at `m`, of the same value in both runs if `p`. -/
theorem Agree.store {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp}
    (hr : memPub τ m = true) {n : Nat} (hn : 0 < n) {V₁ V₂ : BitVec (8 * n)} {p : Bool}
    (hv : p = true → V₁ = V₂) {nb : List Nat}
    (hA₁ : InRegions s₁.wr (s₁.ea m) n) (hA₂ : InRegions s₂.wr (s₂.ea m) n)
    (hnb₁ : ∀ i ∈ nb, 4 ≤ n ∧
      addr ((s₁.mem.write (s₁.ea m) n V₁).readW (s₁.ea m) 32) 0 = (region s₁ i).base)
    (hnb₂ : ∀ i ∈ nb, 4 ≤ n ∧
      addr ((s₂.mem.write (s₂.ea m) n V₂).readW (s₂.ea m) 32) 0 = (region s₂ i).base) :
    Agree { τ with slots := storeSlots τ m n p, wbases := storeWbases τ m n nb }
      { s₁ with mem := s₁.mem.write (s₁.ea m) n V₁ }
      { s₂ with mem := s₂.mem.write (s₂.ea m) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁.store hn hA₁ V₁ p hnb₁
  wf₂ := ha.wf₂.store hn hA₂ V₂ p hnb₂
  ok := storeSlots_ok ha.ok m n p _
  sp := ha.sp
  argMem k h4 hk := by
    show s₁.mem.write (s₁.ea m) n V₁ (argByte s₁ (depth τ.stk + k)) =
      s₂.mem.write (s₂.ea m) n V₂ (argByte s₂ (depth τ.stk + k))
    rw [write_arg ha.wf₁ hA₁ V₁ hk, write_arg ha.wf₂ hA₂ V₂ hk]
    exact ha.argMem k h4 hk
  slots := by
    intro sl hsl k hk₁ hk₂
    have hE : s₁.ea m = s₂.ea m := ha.ea hr
    have same : sl ∈ τ.slots → p = true →
        s₁.mem.write (s₁.ea m) n V₁ (byteAddr s₁ sl.1 k) =
          s₂.mem.write (s₂.ea m) n V₂ (byteAddr s₂ sl.1 k) :=
      fun h hp => by
        have hok := ha.ok sl h
        have hb := ha.byteAddr_eq (n := sl.2.1 + sl.2.2) (by omega) hok k
        rw [hE, hv hp, hb]
        exact write_same _ (hb ▸ ha.slots sl h k hk₁ hk₂)
    show s₁.mem.write _ n V₁ (byteAddr s₁ sl.1 k) = s₂.mem.write _ n V₂ (byteAddr s₂ sl.1 k)
    simp only [storeSlots] at hsl
    split at hsl
    · rename_i i d had
      split at hsl
      · rename_i hfit
        have e₁ := ea_of_addrOf ha.wf₁ had (by omega)
        have e₂ := ea_of_addrOf ha.wf₂ had (by omega)
        have hsl' : (p = true ∧ sl = (i, d, n)) ∨ (sl ∈ τ.slots ∧
            (p = true ∨ sl.1 ≠ i ∨ d + n ≤ sl.2.1 ∨ sl.2.1 + sl.2.2 ≤ d)) := by
          split at hsl
          · rename_i hp
            rcases List.mem_cons.mp hsl with h | h
            · exact .inl ⟨hp, h⟩
            · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at h
              exact .inr h
          · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at hsl
            exact .inr hsl
        rcases hsl' with ⟨hp, rfl⟩ | ⟨h, hsep⟩
        · simp only at hk₁ hk₂
          simp only [e₁, e₂, Mem.write, hv hp]
          have hd : ∀ s : State, byteAddr s i k - byteAddr s i d = BitVec.ofNat 64 (k - d) :=
            fun s => (Offset.add_sub_add_left _ _ _).trans (Offset.ofNat_sub_ofNat (by omega))
          have hlt : (BitVec.ofNat 64 (k - d)).toNat < n := by
            rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
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

/-! ### ALU instructions, uniformly -/

/-- The result, carry and overflow of an ALU operation. -/
def aluOut (op : AluOp) (a b : BitVec 32) (cf : Option Bool) : Option (BitVec 32 × Bool × Bool) :=
  match op with
  | .add => let r := a + b; some (r, 2 ^ 32 ≤ a.toNat + b.toNat, addOverflow a b r)
  | .adc => cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 32
    (r, 2 ^ 32 ≤ a.toNat + b.toNat + c.toNat, addOverflow a b r)
  | .sub | .cmp => let r := a - b; some (r, a.toNat < b.toNat, subOverflow a b r)
  | .sbb => cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 32
    (r, a.toNat < b.toNat + c.toNat, subOverflow a b r)
  | .and | .test => some (a &&& b, false, false)
  | .or => some (a ||| b, false, false)
  | .xor => some (a ^^^ b, false, false)

theorem aluOut_cf {op : AluOp} (h : usesCarry op = false) (a b : BitVec 32)
    (c c' : Option Bool) : aluOut op a b c = aluOut op a b c' := by
  cases op <;> simp_all [usesCarry, aluOut]

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (X86.readSrc s src).bind fun b =>
      (aluOut op (s.gpr d) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg d r else arithFlags s r c o := by
  cases op <;> simp [execAlu, aluOut, writes, Function.comp_def]

section
variable {s : State} {r : Reg} {v x : BitVec 32} {c o : Bool}
@[simp] theorem arithFlags_gpr : (arithFlags s x c o).gpr = s.gpr := rfl
@[simp] theorem arithFlags_mem : (arithFlags s x c o).mem = s.mem := rfl
@[simp] theorem arithFlags_wr : (arithFlags s x c o).wr = s.wr := rfl
@[simp] theorem arithFlags_cf : (arithFlags s x c o).cf = some c := rfl
@[simp] theorem arithFlags_of : (arithFlags s x c o).of = some o := rfl
@[simp] theorem arithFlags_zf : (arithFlags s x c o).zf = some (x == 0) := rfl
@[simp] theorem arithFlags_sf : (arithFlags s x c o).sf = some x.msb := rfl
@[simp] theorem setReg_cf : (s.setReg r v).cf = s.cf := rfl
@[simp] theorem setReg_of : (s.setReg r v).of = s.of := rfl
@[simp] theorem setReg_zf : (s.setReg r v).zf = s.zf := rfl
@[simp] theorem setReg_sf : (s.setReg r v).sf = s.sf := rfl
@[simp] theorem setReg_mem : (s.setReg r v).mem = s.mem := rfl
@[simp] theorem setReg_wr : (s.setReg r v).wr = s.wr := rfl
end

theorem regs_filter {τ : T} {s₁ s₂ s₁' s₂' : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} (h₁ : ∀ r, r ≠ d → s₁'.gpr r = s₁.gpr r)
    (h₂ : ∀ r, r ≠ d → s₂'.gpr r = s₂.gpr r) :
    ∀ r ∈ τ.regs.erase d, s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  simp only [RegSet.mem_erase] at hr
  rw [h₁ r hr.1, h₂ r hr.1, h r hr.2]

theorem not_pub_set {τ : T} {d : Reg} {p : Bool} (hp : ¬ p = true) :
    set τ d p = τ.regs.erase d := by
  simp [set, hp]

theorem alu_sound {τ : T} {op : AluOp} {d : Reg} {src : Src} {s₁ s₂ : State}
    {b₁ b₂ : BitVec 32} {out₁ out₂ : BitVec 32 × Bool × Bool}
    (ha : AgreeRF τ.regs τ.flags s₁ s₂) (hb : srcPub τ src = true → b₁ = b₂)
    (ho₁ : aluOut op (s₁.gpr d) b₁ s₁.cf = some out₁)
    (ho₂ : aluOut op (s₂.gpr d) b₂ s₂.cf = some out₂) :
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    AgreeRF (if writes op then set τ d p else τ.regs) p
      (if writes op then (arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2).setReg d out₁.1
        else arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2)
      (if writes op then (arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2).setReg d out₂.1
        else arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) := by
  intro p
  by_cases hp : p = true
  · have hp' := hp
    simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp'
    obtain ⟨⟨hd, hsp⟩, hc⟩ := hp'
    obtain rfl := hb hsp
    have hout : aluOut op (s₁.gpr d) b₁ s₁.cf = aluOut op (s₂.gpr d) b₁ s₂.cf := by
      rw [ha.1 d (pub_iff.mp hd)]
      rcases hc with hc | hc
      · exact aluOut_cf hc _ _ _ _
      · rw [(ha.2 hc).1]
    rw [hout, ho₂] at ho₁
    cases ho₁
    refine ⟨fun r hr => ?_, fun _ => ?_⟩
    · split
      · rename_i hw
        simp only [hw, ite_true] at hr
        simp only [RegUpd.gpr_setReg, arithFlags_gpr]
        split
        · rfl
        · rename_i hrd
          simp only [set, hp, ite_true, RegSet.mem_insert, hrd, false_or] at hr
          exact ha.1 r hr
      · rename_i hw
        simp only [hw, Bool.false_eq_true, ite_false] at hr ⊢
        simpa using ha.1 r hr
    · split <;> simp
  · refine ⟨fun r hr => ?_, fun h => absurd h hp⟩
    split
    · rename_i hw
      simp only [hw, ite_true, not_pub_set hp] at hr
      refine regs_filter ha.1 (fun r hr => ?_) (fun r hr => ?_) r hr <;>
        simp [RegUpd.gpr_setReg, hr]
    · rename_i hw
      simp only [hw, Bool.false_eq_true, ite_false] at hr
      simpa using ha.1 r hr

/-! ### Instructions that write a register -/

/-- The register an instruction may write, if it writes exactly one (none for
stores, and for `mul`, which writes two). -/
def dst : Instr → Option Reg
  | .mov d _ | .alu _ d _ | .shift _ d _ | .bswap d | .movzx8 d _ | .pop d _ => some d
  | .store .. | .store8 .. | .push _ | .mul _ | .movdquLoad .. | .movdquStore .. | .xop _ => none

/-- Whether an instruction may write the register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .eax || r == .edx
  | _ => dst i == some r

theorem dst_ne_of_clobbers {i : Instr} {r : Reg} (h : clobbers i r = false) : dst i ≠ some r := by
  cases i <;> simp_all [clobbers, dst]

theorem exec_dst {i : Instr} {d : Reg} (hd : dst i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.wr = s.wr ∧ s'.mem = s.mem ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i with
  | push | pop => simp only [exec, reduceCtorEq] at h
  | mov d' src =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact ⟨rfl, rfl, fun r h => setReg_ne h⟩
  | alu op d' src =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, -, out, -, rfl⟩ := h
    split <;> exact ⟨rfl, rfl, fun r h => by simp [RegUpd.gpr_setReg, h]⟩
  | shift op d' n =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
      exact ⟨rfl, rfl, fun r h => by simp [State.setReg, State.setFlags, h]⟩
  | bswap d' =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, fun r h => setReg_ne h⟩
  | movzx8 d' m =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact ⟨rfl, rfl, fun r h => setReg_ne h⟩
  | store m r => simp [dst] at hd
  | store8 m r => simp [dst] at hd
  | mul r | movdquLoad | movdquStore | xop => simp [dst] at hd

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dst i = some d) (hesp : d ≠ .esp)
    {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) (hstk : τ'.stk = τ.stk := by rfl)
    (hroom : τ'.room = τ.room := by rfl) : Agree τ' s₁' s₂' := by
  obtain ⟨hw₁, hm₁, hg₁⟩ := exec_dst hd e₁
  obtain ⟨hw₂, hm₂, hg₂⟩ := exec_dst hd e₂
  exact ha.keep hrf hl hs hwb hargs hab hw₁ hw₂ hm₁ hm₂ (hg₁ _ (Ne.symm hesp)) (hg₂ _ (Ne.symm hesp))
    (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h)) (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h))
    hstk hroom

theorem execMul_gpr (r : Reg) (s : State) {q : Reg} (h₁ : q ≠ .eax) (h₂ : q ≠ .edx) :
    (execMul r s).gpr q = s.gpr q := by
  simp [execMul, State.setReg, State.setFlags, h₁, h₂]

theorem mul_bases {τ : T} {s : State} (hw : Wf τ s) (r : Reg) :
    ∀ p ∈ (kill τ .eax).filter (·.1 != .edx),
      addr ((execMul r s).gpr p.1) p.2.2 = (region (execMul r s) p.2.1).base := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [execMul_gpr r s hp.1.2 hp.2, hw.bases p hp.1.1]; rfl

theorem Agree.mul {τ : T} {r : Reg} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) :
    Agree (mulStep τ r) (execMul r s₁) (execMul r s₂) := by
  refine ha.keep ⟨fun q hq => ?_, fun hp => ?_⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (execMul_gpr r s₁ (by decide) (by decide)) (execMul_gpr r s₂ (by decide) (by decide))
    (mul_bases ha.wf₁ r) (mul_bases ha.wf₂ r)
  · simp only [mulStep] at hq
    by_cases hp : (pub τ .eax && pub τ r) = true
    · have hp' := hp
      simp only [Bool.and_eq_true] at hp'
      have e₁ := ha.reg hp'.1
      have e₂ := ha.reg hp'.2
      simp only [hp, ite_true, RegSet.mem_insert] at hq
      by_cases h₁ : q = .eax
      · subst h₁; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      by_cases h₂ : q = .edx
      · subst h₂; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      simp only [h₁, h₂, false_or] at hq
      rw [execMul_gpr r s₁ h₁ h₂, execMul_gpr r s₂ h₁ h₂]; exact ha.rf.1 q hq
    · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hq
      rw [execMul_gpr r s₁ hq.2.1 hq.1, execMul_gpr r s₂ hq.2.1 hq.1]; exact ha.rf.1 q hq.2.2
  · simp only [mulStep, Bool.and_eq_true] at hp
    simp [execMul, State.setReg, State.setFlags, ha.reg hp.1, ha.reg hp.2]

theorem loadBases_ok {τ : T} {s : State} (hw : Wf τ s) {m : MemOp} {i : Nat} (hi : i ∈ loadBases τ m) :
    addr (s.mem.readW (s.ea m) 32) 0 = (region s i).base := by
  simp only [loadBases, List.mem_append] at hi
  rcases hi with hi | hi
  · split at hi
    · rename_i j o had
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hi
      obtain ⟨q, ⟨hq, hj, ho⟩, rfl⟩ := hi
      obtain ⟨hb, hv⟩ := hw.wbases q hq
      rw [hj, ho] at hb hv
      rw [ea_of_addrOf hw had (by omega)]
      exact hv
    · simp at hi
  · split at hi
    · rename_i hb
      simp only [beq_iff_eq] at hb
      simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hi
      obtain ⟨q, ⟨hq, hqo⟩, rfl⟩ := hi
      have := (hw.argBases q hq).2
      rw [hqo] at this
      show addr (s.mem.readW (addr (s.gpr m.base) m.disp) 32) 0 = _
      rw [hb]; exact this
    · simp at hi

theorem movBases_ok {τ : T} {s : State} (hw : Wf τ s) {d : Reg} {src : Src} {v : BitVec 32}
    (hv : X86.readSrc s src = some v) :
    ∀ p ∈ movBases τ d src, addr ((s.setReg d v).gpr p.1) p.2.2 = (region (s.setReg d v) p.2.1).base := by
  have hk : ∀ p ∈ kill τ d, addr ((s.setReg d v).gpr p.1) p.2.2 = (region (s.setReg d v) p.2.1).base :=
    kill_bases (s' := s.setReg d v) hw rfl fun _ h => setReg_ne h
  cases src with
  | reg r =>
    simp only [X86.readSrc, Option.some.injEq] at hv; subst hv
    intro p hp
    simp only [movBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    rcases hp with hp | ⟨q, ⟨hq, hqr⟩, rfl⟩
    · exact hk p hp
    · simp only [State.setReg, ite_true]
      rw [← hqr]
      exact hw.bases q hq
  | imm _ => exact hk
  | mem m =>
    simp only [X86.readSrc, State.load32] at hv
    split at hv <;> [skip; cases hv]
    cases hv
    intro p hp
    simp only [movBases, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨i, hi, rfl⟩
    · exact hk p hp
    · simp only [State.setReg, ite_true]
      exact loadBases_ok hw hi

theorem Agree.readSrc {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {src : Src}
    (hs : srcPub τ src = true) {v₁ v₂ : BitVec 32} (e₁ : X86.readSrc s₁ src = some v₁)
    (e₂ : X86.readSrc s₂ src = some v₂) : v₁ = v₂ := by
  cases src with
  | reg r =>
    simp only [X86.readSrc, Option.some.injEq] at e₁ e₂
    rw [← e₁, ← e₂, h.reg hs]
  | imm v =>
    simp only [X86.readSrc, Option.some.injEq] at e₁ e₂
    rw [← e₁, ← e₂]
  | mem m => simp [srcPub] at hs

theorem regBases_ok {τ : T} {s : State} (hw : Wf τ s) {m : MemOp} {r : Reg} :
    ∀ i ∈ regBases τ r, 4 ≤ 32 / 8 ∧
      addr ((s.mem.writeW (s.ea m) (s.gpr r)).readW (s.ea m) 32) 0 = (region s i).base := by
  intro i hi
  refine ⟨(Nat.le_refl _), ?_⟩
  rw [Mem.readW_writeW_self32]
  simp only [regBases, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hi
  obtain ⟨q, ⟨hq, hr, h0⟩, rfl⟩ := hi
  have := hw.bases q hq
  rwa [hr, h0] at this

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop | movdquLoad | movdquStore | xop => simp only [step, reduceCtorEq] at hs
  | mov d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨hd, hok⟩ := hok
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    refine ⟨ha.srcAddrs hok, ha.keep ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
      rfl rfl rfl rfl rfl rfl rfl rfl rfl (setReg_ne fun h => hd h.symm)
      (setReg_ne fun h => hd h.symm) (movBases_ok ha.wf₁ hv₁) (movBases_ok ha.wf₂ hv₂)⟩
    simp only [Bool.or_eq_true] at hp
    rcases hp with hp | hp
    · exact ha.readSrc hp hv₁ hv₂
    · cases src with
      | mem m =>
        simp only [loadPub, Bool.or_eq_true] at hp
        simp only [X86.readSrc, State.load32] at hv₁ hv₂
        split at hv₁ <;> [skip; cases hv₁]
        split at hv₂ <;> [skip; cases hv₂]
        cases hv₁; cases hv₂
        rcases hp with hp | hp
        · exact ha.readW hp
        · exact ha.readArg hp
      | reg _ => simp [loadPub] at hp
      | imm _ => simp [loadPub] at hp
  | store m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 4) hm (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
      (regBases_ok ha.wf₁) (regBases_ok ha.wf₂)
  | alu op d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨hd, hok⟩ := hok
    refine ⟨ha.srcAddrs hok, ha.write rfl hd e₁ e₂ ?_ rfl rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
    exact alu_sound ha.rf (fun hp => ha.readSrc hp hb₁ hb₂) ho₁ ho₂
  | shift op d n =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hd; cases hs
    simp only [bne_iff_ne, ne_eq] at hd
    refine ⟨rfl, ha.write rfl hd e₁ e₂ ?_ rfl rfl rfl rfl rfl fun _ h => h⟩
    by_cases hn : 1 ≤ n ∧ n ≤ 31
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
        simp [State.setFlags, hd, hfl]
  | bswap d =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hd; cases hs
    simp only [bne_iff_ne, ne_eq] at hd
    refine ⟨rfl, ha.write rfl hd e₁ e₂ ?_ rfl rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨fun r hr => ?_, fun hf => by simpa using ha.rf.2 hf⟩
    by_cases hrd : r = d
    · subst hrd; simp [State.setReg, ha.rf.1 r hr]
    · simp [State.setReg, hrd, ha.rf.1 r hr]
  | movzx8 d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨hd, hm⟩ := hok
    refine ⟨by simp [addrs, ha.ea hm], ha.write rfl hd e₁ e₂ ?_ rfl rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, -, rfl⟩ := e₁; obtain ⟨x₂, -, rfl⟩ := e₂
    exact ⟨regs_set (p := false) ha.rf.1 (fun h => by cases h), fun hf => ha.rf.2 hf⟩
  | store8 m r =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 1) hm (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
      (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim)
  | mul r =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨rfl, ha.mul⟩

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hzf, hcf]

/-! ### Meets -/

/-- `below top n`: the `n` bytes below `top`. -/
theorem below_sub {top : Addr} {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 64) :
    Region.Sub ⟨top - BitVec.ofNat 64 a, a⟩ ⟨top - BitVec.ofNat 64 b, b⟩ := by
  exact Offset.below_mono top hab hb

/-- Knowing less. -/
theorem Wf.mono {τ τ' : T} {s : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens ∨ τ'.lens = [])
    (hb : ∀ p ∈ τ'.bases, p ∈ τ.bases) (hwb : ∀ p ∈ τ'.wbases, p ∈ τ.wbases ∧ τ'.lens = τ.lens)
    (hargs : τ'.argLen = 0 ∨ τ'.argLen = τ.argLen ∧ τ'.stk = τ.stk)
    (hab : ∀ p ∈ τ'.argBases, p ∈ τ.argBases ∧ τ'.argLen = τ.argLen ∧ τ'.stk = τ.stk)
    (hsr : τ'.stk = τ.stk ∧ τ'.room ≤ τ.room ∨ τ'.stk = [] ∧ τ'.room = 0) : Wf τ' s where
  lens h := by
    rcases hl with hl | hl
    · rw [hl]; exact hw.lens (hl ▸ h)
    · exact absurd hl h
  bases p h := hw.bases p (hb p h)
  wbases p h := by obtain ⟨h, hl⟩ := hwb p h; rw [hl]; exact hw.wbases p h
  args h := by
    rcases hargs with h0 | ⟨ha, hs⟩
    · omega
    · rw [ha, hs]; exact hw.args (ha ▸ h)
  argBases p h := by obtain ⟨h, ha, hs⟩ := hab p h; rw [ha, hs]; exact hw.argBases p h
  stk := by
    rcases hsr with ⟨hs, -⟩ | ⟨hs, -⟩
    · rw [hs]; exact hw.stk
    · rw [hs, depth]; exact (s.gpr .esp).isLt
  frames p h := by
    rcases hsr with ⟨hs, -⟩ | ⟨hs, -⟩
    · exact hw.frames p (hs ▸ h)
    · rw [hs] at h; cases h
  room h := by
    rcases hsr with ⟨hs, hr⟩ | ⟨-, hr⟩
    · obtain ⟨h₁, h₂⟩ := hw.room (by omega)
      have := hw.stk
      rw [hs]
      exact ⟨by omega, fun r hr' => Region.Disjoint.sub_left (h₂ r hr') (below_sub hr (by omega))⟩
    · omega

theorem Agree.mono {τ τ' : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (hr : ∀ r ∈ τ'.regs, r ∈ τ.regs)
    (hf : τ'.flags = true → τ.flags = true) (hl : τ'.lens = τ.lens ∨ τ'.lens = [])
    (hb : ∀ p ∈ τ'.bases, p ∈ τ.bases) (hs : ∀ sl ∈ τ'.slots, sl ∈ τ.slots ∧ τ'.lens = τ.lens)
    (hwb : ∀ p ∈ τ'.wbases, p ∈ τ.wbases ∧ τ'.lens = τ.lens)
    (hargs : τ'.argLen = 0 ∨ τ'.argLen = τ.argLen ∧ τ'.stk = τ.stk)
    (hab : ∀ p ∈ τ'.argBases, p ∈ τ.argBases ∧ τ'.argLen = τ.argLen ∧ τ'.stk = τ.stk)
    (hsr : τ'.stk = τ.stk ∧ τ'.room ≤ τ.room ∨ τ'.stk = [] ∧ τ'.room = 0) : Agree τ' s₁ s₂ where
  rf := ⟨fun r h' => h.rf.1 r (hr r h'), fun hf' => h.rf.2 (hf hf')⟩
  wr hne := by
    rcases hl with hl | hl
    · exact h.wr (hl ▸ hne)
    · exact absurd hl hne
  wf₁ := h.wf₁.mono hl hb hwb hargs hab hsr
  wf₂ := h.wf₂.mono hl hb hwb hargs hab hsr
  ok sl hsl := by obtain ⟨hsl, hl⟩ := hs sl hsl; rw [hl]; exact h.ok sl hsl
  slots sl hsl := h.slots sl (hs sl hsl).1
  sp hpos := by
    rcases hargs with h0 | ⟨ha, -⟩
    · omega
    · exact h.sp (ha ▸ hpos)
  argMem k h4 hk := by
    rcases hargs with h0 | ⟨ha, hs⟩
    · omega
    · rw [hs]; exact h.argMem k h4 (ha ▸ hk)

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  refine h.mono (fun r h => (RegSet.mem_inter.mp h).1) (fun hf => ?_) ?_ (fun p hp => (List.mem_filter.mp hp).1)
    (fun sl hsl => ?_) (fun p hp => ?_) ?_ (fun p hp => ?_) ?_ <;> simp only [meet] at *
  · simp only [Bool.and_eq_true] at hf; exact hf.1
  · split <;> simp
  · split at hsl <;> [rename_i he; cases hsl]
    exact ⟨(List.mem_filter.mp hsl).1, by simp [he]⟩
  · split at hp <;> [rename_i he; cases hp]
    exact ⟨(List.mem_filter.mp hp).1, by simp [he]⟩
  · split <;> simp_all
  · split at hp <;> [rename_i he; cases hp]
    exact ⟨(List.mem_filter.mp hp).1, by simp [he]⟩
  · split <;> simp_all [Nat.min_le_left]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  refine h.mono (fun r h => (RegSet.mem_inter.mp h).2) (fun hf => ?_) ?_
    (fun p hp => by simpa using (List.mem_filter.mp hp).2)
    (fun sl hsl => ?_) (fun p hp => ?_) ?_ (fun p hp => ?_) ?_ <;> simp only [meet] at *
  · simp only [Bool.and_eq_true] at hf; exact hf.2
  · split <;> simp_all
  · split at hsl <;> [rename_i he; cases hsl]
    exact ⟨by simpa using (List.mem_filter.mp hsl).2, by simp [he]⟩
  · split at hp <;> [rename_i he; cases hp]
    exact ⟨by simpa using (List.mem_filter.mp hp).2, by simp [he]⟩
  · split <;> simp_all
  · split at hp <;> [rename_i he; cases hp]
    exact ⟨by simpa using (List.mem_filter.mp hp).2, by simp [he]⟩
  · split <;> simp_all [Nat.min_le_right]

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hwb⟩, ha⟩, hab⟩, hst⟩, hro⟩ := hle
  refine h.mono (fun r h => RegSet.mem_of_subset hr h) (fun hf' => ?_) (.inl hl) hb (fun sl h => ⟨hs sl h, hl⟩) (fun p h => ⟨hwb p h, hl⟩)
    (.inr ⟨ha, hst⟩) (fun p h => ⟨hab p h, ha, hst⟩) (.inl ⟨hst, hro⟩)
  rcases hf with hf | hf
  · simp [hf'] at hf
  · exact hf

/-- The return address and the `n` bytes of arguments above it, as one region:
disjoint from `r` if both parts are. -/
theorem frame_disjoint {esp : BitVec 32} {n : Nat} (hfit : esp.toNat + 4 + n ≤ 2 ^ 32) {r : Region}
    (hret : Region.Disjoint ⟨esp.setWidth 64, 4⟩ r) (hargs : Region.Disjoint ⟨addr esp 4, n⟩ r) :
    Region.Disjoint ⟨esp.setWidth 64, 4 + n⟩ r := by
  intro a ha hr
  simp only [Region.Contains] at ha
  by_cases h4 : (a - esp.setWidth 64).toNat < 4
  · exact hret a (by simp only [Region.Contains]; omega) hr
  · refine hargs a ?_ hr
    simp only [Region.Contains]
    rw [addr_eq (by omega), Offset.sub_add_eq, Offset.toNat_sub_ofNat]
    have := (a - esp.setWidth 64).isLt
    omega

/-- Byte `k` above `esp`, as byte `k % 4` of argument word `(k - 4) / 4`. -/
theorem argByte_eq {s : State} {n : Nat} (hfit : (s.gpr .esp).toNat + n ≤ 2 ^ 32) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    argByte s k = argAddr s ((k - 4) / 4) + BitVec.ofNat 64 ((k - 4) % 4) := by
  simp only [argByte, argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * ((k - 4) / 4))).setWidth 64 =
    addr (s.gpr .esp) (4 + 4 * ((k - 4) / 4)) from rfl, addr_eq (by omega), BitVec.add_assoc,
    ← BitVec.ofNat_add]
  congr 2; omega

/-! ### The stack -/

theorem frameList_shift (xs : List (Option Nat)) (j o : Nat) :
    frameList xs j o = (frameList xs 0 0).map fun p => (p.1 + j, p.2.1 + o, p.2.2) := by
  induction xs generalizing j o with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none =>
      simp only [frameList]
      rw [ih j (o + 4), ih 0 (0 + 4), List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      omega
    | some n =>
      simp only [frameList, List.map_cons]
      rw [ih (j + 1) (o + n), ih (0 + 1) (0 + n), List.map_map]
      refine congr (congrArg _ (by simp)) (List.map_congr_left fun p _ => ?_)
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      omega

theorem frameList_bound {xs : List (Option Nat)} {j o : Nat} {p : Nat × Nat × Nat}
    (h : p ∈ frameList xs j o) :
    j ≤ p.1 ∧ p.1 < j + nframes xs ∧ o ≤ p.2.1 ∧ p.2.1 + p.2.2 ≤ o + depth xs := by
  induction xs generalizing j o with
  | nil => cases h
  | cons x xs ih =>
    cases x with
    | none =>
      have := ih h
      simp only [nframes, depth, itemSize]; omega
    | some n =>
      simp only [frameList, List.mem_cons] at h
      rcases h with rfl | h
      · simp only [nframes, depth, itemSize]; omega
      · have := ih h
        simp only [nframes, depth, itemSize]; omega

theorem frameList_idx {xs : List (Option Nat)} {i : Nat} (hi : i < nframes xs) (j o : Nat) :
    ∃ p ∈ frameList xs j o, p.1 = j + i := by
  induction xs generalizing i j o with
  | nil => simp [nframes] at hi
  | cons x xs ih =>
    cases x with
    | none => exact ih hi j (o + 4)
    | some n =>
      simp only [nframes] at hi
      cases i with
      | zero => exact ⟨_, List.mem_cons_self .., by simp⟩
      | succ i =>
        obtain ⟨p, hp, he⟩ := ih (i := i) (by omega) (j + 1) (o + n)
        exact ⟨p, List.mem_cons_of_mem _ hp, by omega⟩

/-- `addr` from two stack pointers that are the same distance below the stack pointer on entry. -/
theorem addr_move {x x' : BitVec 32} {d d' : Nat} (h : x'.toNat + d' = x.toNat + d) (o : Nat) :
    addr x' (d' + o) = addr x (d + o) := by
  simp only [addr]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.add_mod_mod, Nat.add_mod_mod, ← Nat.add_assoc, ← Nat.add_assoc, h]

theorem argByte_move {s s' : State} {d d' : Nat}
    (h : (s'.gpr .esp).toNat + d' = (s.gpr .esp).toNat + d) (k : Nat) :
    argByte s' (d' + k) = argByte s (d + k) := by
  simp only [argByte]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (s'.gpr .esp).toNat) (by have := (s'.gpr .esp).isLt; omega),
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat) (by have := (s.gpr .esp).isLt; omega),
    Nat.add_mod_mod, Nat.add_mod_mod, ← Nat.add_assoc, ← Nat.add_assoc, h]

/-- The known region bases of `esp`: those of the frames of the stack, the
outermost first (so that `addrOf` finds, for an offset, the frame it is in). -/
def stkBases (stk : List (Option Nat)) : List (Reg × Nat × Nat) :=
  ((frameList stk 0 0).map fun p => (.esp, p.1, p.2.1)).reverse

theorem stkBases_ok {stk : List (Option Nat)} {s : State}
    (hf : ∀ p ∈ frameList stk 0 0, s.wr[p.1]? = some ⟨addr (s.gpr .esp) p.2.1, p.2.2⟩) :
    ∀ p ∈ stkBases stk, addr (s.gpr p.1) p.2.2 = (region s p.2.1).base := by
  intro p hp
  simp only [stkBases, List.mem_reverse, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [region, List.getD_eq_getElem?_getD, hf q hq, Option.getD_some]

/-- A writable region is a frame of the stack, or one of the others. -/
theorem Wf.wr_cases {τ : T} {s : State} (hw : Wf τ s) {r : Region} (hr : r ∈ s.wr) :
    (∃ p ∈ frameList τ.stk 0 0, r = ⟨addr (s.gpr .esp) p.2.1, p.2.2⟩) ∨
      r ∈ s.wr.drop (nframes τ.stk) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  by_cases h : i < nframes τ.stk
  · obtain ⟨p, hp, he⟩ := frameList_idx h 0 0
    have := hw.frames p hp
    rw [he, Nat.zero_add, List.getElem?_eq_getElem hi, Option.some.injEq] at this
    exact .inl ⟨p, hp, this⟩
  · refine .inr ?_
    have : s.wr[i] = (s.wr.drop (nframes τ.stk))[i - nframes τ.stk]'(by simp; omega) := by
      simp only [List.getElem_drop]; congr 1; omega
    rw [this]; exact List.getElem_mem _

/-- The `m` bytes below `esp`, if calls and frames may use them. -/
def belowSp (s : State) (m : Nat) : Region := ⟨(s.gpr .esp - BitVec.ofNat 32 m).setWidth 64, m⟩

theorem sub_setWidth {e : BitVec 32} {m : Nat} (h : m ≤ e.toNat) :
    (e - BitVec.ofNat 32 m).setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  have := e.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := m) (by omega), Nat.mod_eq_of_lt (a := m) (by omega),
    Nat.mod_eq_of_lt (a := e.toNat) (by omega)]
  omega

/-- The bytes below `esp` that calls and frames may use lie outside every
writable region and the arguments. -/
theorem Wf.below {τ : T} {s : State} (hw : Wf τ s) {m : Nat} (hm : 0 < m)
    (hroom : depth τ.stk + m ≤ τ.room) :
    m ≤ (s.gpr .esp).toNat ∧ (∀ r ∈ s.wr, (belowSp s m).Disjoint r) ∧
      (0 < τ.argLen → (belowSp s m).Disjoint ⟨argByte s (depth τ.stk), τ.argLen⟩) := by
  obtain ⟨h₁, h₂⟩ := hw.room (by omega)
  have hs := hw.stk
  have hm' : m ≤ (s.gpr .esp).toNat := by omega
  simp only [belowSp, sub_setWidth hm']
  refine ⟨hm', fun r hr => ?_, fun hpos => ?_⟩
  · rcases hw.wr_cases hr with ⟨p, hp, rfl⟩ | hr
    · have hb := frameList_bound hp
      rw [addr_eq (by omega)]
      exact Offset.disjoint_below_above _ (by omega)
    · exact Region.Disjoint.sub_left (h₂ r hr) (Offset.below_sub_below _ (by omega) (by omega))
  · have := (hw.args hpos).1
    exact Offset.disjoint_below_above _ (by omega)

/-- Byte `k` of writable region `j` lies in a writable region. -/
theorem Wf.byte_mem {τ : T} {s : State} (hw : Wf τ s) {j k : Nat} (hk : k < τ.lens.getD j 0) :
    ∃ r ∈ s.wr, r.Contains (byteAddr s j k) 1 := by
  have hne := lens_ne (n := k + 1) (by omega) hk
  obtain ⟨hj, hr⟩ := region_mem hw hne (i := j) (by omega)
  have hb := region_bound hw (i := j) (by omega)
  refine ⟨_, List.getElem_mem hj, ?_⟩
  rw [← hr]
  have hl := region_len hw hne j
  simp only [Region.Contains, byteAddr]
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  omega

/-- What `τ` says about a state stays true when `esp` moves along the stack
`τ'.stk` and memory changes outside the writable regions and the arguments. -/
theorem Wf.moveSp {τ τ' : T} {s s' : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hroom : τ'.room = τ.room) (hnf : nframes τ'.stk = nframes τ.stk)
    (hE : (s'.gpr .esp).toNat + depth τ'.stk = (s.gpr .esp).toNat + depth τ.stk)
    (hwr : s'.wr = s.wr)
    (hmem : ∀ x, ((∃ r ∈ s.wr, r.Contains x 1) ∨ ∃ k < τ.argLen, x = argByte s (depth τ.stk + k)) →
      s'.mem x = s.mem x)
    (hframes : ∀ p ∈ frameList τ'.stk 0 0, s'.wr[p.1]? = some ⟨addr (s'.gpr .esp) p.2.1, p.2.2⟩)
    (hb : ∀ p ∈ τ'.bases, addr (s'.gpr p.1) p.2.2 = (region s' p.2.1).base) : Wf τ' s' where
  lens h := by rw [hwr, hl]; exact hw.lens (hl ▸ h)
  bases := hb
  wbases p h := by
    rw [hwb] at h
    obtain ⟨hp, hv⟩ := hw.wbases p h
    refine ⟨hl ▸ hp, ?_⟩
    have e : ∀ q, byteAddr s' q = byteAddr s q := fun q => by
      funext k; simp only [byteAddr, region, hwr]
    simp only [region, hwr] at hv ⊢
    rw [e, ← hv]
    refine congrArg (addr · 0) ?_
    refine Mem.readW_congr fun t ht => ?_
    rw [byteAddr_add]
    exact hmem _ (.inl (hw.byte_mem (by omega)))
  args h := by
    rw [hargs] at h ⊢
    obtain ⟨h₁, h₂⟩ := hw.args h
    refine ⟨by omega, fun r hr => ?_⟩
    rw [← Nat.add_zero (depth τ'.stk), argByte_move hE, Nat.add_zero]
    exact h₂ r (hwr ▸ hr)
  argBases p h := by
    rw [hab] at h
    obtain ⟨hp, hv⟩ := hw.argBases p h
    refine ⟨hargs ▸ hp, ?_⟩
    rw [addr_move hE]
    simp only [region, hwr] at hv ⊢
    rw [← hv]
    refine congrArg (addr · 0) ?_
    refine Mem.readW_congr fun t ht => ?_
    rw [argWord hw hp]
    exact hmem _ (.inr ⟨p.1 + t, by omega, by rw [Nat.add_assoc]⟩)
  stk := by rw [hE]; exact hw.stk
  frames := hframes
  room h := by
    rw [hroom] at h ⊢
    obtain ⟨h₁, h₂⟩ := hw.room h
    refine ⟨by omega, fun r hr => ?_⟩
    rw [← Nat.add_zero (depth τ'.stk), argByte_move hE, Nat.add_zero]
    rw [hnf, hwr] at hr
    exact h₂ r hr

theorem Agree.moveSp {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hroom : τ'.room = τ.room) (hnf : nframes τ'.stk = nframes τ.stk)
    (hE₁ : (s₁'.gpr .esp).toNat + depth τ'.stk = (s₁.gpr .esp).toNat + depth τ.stk)
    (hE₂ : (s₂'.gpr .esp).toNat + depth τ'.stk = (s₂.gpr .esp).toNat + depth τ.stk)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr)
    (hm₁ : ∀ x, ((∃ r ∈ s₁.wr, r.Contains x 1) ∨ ∃ k < τ.argLen, x = argByte s₁ (depth τ.stk + k)) →
      s₁'.mem x = s₁.mem x)
    (hm₂ : ∀ x, ((∃ r ∈ s₂.wr, r.Contains x 1) ∨ ∃ k < τ.argLen, x = argByte s₂ (depth τ.stk + k)) →
      s₂'.mem x = s₂.mem x)
    (hf₁ : ∀ p ∈ frameList τ'.stk 0 0, s₁'.wr[p.1]? = some ⟨addr (s₁'.gpr .esp) p.2.1, p.2.2⟩)
    (hf₂ : ∀ p ∈ frameList τ'.stk 0 0, s₂'.wr[p.1]? = some ⟨addr (s₂'.gpr .esp) p.2.1, p.2.2⟩)
    (hb₁ : ∀ p ∈ τ'.bases, addr (s₁'.gpr p.1) p.2.2 = (region s₁' p.2.1).base)
    (hb₂ : ∀ p ∈ τ'.bases, addr (s₂'.gpr p.1) p.2.2 = (region s₂' p.2.1).base)
    (hsp : 0 < τ.argLen → s₁'.gpr .esp = s₂'.gpr .esp) : Agree τ' s₁' s₂' where
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ha.wf₁.moveSp hl hwb hargs hab hroom hnf hE₁ hw₁ hm₁ hf₁ hb₁
  wf₂ := ha.wf₂.moveSp hl hwb hargs hab hroom hnf hE₂ hw₂ hm₂ hf₂ hb₂
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    rw [hs] at h
    have hk := ha.ok sl h
    have e₁ : byteAddr s₁' sl.1 k = byteAddr s₁ sl.1 k := by simp only [byteAddr, region, hw₁]
    have e₂ : byteAddr s₂' sl.1 k = byteAddr s₂ sl.1 k := by simp only [byteAddr, region, hw₂]
    rw [e₁, e₂, hm₁ _ (.inl (ha.wf₁.byte_mem (by omega))), hm₂ _ (.inl (ha.wf₂.byte_mem (by omega)))]
    exact ha.slots sl h k h₁ h₂
  sp h := hsp (hargs ▸ h)
  argMem k h4 hk := by
    rw [hargs] at hk
    rw [argByte_move hE₁, argByte_move hE₂, hm₁ _ (.inr ⟨k, hk, rfl⟩), hm₂ _ (.inr ⟨k, hk, rfl⟩)]
    exact ha.argMem k h4 hk

/-- A call stores its return address below `esp`, within the bytes that the
stack may use, and so outside every writable region and the arguments. -/
def callStep (τ : T) : Option T :=
  if pub τ .esp && decide (depth τ.stk + 4 ≤ τ.room) then
    some { τ with stk := none :: τ.stk, bases := kill τ .esp ++ stkBases (none :: τ.stk) }
  else none

/-- A return loads its return address from `[esp]`. -/
def retStep (τ : T) : Option T :=
  match τ.stk with
  | none :: stk =>
    if pub τ .esp then some { τ with stk := stk, bases := kill τ .esp ++ stkBases stk } else none
  | _ => none

theorem frames_call {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr)
    (hsp : (s'.gpr .esp).toNat + 4 = (s.gpr .esp).toNat) :
    ∀ p ∈ frameList (none :: τ.stk) 0 0, s'.wr[p.1]? = some ⟨addr (s'.gpr .esp) p.2.1, p.2.2⟩ := by
  intro p hp
  simp only [frameList] at hp
  rw [frameList_shift] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have e := addr_move (x := s.gpr .esp) (x' := s'.gpr .esp) (d := 0) (d' := 4) (by omega) q.2.1
  simp only [Nat.add_zero, hwr]
  rw [hw.frames q hq, Nat.add_comm q.2.1 4, e, Nat.zero_add]

theorem frames_ret {τ : T} {stk : List (Option Nat)} (hstk : τ.stk = none :: stk) {s s' : State}
    (hw : Wf τ s) (hwr : s'.wr = s.wr) (hsp : (s'.gpr .esp).toNat = (s.gpr .esp).toNat + 4) :
    ∀ p ∈ frameList stk 0 0, s'.wr[p.1]? = some ⟨addr (s'.gpr .esp) p.2.1, p.2.2⟩ := by
  intro p hp
  have : (p.1, p.2.1 + 4, p.2.2) ∈ frameList τ.stk 0 0 := by
    rw [hstk, frameList, frameList_shift]
    exact List.mem_map.mpr ⟨p, hp, by simp⟩
  have h := hw.frames _ this
  have e := addr_move (x := s.gpr .esp) (x' := s'.gpr .esp) (d := 4) (d' := 0) (by omega) p.2.1
  simp only at h
  rw [hwr, h, Nat.zero_add] at *
  rw [e, Nat.add_comm]

end Taint

/-- The state a called function starts in: `esp` moved down by 4 and the
return address (the next of the state's unknowns) stored there. -/
def State.callEntry (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - 4) with
    mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

theorem call_callEntry (s : State) : isa.call s = some s.callEntry := rfl

@[simp] theorem State.callEntry_rd (s : State) : s.callEntry.rd = s.rd := rfl
@[simp] theorem State.callEntry_wr (s : State) : s.callEntry.wr = s.wr := rfl
@[simp] theorem State.callEntry_esp (s : State) : s.callEntry.gpr .esp = s.gpr .esp - 4 := by
  simp [State.callEntry, State.setReg]
theorem State.callEntry_gpr (s : State) {r : Reg} (h : r ≠ .esp) : s.callEntry.gpr r = s.gpr r := by
  simp [State.callEntry, State.setReg, h]
theorem State.callEntry_mem (s : State) :
    s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := rfl

theorem ofNat_four_mul_succ (n : Nat) :
    BitVec.ofNat 32 (4 * (n + 1)) = BitVec.ofNat 32 (4 * n) + 4 := by
  rw [show 4 * (n + 1) = 4 * n + 4 by omega, BitVec.ofNat_add]; rfl

theorem pushRegs_eq (s : State) (rs : List Reg) :
    (pushRegs s rs).rd = s.rd ∧ (pushRegs s rs).wr = s.wr ∧
      (pushRegs s rs).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) ∧
      ∀ r, r ≠ .esp → (pushRegs s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, by simp [pushRegs], fun _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) }
    refine ⟨h₁, h₂, ?_, fun r hr => ?_⟩
    · simp only [pushRegs, h₃, List.length_cons, ofNat_four_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.sub_sub, BitVec.add_comm]
    · simp only [pushRegs, h₄ r hr]
      simp [State.setReg, hr]

theorem popReg_eq (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).rd = s.rd ∧ (popReg s d k).wr = s.wr ∧
      (popReg s d k).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) ∧
      ∀ r, r ≠ .esp → r ≠ d → (popReg s d k).gpr r = s.gpr r := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, by simp [popReg], fun _ _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih ((s.setReg d (s.mem.readW ((s.gpr .esp).setWidth 64) 32)).setReg .esp
      (s.gpr .esp + 4))
    refine ⟨h₁, h₂, ?_, fun r hr hr' => ?_⟩
    · simp only [popReg, h₃, ofNat_four_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.add_assoc, BitVec.add_comm (4 : BitVec 32)]
    · simp only [popReg, h₄ r hr hr']
      simp [State.setReg, hr, hr']

theorem pushRegs_rest (s : State) (rs : List Reg) :
    (pushRegs s rs).cf = s.cf ∧ (pushRegs s rs).zf = s.zf ∧ (pushRegs s rs).sf = s.sf ∧
      (pushRegs s rs).of = s.of := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x xs ih => exact ih _

theorem popReg_rest (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).mem = s.mem ∧ (popReg s d k).cf = s.cf ∧ (popReg s d k).zf = s.zf ∧
      (popReg s d k).sf = s.sf ∧ (popReg s d k).of = s.of := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih => exact ih _

/-- `push r` for each of `rs` stores `rs[j]` at `esp - 4 (j + 1)`, and nothing
outside the `4 * rs.length` bytes below `esp`. -/
theorem pushRegs_mem (s : State) (rs : List Reg) (hrs : .esp ∉ rs)
    (hn : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    (∀ x, ¬ (Taint.belowSp s (4 * rs.length)).Contains x 1 → (pushRegs s rs).mem x = s.mem x) ∧
      ∀ j (hj : j < rs.length), (pushRegs s rs).mem.readW
        ((s.gpr .esp - BitVec.ofNat 32 (4 * (j + 1))).setWidth 64) 32 = s.gpr rs[j] := by
  induction rs generalizing s with
  | nil =>
    exact ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hrs
    simp only [List.length_cons] at hn ⊢
    have he := (s.gpr .esp).isLt
    let s₁ : State := { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) }
    have hs₁ : s₁ = { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) } := rfl
    have hsp₁ : s₁.gpr .esp = s.gpr .esp - 4 := by simp [hs₁, State.setReg]
    have hg₁ : ∀ r, r ≠ .esp → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
    have e₂ : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by show 4 ≤ _; omega))
    have e₁ : (s₁.gpr .esp).toNat = (s.gpr .esp).toNat - 4 := by rw [hsp₁, e₂]
    obtain ⟨ih₁, ih₂⟩ := ih s₁ hrs.2 (by omega)
    have hp : pushRegs s (x :: xs) = pushRegs s₁ xs := rfl
    have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    -- The bytes `xs` stores are below those of `x`.
    have hsub : ∀ y, (Taint.belowSp s₁ (4 * xs.length)).Contains y 1 →
        (Taint.belowSp s (4 * (xs.length + 1))).Contains y 1 ∧ ¬ (y - (s.gpr .esp - 4).setWidth 64).toNat < 4 := by
      intro y hy
      simp only [Taint.belowSp, Region.Contains, hsp₁] at hy ⊢
      rw [Taint.sub_setWidth (by omega)] at hy ⊢
      rw [show (s.gpr .esp - 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 from
        Taint.sub_setWidth (m := 4) (by omega)] at hy ⊢
      generalize (s.gpr .esp).setWidth 64 = E at *
      simp only [Offset.sub_sub_eq, Offset.toNat_add_ofNat] at hy ⊢
      have := (y - E).isLt
      omega
    refine ⟨fun y hy => ?_, fun j hj => ?_⟩
    · rw [hp, ih₁ y fun h => hy (hsub y h).1]
      apply Mem.write_apply
      intro hlt
      apply hy
      simp only [Taint.belowSp, Region.Contains]
      rw [Taint.sub_setWidth (by omega)]
      rw [show (s.gpr .esp - 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 from
        Taint.sub_setWidth (m := 4) (by omega)] at hlt
      generalize (s.gpr .esp).setWidth 64 = E at *
      simp only [Offset.sub_sub_eq, Offset.toNat_add_ofNat] at hlt ⊢
      have := (y - E).isLt
      omega
    · rw [hp]
      cases j with
      | zero =>
        simp only [Nat.zero_add, Nat.mul_one, List.getElem_cons_zero]
        rw [show (s.gpr .esp - BitVec.ofNat 32 4) = s.gpr .esp - 4 from rfl]
        rw [← Mem.readW_writeW_self32 s.mem ((s.gpr .esp - 4).setWidth 64) (s.gpr x)]
        refine Mem.readW_congr fun t ht => ih₁ _ fun h => (hsub _ h).2 ?_
        rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := ih₂ j (by simp at hj; omega)
        rw [hsp₁, hg₁ _ (fun h => hrs.2 (h ▸ List.getElem_mem _))] at this
        rw [show 4 * (j + 1 + 1) = 4 * (j + 1) + 4 by omega, BitVec.ofNat_add, BitVec.add_comm,
          ← BitVec.sub_sub]
        exact this


namespace Taint

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : callStep τ = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [callStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hp, hr⟩ := hp
  rw [call_callEntry, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have hsp := ha.reg hp
  have mem : ∀ {s : State}, Wf τ s → ∀ x,
      ((∃ r ∈ s.wr, r.Contains x 1) ∨ ∃ k < τ.argLen, x = argByte s (depth τ.stk + k)) →
      s.callEntry.mem x = s.mem x := by
    intro s hw x hx
    obtain ⟨-, hd, hz⟩ := hw.below (m := 4) (by omega) hr
    rw [State.callEntry_mem]
    apply Mem.write_apply
    intro hlt
    have hin : (belowSp s 4).Contains x 1 := by
      simp only [Region.Contains, belowSp]; exact Nat.succ_le_of_lt hlt
    rcases hx with ⟨r, hr', hc⟩ | ⟨k, hk, rfl⟩
    · exact hd r hr' _ hin hc
    · have := (hw.args (by omega)).1
      refine hz (by omega) _ hin ?_
      simp only [Region.Contains, argByte]
      rw [Offset.add_ofNat_add_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  have esp4 : ∀ {s : State}, Wf τ s → (s.callEntry.gpr .esp).toNat + 4 = (s.gpr .esp).toNat := by
    intro s hw
    have := (hw.below (m := 4) (by omega) hr).1
    rw [State.callEntry_esp, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      Offset.toNat_sub_ofNat]
    have := (s.gpr .esp).isLt
    omega
  have hf₁ := frames_call ha.wf₁ (s' := s₁.callEntry) rfl (esp4 ha.wf₁)
  have hf₂ := frames_call ha.wf₂ (s' := s₂.callEntry) rfl (esp4 ha.wf₂)
  refine ⟨by simp [hsp], ha.moveSp ⟨fun r hr' => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl rfl
    (by simp only [depth, itemSize]; have := esp4 ha.wf₁; omega)
    (by simp only [depth, itemSize]; have := esp4 ha.wf₂; omega) rfl rfl (mem ha.wf₁) (mem ha.wf₂)
    hf₁ hf₂ (fun p hp => ?_) (fun p hp => ?_) (fun _ => by simp only [State.callEntry_esp, hsp])⟩
  · by_cases h : r = .esp
    · subst h; simp only [State.callEntry_esp, hsp]
    · rw [State.callEntry_gpr _ h, State.callEntry_gpr _ h]; exact ha.rf.1 r hr'
  · rcases List.mem_append.mp hp with hp | hp
    · exact kill_bases (s' := s₁.callEntry) ha.wf₁ rfl (fun r h => State.callEntry_gpr _ h) p hp
    · exact stkBases_ok hf₁ p hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact kill_bases (s' := s₂.callEntry) ha.wf₂ rfl (fun r h => State.callEntry_gpr _ h) p hp
    · exact stkBases_ok hf₂ p hp

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : retStep τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  simp only [retStep] at hs
  split at hs <;> [rename_i stk hstk; cases hs]
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have hsp := ha.reg hp
  have esp4 : ∀ {s : State}, Wf τ s →
      ((s.setReg .esp (s.gpr .esp + 4)).gpr .esp).toNat = (s.gpr .esp).toNat + 4 := by
    intro s hw
    have := hw.stk
    rw [hstk] at this; simp only [depth, itemSize] at this
    simp only [State.setReg, ite_true]; bv_omega
  have hg : ∀ {s : State} (r : Reg), r ≠ .esp → (s.setReg .esp (s.gpr .esp + 4)).gpr r = s.gpr r :=
    fun r h => setReg_ne h
  have hf₁ := frames_ret hstk ha.wf₁ (s' := b₁.setReg .esp (b₁.gpr .esp + 4)) rfl (esp4 ha.wf₁)
  have hf₂ := frames_ret hstk ha.wf₂ (s' := b₂.setReg .esp (b₂.gpr .esp + 4)) rfl (esp4 ha.wf₂)
  refine ⟨by simp [hsp], ha.moveSp ⟨fun r hr' => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
    (by rw [hstk]; rfl) (by rw [esp4 ha.wf₁, hstk]; simp only [depth, itemSize]; omega)
    (by rw [esp4 ha.wf₂, hstk]; simp only [depth, itemSize]; omega) rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hf₁ hf₂ (fun p hp => ?_) (fun p hp => ?_)
    (fun _ => by simp only [State.setReg, ite_true, hsp])⟩
  · by_cases h : r = .esp
    · subst h; simp only [State.setReg, ite_true, hsp]
    · rw [hg r h, hg r h]; exact ha.rf.1 r hr'
  · rcases List.mem_append.mp hp with hp | hp
    · exact kill_bases (s' := b₁.setReg .esp (b₁.gpr .esp + 4)) ha.wf₁ rfl hg p hp
    · exact stkBases_ok hf₁ p hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact kill_bases (s' := b₂.setReg .esp (b₂.gpr .esp + 4)) ha.wf₂ rfl hg p hp
    · exact stkBases_ok hf₂ p hp

/-- A frame's pop removes the frame at `esp` (the first writable region) and
loads its register from it: a secret. -/
def popStep (τ : T) : Instr → Option T
  | .pop r _ =>
    match τ.stk with
    | some _ :: stk =>
      if pub τ .esp then
        some { τ with
          regs := τ.regs.erase r
          stk := stk
          lens := τ.lens.tail
          bases := ((τ.bases.filter fun p => p.1 != .esp && p.1 != r && p.2.1 != 0).map
            fun p => (p.1, p.2.1 - 1, p.2.2)) ++ stkBases stk
          slots := (τ.slots.filter (·.1 != 0)).map fun sl => (sl.1 - 1, sl.2)
          wbases := (τ.wbases.filter fun p => p.1 != 0 && p.2.2 != 0).map
            fun p => (p.1 - 1, p.2.1, p.2.2 - 1)
          argBases := (τ.argBases.filter (·.2 != 0)).map fun p => (p.1, p.2 - 1) }
      else none
    | _ => none
  | _ => none

theorem region_tail (s s' : State) (h : s'.wr = s.wr.tail) (i : Nat) :
    region s' i = region s (i + 1) := by
  simp only [region, h, List.getD_eq_getElem?_getD, List.getElem?_tail]

theorem Wf.pop {τ : T} {n : Nat} {stk : List (Option Nat)} (hstk : τ.stk = some n :: stk) {r : Reg}
    {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr.tail) (hm : s'.mem = s.mem)
    (hsp : (s'.gpr .esp).toNat = (s.gpr .esp).toNat + n)
    (hg : ∀ q, q ≠ .esp → q ≠ r → s'.gpr q = s.gpr q) :
    Wf { τ with
      regs := τ.regs.erase r
      stk := stk
      lens := τ.lens.tail
      bases := ((τ.bases.filter fun p => p.1 != .esp && p.1 != r && p.2.1 != 0).map
        fun p => (p.1, p.2.1 - 1, p.2.2)) ++ stkBases stk
      slots := (τ.slots.filter (·.1 != 0)).map fun sl => (sl.1 - 1, sl.2)
      wbases := (τ.wbases.filter fun p => p.1 != 0 && p.2.2 != 0).map
        fun p => (p.1 - 1, p.2.1, p.2.2 - 1)
      argBases := (τ.argBases.filter (·.2 != 0)).map fun p => (p.1, p.2 - 1) } s' := by
  have hE : (s'.gpr .esp).toNat + depth stk = (s.gpr .esp).toNat + depth τ.stk := by
    rw [hsp, hstk, depth, itemSize]; omega
  have hrt := region_tail s s' hwr
  have hframes : ∀ p ∈ frameList stk 0 0, s'.wr[p.1]? = some ⟨addr (s'.gpr .esp) p.2.1, p.2.2⟩ := by
    intro p hp
    have : (p.1 + 1, p.2.1 + n, p.2.2) ∈ frameList τ.stk 0 0 := by
      rw [hstk, frameList, frameList_shift]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, by simp⟩)
    have h := hw.frames _ this
    have e := addr_move (x := s.gpr .esp) (x' := s'.gpr .esp) (d := n) (d' := 0) (by omega) p.2.1
    simp only at h
    rw [hwr, List.getElem?_tail, h, Nat.zero_add] at *
    rw [e, Nat.add_comm]
  refine ⟨fun hne => ?_, fun p hp => ?_, fun p hp => ?_, fun hpos => ?_, fun p hp => ?_, ?_, hframes,
    fun hpos => ?_⟩
  · have hne' : τ.lens ≠ [] := fun h => hne (by simp [h])
    obtain ⟨h₁, h₂, h₃⟩ := hw.lens hne'
    refine ⟨by rw [hwr]; exact match s.wr, τ.lens, h₁ with | _, _, .nil => .nil | _, _, .cons _ h => h,
      by rw [hwr]; exact h₂.sublist (List.tail_sublist _),
      fun q hq => h₃ q (List.mem_of_mem_tail (hwr ▸ hq))⟩
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hq
      obtain ⟨hq, ⟨h₁, h₂⟩, h₃⟩ := hq
      simp only
      rw [hg _ h₁ h₂, hrt, Nat.sub_add_cancel (by omega)]
      exact hw.bases q hq
    · exact stkBases_ok hframes p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hq
    obtain ⟨hq, h₁, h₂⟩ := hq
    obtain ⟨hb, hv⟩ := hw.wbases q hq
    have hb' : q.2.1 + 4 ≤ τ.lens.tail.getD (q.1 - 1) 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_tail] at hb ⊢
      rw [Nat.sub_add_cancel (by omega)]; exact hb
    refine ⟨hb', ?_⟩
    simp only [byteAddr, hrt, hm, Nat.sub_add_cancel (Nat.pos_of_ne_zero h₁),
      Nat.sub_add_cancel (Nat.pos_of_ne_zero h₂)]
    exact hv
  · obtain ⟨h₁, h₂⟩ := hw.args hpos
    refine ⟨by simp only; omega, fun q hq => ?_⟩
    simp only
    rw [← Nat.add_zero (depth stk), argByte_move hE, Nat.add_zero]
    exact h₂ q (List.mem_of_mem_tail (hwr ▸ hq))
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
    obtain ⟨hq, h₁⟩ := hq
    obtain ⟨hb, hv⟩ := hw.argBases q hq
    refine ⟨hb, ?_⟩
    simp only
    rw [addr_move hE, hm, hrt, Nat.sub_add_cancel (Nat.pos_of_ne_zero h₁)]
    exact hv
  · simp only; rw [hE]; exact hw.stk
  · obtain ⟨h₁, h₂⟩ := hw.room hpos
    refine ⟨by simp only; omega, fun q hq => ?_⟩
    simp only
    rw [← Nat.add_zero (depth stk), argByte_move hE, Nat.add_zero]
    refine h₂ q ?_
    rw [hstk, nframes, ← List.drop_tail, ← hwr]
    exact hq

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : popStep τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [popStep, reduceCtorEq] at hs
  rename_i r k
  split at hs <;> [rename_i n stk hstk; cases hs]
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, X86.pop] at e₁ e₂
  split at e₁ <;> [rename_i hc₁; cases e₁]
  split at e₂ <;> [rename_i hc₂; cases e₂]
  cases e₁; cases e₂
  have hsp := ha.reg hp
  -- The frame the pop removes is the one at `esp`, of `n = 4 k` bytes.
  have hn : ∀ {a b : State}, Wf τ b → (k ≠ 0 ∧ r ≠ .esp ∧ b.gpr .esp = a.gpr .esp ∧ b.wr = a.wr ∧
      a.wr.head? = some ⟨(a.gpr .esp).setWidth 64, 4 * k⟩) → n = 4 * k := by
    intro a b hw hc
    have h := hw.frames (0, 0, n) (by rw [hstk]; exact List.mem_cons_self ..)
    rw [hc.2.2.2.1, ← List.head?_eq_getElem?, hc.2.2.2.2, ← hc.2.2.1] at h
    simp only [Option.some.injEq, Region.mk.injEq] at h
    exact h.2.symm
  have hn₁ := hn ha.wf₁ hc₁
  have hsp' : ∀ {a b : State}, Wf τ b → (k ≠ 0 ∧ r ≠ .esp ∧ b.gpr .esp = a.gpr .esp ∧ b.wr = a.wr ∧
      a.wr.head? = some ⟨(a.gpr .esp).setWidth 64, 4 * k⟩) →
      ((popReg b r k).gpr .esp).toNat = (b.gpr .esp).toNat + n := by
    intro a b hw hc
    have := hw.stk
    rw [hstk, depth, itemSize, hn hw hc] at this
    rw [(popReg_eq b r k).2.2.1, Offset.toNat_add_ofNat]
    omega
  have hg : ∀ {b : State} (q : Reg), q ≠ .esp → q ≠ r →
      ({ popReg b r k with wr := b.wr.tail } : State).gpr q = b.gpr q :=
    fun q h₁ h₂ => (popReg_eq _ r k).2.2.2 q h₁ h₂
  have w₁ := ha.wf₁.pop hstk (s' := { popReg b₁ r k with wr := b₁.wr.tail }) rfl (popReg_rest b₁ r k).1
    (hsp' ha.wf₁ hc₁) hg
  have w₂ := ha.wf₂.pop hstk (s' := { popReg b₂ r k with wr := b₂.wr.tail }) rfl (popReg_rest b₂ r k).1
    (hsp' ha.wf₂ hc₂) hg
  have hE : ∀ {b : State}, (({ popReg b r k with wr := b.wr.tail } : State).gpr .esp) =
      b.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq _ r k).2.2.1
  refine ⟨by simp [addrs, hsp], ⟨⟨fun q hq => ?_, fun hf => ?_⟩, fun hne => ?_, w₁, w₂, fun sl hsl => ?_,
    fun sl hsl t h₁ h₂ => ?_, fun _ => by rw [hE, hE, hsp], fun t h4 ht => ?_⟩⟩
  · simp only [RegSet.mem_erase] at hq
    by_cases h : q = .esp
    · subst h; rw [hE, hE, hsp]
    · rw [hg q h hq.1, hg q h hq.1]; exact ha.rf.1 q hq.2
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := popReg_rest b₁ r k |>.2
    obtain ⟨g₁, g₂, g₃, g₄⟩ := popReg_rest b₂ r k |>.2
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ha.rf.2 hf
    exact ⟨f₁.trans (h₁.trans g₁.symm), f₂.trans (h₂.trans g₂.symm), f₃.trans (h₃.trans g₃.symm),
      f₄.trans (h₄.trans g₄.symm)⟩
  · have hne' : τ.lens ≠ [] := fun h => hne (by simp [h])
    show b₁.wr.tail = b₂.wr.tail
    rw [ha.wr hne']
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsl
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
    have := ha.ok q hq.1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_tail] at this ⊢
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hq.2)]; exact this
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsl
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
    have e : ∀ b : State,
        byteAddr ({ popReg b r k with wr := b.wr.tail } : State) (q.1 - 1) t = byteAddr b q.1 t :=
      fun b => by
        simp only [byteAddr]; rw [region_tail b _ rfl, Nat.sub_add_cancel (Nat.pos_of_ne_zero hq.2)]
    show (popReg b₁ r k).mem (byteAddr _ (q.1 - 1) t) = (popReg b₂ r k).mem (byteAddr _ (q.1 - 1) t)
    rw [e, e, (popReg_rest _ r k).1, (popReg_rest _ r k).1]
    exact ha.slots q hq.1 t h₁ h₂
  · have e₁ : ((({ popReg b₁ r k with wr := b₁.wr.tail } : State).gpr .esp)).toNat + depth stk =
        (b₁.gpr .esp).toNat + depth τ.stk := by
      rw [hsp' ha.wf₁ hc₁, hstk, depth, itemSize]; omega
    have e₂ : ((({ popReg b₂ r k with wr := b₂.wr.tail } : State).gpr .esp)).toNat + depth stk =
        (b₂.gpr .esp).toNat + depth τ.stk := by
      rw [hsp' ha.wf₂ hc₂, hstk, depth, itemSize]; omega
    simp only at ht ⊢
    rw [argByte_move e₁, argByte_move e₂, (popReg_rest _ r k).1, (popReg_rest _ r k).1]
    exact ha.argMem t h4 ht

/-- The public slots of a frame's push `push rs`, the first register at `o - 4`. -/
def pushSlots (τ : T) : List Reg → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | r :: rs, o => (if pub τ r then [(0, o - 4, 4)] else []) ++ pushSlots τ rs (o - 4)

/-- The base-address words of a frame's push `push rs`, the first register at `o - 4`
(the other regions' indices move up by one). -/
def pushWbases (τ : T) : List Reg → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | r :: rs, o => (regBases τ r).map (fun i => (0, o - 4, i + 1)) ++ pushWbases τ rs (o - 4)

/-- The analysis after a frame's push `push rs`: the frame is writable region `0`
and the others move up by one. -/
def pushed (τ : T) (rs : List Reg) : T :=
  let n := 4 * rs.length
  { τ with
    stk := some n :: τ.stk
    lens := n :: τ.lens
    bases := (kill τ .esp).map (fun p => (p.1, p.2.1 + 1, p.2.2)) ++ stkBases (some n :: τ.stk)
    slots := pushSlots τ rs n ++ τ.slots.map fun sl => (sl.1 + 1, sl.2)
    wbases := pushWbases τ rs n ++ τ.wbases.map fun p => (p.1 + 1, p.2.1, p.2.2 + 1)
    argBases := τ.argBases.map fun p => (p.1, p.2 + 1) }

/-- A frame's push stores its registers below `esp`, within the bytes that the
stack may use, which become a new writable region. -/
def pushStep (τ : T) : Instr → Option T
  | .push rs =>
    if pub τ .esp && τ.lens != [] && decide (depth τ.stk + 4 * rs.length ≤ τ.room) then
      some (pushed τ rs)
    else none
  | _ => none

theorem pushSlots_mem {τ : T} {rs : List Reg} {o : Nat} {sl : Nat × Nat × Nat}
    (h : sl ∈ pushSlots τ rs o) :
    ∃ j, ∃ hj : j < rs.length, pub τ rs[j] = true ∧ sl = (0, o - 4 * (j + 1), 4) := by
  induction rs generalizing o with
  | nil => cases h
  | cons r rs ih =>
    simp only [pushSlots, List.mem_append] at h
    rcases h with h | h
    · split at h <;> [rename_i hp; cases h]
      simp only [List.mem_singleton] at h
      exact ⟨0, by simp, hp, by simp [h]⟩
    · obtain ⟨j, hj, hp, rfl⟩ := ih h
      exact ⟨j + 1, by simp; omega, hp, by simp; omega⟩

theorem pushWbases_mem {τ : T} {rs : List Reg} {o : Nat} {q : Nat × Nat × Nat}
    (h : q ∈ pushWbases τ rs o) :
    ∃ j, ∃ hj : j < rs.length, ∃ i ∈ regBases τ rs[j], q = (0, o - 4 * (j + 1), i + 1) := by
  induction rs generalizing o with
  | nil => cases h
  | cons r rs ih =>
    simp only [pushWbases, List.mem_append, List.mem_map] at h
    rcases h with ⟨i, hi, rfl⟩ | h
    · exact ⟨0, by simp, i, hi, by simp⟩
    · obtain ⟨j, hj, i, hi, rfl⟩ := ih h
      exact ⟨j + 1, by simp; omega, i, hi, by simp; omega⟩

theorem push_addr {e : BitVec 32} {n j i : Nat} (hn : n ≤ e.toNat) (hj : 4 * (j + 1) ≤ n) :
    (e - BitVec.ofNat 32 n).setWidth 64 + BitVec.ofNat 64 (n - 4 * (j + 1) + i) =
      (e - BitVec.ofNat 32 (4 * (j + 1))).setWidth 64 + BitVec.ofNat 64 i := by
  rw [sub_setWidth hn, sub_setWidth (by omega), BitVec.ofNat_add, ← Offset.ofNat_sub_ofNat hj,
    ← BitVec.add_assoc, Offset.sub_add_sub_cancel]

theorem region_cons (s s' : State) (f : Region) (h : s'.wr = f :: s.wr) (i : Nat) :
    region s' (i + 1) = region s i := by
  simp only [region, h, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

theorem byteAddr_cons (s s' : State) (f : Region) (h : s'.wr = f :: s.wr) (i k : Nat) :
    byteAddr s' (i + 1) k = byteAddr s i k := by
  simp only [byteAddr, region_cons s s' f h]

/-- The state after a frame's push. -/
abbrev pushState (s : State) (rs : List Reg) : State :=
  { pushRegs s rs with wr := belowSp s (4 * rs.length) :: s.wr }

theorem push_eq_pushState {rs : List Reg} {s s' : State} (h : isa.push (.push rs) s = some s') :
    rs ≠ [] ∧ .esp ∉ rs ∧ s' = pushState s rs := by
  simp only [isa, X86.push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨hc.1, hc.2.1, rfl⟩

section push
variable {τ : T} {rs : List Reg} {s : State} (hw : Wf τ s) (hrs : .esp ∉ rs) (hne : rs ≠ [])
  (hroom : depth τ.stk + 4 * rs.length ≤ τ.room)
include hw hrs hne hroom

theorem push_facts :
    4 * rs.length ≤ (s.gpr .esp).toNat ∧
    ((pushState s rs).gpr .esp).toNat + depth (pushed τ rs).stk = (s.gpr .esp).toNat + depth τ.stk ∧
    (∀ q, q ≠ .esp → (pushState s rs).gpr q = s.gpr q) ∧
    ∀ x, ((∃ r ∈ s.wr, r.Contains x 1) ∨ ∃ k < τ.argLen, x = argByte s (depth τ.stk + k)) →
      (pushState s rs).mem x = s.mem x := by
  have hn : 0 < 4 * rs.length := by
    cases rs with
    | nil => exact absurd rfl hne
    | cons => simp
  obtain ⟨hle, hd, hz⟩ := hw.below hn hroom
  obtain ⟨-, -, h₃, h₄⟩ := pushRegs_eq s rs
  refine ⟨hle, ?_, h₄, fun x hx => (pushRegs_mem s rs hrs hle).1 x fun hin => ?_⟩
  · show ((pushRegs s rs).gpr .esp).toNat + (4 * rs.length + depth τ.stk) = _
    rw [h₃, Offset.toNat_sub_ofNat]
    have := (s.gpr .esp).isLt
    omega
  · rcases hx with ⟨r, hr, hc⟩ | ⟨k, hk, rfl⟩
    · exact hd r hr _ hin hc
    · have := (hw.args (by omega)).1
      refine hz (by omega) _ hin ?_
      simp only [Region.Contains, argByte]
      rw [Offset.add_ofNat_add_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega

theorem Wf.push (hl : τ.lens ≠ []) : Wf (pushed τ rs) (pushState s rs) := by
  obtain ⟨hle, hE, hg, hkeep⟩ := push_facts hw hrs hne hroom
  have hn : 0 < 4 * rs.length := by
    cases rs with
    | nil => exact absurd rfl hne
    | cons => simp
  obtain ⟨-, hd, hz⟩ := hw.below hn hroom
  have hrc := region_cons s (pushState s rs) _ rfl
  have hesp : (pushState s rs).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) :=
    (pushRegs_eq s rs).2.2.1
  have hframes : ∀ p ∈ frameList (pushed τ rs).stk 0 0,
      (pushState s rs).wr[p.1]? = some ⟨addr ((pushState s rs).gpr .esp) p.2.1, p.2.2⟩ := by
    intro p hp
    simp only [pushed, frameList, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only [List.getElem?_cons_zero, Option.some.injEq, belowSp, addr]
      rw [show (pushState s rs).gpr .esp = (pushRegs s rs).gpr .esp from rfl, (pushRegs_eq s rs).2.2.1]
      congr 1; simp
    · rw [frameList_shift] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have e := addr_move (x := s.gpr .esp) (x' := (pushState s rs).gpr .esp) (d := 0)
        (d' := 4 * rs.length) (by rw [hesp, Offset.toNat_sub_ofNat]; have := (s.gpr .esp).isLt; omega) q.2.1
      simp only [List.getElem?_cons_succ, Nat.zero_add] at e ⊢
      rw [hw.frames q hq, Nat.add_comm q.2.1, e]
  refine ⟨fun _ => ?_, fun p hp => ?_, fun p hp => ?_, fun hpos => ?_, fun p hp => ?_, ?_, hframes,
    fun hpos => ?_⟩
  · obtain ⟨h₁, h₂, h₃⟩ := hw.lens hl
    refine ⟨.cons (by simp [belowSp]) h₁, List.pairwise_cons.mpr ⟨hd, h₂⟩, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [belowSp, sub_setWidth hle]
      have := (s.gpr .esp).isLt
      rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      · rw [Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat) (by omega), Nat.mod_eq_of_lt (a := 4 * rs.length) (by omega)]
        omega
    · exact h₃ r hr
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hq' := hq
      simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hq'
      simp only
      rw [hg _ hq'.2, hrc]
      exact hw.bases q hq'.1
    · exact stkBases_ok hframes p hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, hj, i, hi, rfl⟩ := pushWbases_mem hp
      refine ⟨by simp [pushed]; omega, ?_⟩
      rw [hrc]
      have h0 : byteAddr (pushState s rs) 0 (4 * rs.length - 4 * (j + 1)) =
          (s.gpr .esp - BitVec.ofNat 32 (4 * (j + 1))).setWidth 64 := by
        simp only [byteAddr, region, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
          Option.getD_some, belowSp]
        rw [← Nat.add_zero (4 * rs.length - 4 * (j + 1)), push_addr (j := j) (i := 0) hle (by omega),
          show BitVec.ofNat 64 0 = 0 from rfl]
        exact BitVec.add_zero _
      rw [h0]
      have := (pushRegs_mem s rs hrs hle).2 j hj
      show addr ((pushRegs s rs).mem.readW _ 32) 0 = _
      rw [this]
      simp only [regBases, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hi
      obtain ⟨q, ⟨hq, hr, h0⟩, rfl⟩ := hi
      have := hw.bases q hq
      rwa [hr, h0] at this
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hb, hv⟩ := hw.wbases q hq
      refine ⟨by simpa [pushed] using hb, ?_⟩
      simp only
      rw [byteAddr_cons s (pushState s rs) _ rfl, hrc, ← hv]
      refine congrArg (addr · 0) ?_
      refine Mem.readW_congr fun t ht => ?_
      rw [byteAddr_add]
      exact hkeep _ (.inl (hw.byte_mem (by omega)))
  · obtain ⟨h₁, h₂⟩ := hw.args hpos
    refine ⟨by simp only [pushed] at hE ⊢; omega, fun r hr => ?_⟩
    rw [← Nat.add_zero (depth _), argByte_move hE, Nat.add_zero]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hz hpos).symm
    · exact h₂ r hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hb, hv⟩ := hw.argBases q hq
    refine ⟨hb, ?_⟩
    simp only [hrc]
    rw [addr_move hE, ← hv]
    refine congrArg (addr · 0) ?_
    refine Mem.readW_congr fun t ht => ?_
    rw [argWord hw hb]
    exact hkeep _ (.inr ⟨q.1 + t, by omega, by rw [Nat.add_assoc]⟩)
  · rw [hE]; exact hw.stk
  · change 0 < τ.room at hpos
    obtain ⟨h₁, h₂⟩ := hw.room hpos
    refine ⟨by change τ.room ≤ _; omega, fun r hr => ?_⟩
    rw [← Nat.add_zero (depth _), argByte_move hE, Nat.add_zero]
    simp only [pushed, nframes, List.drop_succ_cons] at hr
    exact h₂ r hr

end push

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : pushStep τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [pushStep, reduceCtorEq] at hs
  rename_i rs
  split at hs <;> [rename_i hc; cases hs]
  cases hs
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hp, hl⟩, hroom⟩ := hc
  obtain ⟨hne, hrs, rfl⟩ := push_eq_pushState e₁
  obtain ⟨-, -, rfl⟩ := push_eq_pushState e₂
  have hsp := ha.reg hp
  obtain ⟨hle₁, hE₁, hg₁, hk₁⟩ := push_facts ha.wf₁ hrs hne hroom
  obtain ⟨hle₂, hE₂, hg₂, hk₂⟩ := push_facts ha.wf₂ hrs hne hroom
  have hesp : ∀ {s : State}, (pushState s rs).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) :=
    (pushRegs_eq _ rs).2.2.1
  have hrc₁ := region_cons s₁ (pushState s₁ rs) _ rfl
  have hrc₂ := region_cons s₂ (pushState s₂ rs) _ rfl
  refine ⟨by simp [addrs, hsp], ⟨⟨fun q hq => ?_, fun hf => ?_⟩, fun _ => ?_, ha.wf₁.push hrs hne hroom hl,
    ha.wf₂.push hrs hne hroom hl, fun sl hsl => ?_, fun sl hsl t h₁ h₂ => ?_,
    fun _ => by rw [hesp, hesp, hsp], fun t h4 ht => ?_⟩⟩
  · by_cases h : q = .esp
    · subst h; rw [hesp, hesp, hsp]
    · rw [hg₁ q h, hg₂ q h]; exact ha.rf.1 q hq
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := pushRegs_rest s₁ rs
    obtain ⟨g₁, g₂, g₃, g₄⟩ := pushRegs_rest s₂ rs
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ha.rf.2 hf
    exact ⟨f₁.trans (h₁.trans g₁.symm), f₂.trans (h₂.trans g₂.symm), f₃.trans (h₃.trans g₃.symm),
      f₄.trans (h₄.trans g₄.symm)⟩
  · show belowSp s₁ _ :: s₁.wr = belowSp s₂ _ :: s₂.wr
    simp only [belowSp, hsp, ha.wr hl]
  · rcases List.mem_append.mp hsl with hsl | hsl
    · obtain ⟨j, hj, -, rfl⟩ := pushSlots_mem hsl
      simp [pushed]; omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsl
      simpa [pushed] using ha.ok q hq
  · rcases List.mem_append.mp hsl with hsl | hsl
    · obtain ⟨j, hj, hpj, rfl⟩ := pushSlots_mem hsl
      simp only at h₁ h₂
      obtain ⟨i, hi, rfl⟩ : ∃ i < 4, t = 4 * rs.length - 4 * (j + 1) + i := ⟨t - (4 * rs.length - 4 * (j + 1)), by omega, by omega⟩
      simp only [byteAddr, region, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        belowSp]
      rw [push_addr (j := j) (i := i) hle₁ (by omega), push_addr (j := j) (i := i) hle₂ (by omega), hsp]
      show (pushRegs s₁ rs).mem _ = (pushRegs s₂ rs).mem _
      rw [Mem.readW_byte (pushRegs s₁ rs).mem _ hi, Mem.readW_byte (pushRegs s₂ rs).mem _ hi,
        ← hsp, (pushRegs_mem s₁ rs hrs hle₁).2 j hj, hsp, (pushRegs_mem s₂ rs hrs hle₂).2 j hj, ha.reg hpj]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsl
      have hk := ha.ok q hq
      simp only at h₁ h₂ ⊢
      rw [byteAddr_cons s₁ (pushState s₁ rs) _ rfl, byteAddr_cons s₂ (pushState s₂ rs) _ rfl,
        hk₁ _ (.inl (ha.wf₁.byte_mem (by omega))),
        hk₂ _ (.inl (ha.wf₂.byte_mem (by omega)))]
      exact ha.slots q hq t h₁ h₂
  · rw [argByte_move hE₁, argByte_move hE₂, hk₁ _ (.inr ⟨t, ht, rfl⟩), hk₂ _ (.inr ⟨t, ht, rfl⟩)]
    exact ha.argMem t h4 ht

/-! ## Evaluation by the kernel

The kernel evaluates `step` and `le` for every instruction and every hint of
a check (`VG.Taint.check`). `stepK` and `leK` are the same functions written
with the functions of `VG.KList`, which the kernel evaluates several times
faster. -/

open VG.KList (any all filter find? map append)

/-- `a == b`, by the registers' indices. -/
def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

theorem regEq_eq (a b : Reg) : regEq a b = (a == b) := by
  rw [regEq, KList.beq_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => RegIdx.idx_inj h, fun h => h ▸ rfl⟩

def killK (τ : T) (d : Reg) : List (Reg × Nat × Nat) := filter (fun p => !regEq p.1 d) τ.bases

def addrOfK (τ : T) (m : MemOp) : Option (Nat × Nat) :=
  (find? (fun p => regEq p.1 m.base && Nat.ble p.2.2 m.disp) τ.bases).map
    fun p => (p.2.1, m.disp - p.2.2)

def slotPubK (τ : T) (m : MemOp) (w : Nat) : Bool :=
  match addrOfK τ m with
  | some (i, d) =>
    any τ.slots fun sl => Nat.beq sl.1 i && Nat.ble sl.2.1 d && Nat.ble (d + w) (sl.2.1 + sl.2.2)
  | none => false

def argPubK (τ : T) (m : MemOp) (w : Nat) : Bool :=
  regEq m.base .esp && Nat.ble (depth τ.stk + 4) m.disp &&
    Nat.ble (m.disp + w) (depth τ.stk + τ.argLen)

def srcOkK (τ : T) : Src → Bool
  | .mem m => pub τ m.base
  | _ => true

def loadPubK (τ : T) : Src → Bool
  | .mem m => slotPubK τ m 4 || argPubK τ m 4
  | _ => false

def loadBasesK (τ : T) (m : MemOp) : List Nat :=
  append
    (match addrOfK τ m with
      | some (j, o) => map (·.2.2) (filter (fun p => Nat.beq p.1 j && Nat.beq p.2.1 o) τ.wbases)
      | none => [])
    (bif regEq m.base .esp then
      map (·.2) (filter (fun p => Nat.beq (depth τ.stk + p.1) m.disp) τ.argBases)
    else [])

def movBasesK (τ : T) (d : Reg) : Src → List (Reg × Nat × Nat)
  | .reg r => append (killK τ d) (map (fun p => (d, p.2)) (filter (fun p => regEq p.1 r) τ.bases))
  | .mem m => append (killK τ d) (map (fun i => (d, i, 0)) (loadBasesK τ m))
  | .imm _ => killK τ d

def regBasesK (τ : T) (r : Reg) : List Nat :=
  map (·.2.1) (filter (fun p => regEq p.1 r && Nat.beq p.2.2 0) τ.bases)

def storeSlotsK (τ : T) (m : MemOp) (w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ m with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      let kept := filter (fun sl => p || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d) τ.slots
      bif p then (i, d, w) :: kept else kept
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

def storeWbasesK (τ : T) (m : MemOp) (w : Nat) (nb : List Nat) : List (Nat × Nat × Nat) :=
  match addrOfK τ m with
  | some (j, d) =>
    bif Nat.ble (d + w) (τ.lens.getD j 0) then
      append (filter (fun p => !Nat.beq p.1 j || Nat.ble (d + w) p.2.1 || Nat.ble (p.2.1 + 4) d) τ.wbases)
        (map (fun i => (j, d, i)) nb)
    else []
  | none => []

def storeStepK (τ : T) (m : MemOp) (w : Nat) (p : Bool) (nb : List Nat) : Option T :=
  bif pub τ m.base then some { τ with slots := storeSlotsK τ m w p, wbases := storeWbasesK τ m w nb }
  else none

def setK (τ : T) (r : Reg) (p : Bool) : RegSet Reg := bif p then τ.regs.insert r else τ.regs.erase r

def stepK (τ : T) : Instr → Option T
  | .mov d src =>
    bif !regEq d .esp && srcOkK τ src then
      some { τ with regs := setK τ d (srcPub τ src || loadPubK τ src), bases := movBasesK τ d src }
    else none
  | .store m r => storeStepK τ m 4 (pub τ r) (regBasesK τ r)
  | .alu op d src =>
    bif !regEq d .esp && srcOkK τ src then
      let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
      some { τ with regs := bif writes op then setK τ d p else τ.regs, flags := p, bases := killK τ d }
    else none
  | .shift _ d _ =>
    bif !regEq d .esp then some { τ with flags := τ.flags && pub τ d, bases := killK τ d } else none
  | .bswap d => bif !regEq d .esp then some { τ with bases := killK τ d } else none
  | .movzx8 d m =>
    bif !regEq d .esp && pub τ m.base then some { τ with regs := setK τ d false, bases := killK τ d }
    else none
  | .store8 m r => storeStepK τ m 1 (pub τ r.reg) []
  | .mul r => some (mulStep τ r)
  | .push _ | .pop .. | .movdquLoad .. | .movdquStore .. | .xop _ => none

/-- `l.contains a`, for a known base address. -/
def memB (a : Reg × Nat × Nat) (l : List (Reg × Nat × Nat)) : Bool :=
  any l fun b => regEq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

/-- `l.contains a`, for a slot or a known base-address word. -/
def mem3 (a : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  any l fun b => Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

/-- `l.contains a`, for a known base address among the arguments. -/
def mem2 (a : Nat × Nat) (l : List (Nat × Nat)) : Bool :=
  any l fun b => Nat.beq a.1 b.1 && Nat.beq a.2 b.2

def leK (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    all τ.bases (memB · σ.bases) && all τ.slots (mem3 · σ.slots) && all τ.wbases (mem3 · σ.wbases) &&
    Nat.beq τ.argLen σ.argLen && all τ.argBases (mem2 · σ.argBases) && τ.stk == σ.stk &&
    Nat.ble τ.room σ.room

section
open KList

theorem killK_eq : killK = kill := by
  funext τ d; simp only [killK, kill, filter_eq, regEq_eq]; rfl

theorem setK_eq : setK = set := by
  funext τ r p; simp only [setK, set, Bool.cond_eq_ite]

theorem addrOfK_eq : addrOfK = addrOf := by
  funext τ m; simp only [addrOfK, addrOf, find?_eq, regEq_eq, ble_eq]

theorem slotPubK_eq : slotPubK = slotPub := by
  funext τ m w; simp only [slotPubK, slotPub, addrOfK_eq]
  rcases addrOf τ m with _ | ⟨i, d⟩ <;> simp only [any_eq, beq_eq, ble_eq]

theorem srcOkK_eq : srcOkK = srcOk := by
  funext τ src; cases src <;> rfl

theorem loadPubK_eq : loadPubK = loadPub := by
  funext τ src; cases src <;> simp only [loadPubK, loadPub, slotPubK_eq, argPubK, argPub, regEq_eq, ble_eq]

theorem loadBasesK_eq : loadBasesK = loadBases := by
  funext τ m; simp only [loadBasesK, loadBases, addrOfK_eq, append_eq, regEq_eq, Bool.cond_eq_ite]
  rcases addrOf τ m with _ | ⟨j, o⟩ <;> simp only [map_eq, filter_eq, beq_eq]

theorem movBasesK_eq : movBasesK = movBases := by
  funext τ d src
  cases src <;> simp only [movBasesK, movBases, killK_eq, append_eq, map_eq, filter_eq, regEq_eq, loadBasesK_eq]

theorem regBasesK_eq : regBasesK = regBases := by
  funext τ r; simp only [regBasesK, regBases, map_eq, filter_eq, regEq_eq, beq_eq]

theorem storeSlotsK_eq : storeSlotsK = storeSlots := by
  funext τ m w p; simp only [storeSlotsK, storeSlots, addrOfK_eq]
  rcases addrOf τ m with _ | ⟨i, d⟩ <;> simp only [filter_eq, beq_eq, ble_eq, Bool.cond_eq_ite, decide_eq_true_eq, bne]

theorem storeWbasesK_eq : storeWbasesK = storeWbases := by
  funext τ m w nb; simp only [storeWbasesK, storeWbases, addrOfK_eq]
  rcases addrOf τ m with _ | ⟨j, d⟩ <;> simp only [append_eq, map_eq, filter_eq, beq_eq, ble_eq, Bool.cond_eq_ite, decide_eq_true_eq, bne]

theorem storeStepK_eq : storeStepK = storeStep := by
  funext τ m w p nb; simp only [storeStepK, storeStep, storeSlotsK_eq, storeWbasesK_eq, Bool.cond_eq_ite, memPub]
  rfl

theorem stepK_eq : stepK = step := by
  funext τ i
  cases i <;> simp only [stepK, step, regEq_eq, bne, srcOkK_eq, setK_eq, loadPubK_eq, movBasesK_eq,
    killK_eq, storeStepK_eq, regBasesK_eq, Bool.cond_eq_ite, memPub]
  -- `movzx8`: the same up to the instance deciding the condition.
  rfl

theorem memB_eq (a : Reg × Nat × Nat) (l : List (Reg × Nat × Nat)) : memB a l = l.contains a := by
  simp only [memB, any_eq, beq_eq, regEq_eq, List.contains_eq_any_beq]
  congr; funext b; rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Prod.ext_iff, and_assoc]

theorem mem3_eq (a : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) : mem3 a l = l.contains a := by
  simp only [mem3, any_eq, beq_eq, List.contains_eq_any_beq]
  congr; funext b; rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Prod.ext_iff, and_assoc]

theorem mem2_eq (a : Nat × Nat) (l : List (Nat × Nat)) : mem2 a l = l.contains a := by
  simp only [mem2, any_eq, beq_eq, List.contains_eq_any_beq]
  rfl

theorem leK_eq : leK = le := by
  funext τ σ
  simp only [leK, le, memB_eq, mem3_eq, mem2_eq, all_eq, beq_eq, ble_eq]

end
end VG.X86.Taint

namespace VG.X86

/-- Taint tracking for x86 (32-bit). -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.stepK
  step_sound ha hs := Taint.step_sound ha (Taint.stepK_eq ▸ hs)
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.leK
  le_sound h := Taint.le_sound (Taint.leK_eq ▸ h)
  call := Taint.callStep
  call_sound := Taint.call_sound
  ret := Taint.retStep
  ret_sound := Taint.ret_sound
  push := Taint.pushStep
  push_sound := Taint.push_sound
  pop := Taint.popStep
  pop_sound := Taint.pop_sound

end VG.X86
