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
secrets, the analysis knows lower bounds on the lengths of the writable
regions (`lens`, whose regions are then pairwise disjoint and the same in both
runs; a bound of `0` means the length is unknown and the region has no slots) and
which registers point at a known offset into which region (`bases`). A store
through such a register, at a known offset, can only change bytes of its own
region at that offset; any other store of a secret forgets every slot.

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
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order (one per region;
  `0` if unknown); `[]` if nothing is known about the regions. -/
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
    List.Forall₂ (fun r l => l ≤ r.len) s.wr τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧ ∀ r ∈ s.wr, r.len ≤ 2 ^ 64) ∧
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
non-negative immediate moves a pointer that far into its region, and a `sub`
moves it back (no further back than the region's base). -/
def aluBases (τ : T) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) : List (Reg × Nat × Nat) :=
  match op, src with
  | .add, .imm v =>
    if wide && !v.msb then kill τ d ++ (τ.bases.filter (·.1 == d)).map fun p => (d, p.2.1, p.2.2 + v.toNat)
    else kill τ d
  | .sub, .imm v =>
    if wide && !v.msb then
      kill τ d ++ (τ.bases.filter fun p => p.1 == d && v.toNat ≤ p.2.2).map fun p => (d, p.2.1, p.2.2 - v.toNat)
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
           flags := p, bases := (kill τ .rax).filter (·.1 != .rdx), lo := .empty }

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
  forall₂_getD (hw.1 hne).1 i

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := forall₂_length (hw.1 hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hi' : i < s.wr.length := hl ▸ this
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

end VG.X86_64.Taint
