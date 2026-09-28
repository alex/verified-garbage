import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Exec
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
them sound in the presence of stores of secrets, the analysis knows the
lengths of the writable regions (`lens`, whose regions are then pairwise
disjoint, the same in both runs, and within the 32-bit address space) and
which registers point at a known offset before the base address of which
region (`bases`). A store through such a register can only change bytes of
its own region at the store's offset; any other store of a secret forgets
every slot.

With only seven usable registers, pointers also round-trip through memory:
`wbases` records which words of the writable regions hold the base address
of which region, so that a register loaded from one is known to point there.
Any store at an unknown address forgets them.

The first `argLen` bytes at `esp` (the return address, then the arguments of
code that may only read them) are outside every writable region, so no store
changes them, and at the same address in both runs; those from `esp + 4` on
(the arguments) are public, and `argBases` records which of their words are
the base address of a writable region. No instruction may write `esp`.
-/

namespace VG.X86.Taint

deriving instance Lean.ToExpr for Reg

structure T where
  regs : List Reg
  flags : Bool
  /-- The lengths of the writable regions `s.wr`, in order; `[]` if unknown. -/
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
  /-- `(o, i)`: the word at `esp + o` is the base address of writable region `i`. -/
  argBases : List (Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.contains r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The address of byte `k` above `esp`. -/
def argByte (s : State) (k : Nat) : Addr := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k

/-- The registers `regs` and, if `flags`, the flags are the same in both states. -/
def AgreeRF (regs : List Reg) (flags : Bool) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ regs, s₁.gpr r = s₂.gpr r) ∧
  (flags = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)

/-- What `τ` says about each state on its own. -/
structure Wf (τ : T) (s : State) : Prop where
  lens : τ.lens ≠ [] →
    s.wr.map Region.len = τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  bases : ∀ p ∈ τ.bases, addr (s.gpr p.1) p.2.2 = (region s p.2.1).base
  wbases : ∀ p ∈ τ.wbases, p.2.1 + 4 ≤ τ.lens.getD p.1 0 ∧
    addr (s.mem.readW (byteAddr s p.1 p.2.1) 32) 0 = (region s p.2.2).base
  args : 0 < τ.argLen →
    (s.gpr .esp).toNat + τ.argLen ≤ 2 ^ 32 ∧
      ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, τ.argLen⟩ r
  argBases : ∀ p ∈ τ.argBases, p.1 + 4 ≤ τ.argLen ∧
    addr (s.mem.readW (addr (s.gpr .esp) p.1) 32) 0 = (region s p.2).base

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
  argMem : ∀ k, 4 ≤ k → k < τ.argLen → s₁.mem (argByte s₁ k) = s₂.mem (argByte s₂ k)

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : List Reg :=
  if p then r :: τ.regs else τ.regs.filter (· != r)

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
  m.base == .esp && 4 ≤ m.disp && m.disp + w ≤ τ.argLen

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
  (if m.base == .esp then (τ.argBases.filter (·.1 == m.disp)).map (·.2) else [])

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

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.filter (pub τ₂)
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  wbases := if τ₁.lens = τ₂.lens then τ₁.wbases.filter (τ₂.wbases.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen then τ₁.argBases.filter (τ₂.argBases.contains ·) else []

def le (τ σ : T) : Bool :=
  τ.regs.all (pub σ) && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) &&
    τ.wbases.all (σ.wbases.contains ·) && τ.argLen == σ.argLen &&
    τ.argBases.all (σ.argBases.contains ·)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := by simp [pub]

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
  · simp only [hp, ite_true, List.mem_cons] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, List.mem_filter, bne_iff_ne, ne_eq] at hr
    simp [hr.2, h r hr.1]

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

theorem region_len {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) (i : Nat) :
    (region s i).len = τ.lens.getD i 0 := by
  rw [← (hw.lens hne).1]
  simp only [region, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.wr[i]? <;> rfl

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := (hw.lens hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hi' : i < s.wr.length := by rw [← hl, List.length_map] at this; exact this
  exact ⟨hi', by simp [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']⟩

/-- Region `i` lies within the 32-bit address space. -/
theorem region_bound {τ : T} {s : State} (hw : Wf τ s) {i : Nat} (hi : 0 < τ.lens.getD i 0) :
    (region s i).base.toNat + τ.lens.getD i 0 ≤ 2 ^ 32 := by
  have hne := lens_ne hi le_rfl
  obtain ⟨hi', hr⟩ := region_mem hw hne hi
  rw [← region_len hw hne i, hr]
  exact (hw.lens hne).2.2 _ (List.getElem_mem _)

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
  exact addr_offset (hw.bases _ hb) hk (by omega)

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

/-- The word at `esp + o`, byte by byte. -/
theorem argWord {τ : T} {s : State} (hw : Wf τ s) {o : Nat} (ho : o + 4 ≤ τ.argLen) (k : Nat) :
    addr (s.gpr .esp) o + BitVec.ofNat 64 k = argByte s (o + k) := by
  have := (hw.args (by omega)).1
  rw [addr_eq (by omega), argByte, BitVec.ofNat_add, BitVec.add_assoc]

/-- A load of a word from the stack arguments. -/
theorem Agree.readArg {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {m : MemOp}
    (hp : argPub τ m 4 = true) : s₁.mem.readW (s₁.ea m) 32 = s₂.mem.readW (s₂.ea m) 32 := by
  simp only [argPub, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨hb, h4⟩, ho⟩ := hp
  have hsp := ha.sp (by omega)
  show s₁.mem.readW (addr (s₁.gpr m.base) m.disp) 32 = s₂.mem.readW (addr (s₂.gpr m.base) m.disp) 32
  rw [hb, hsp]
  refine Mem.readW_congr fun k hk => ?_
  have := ha.argMem (m.disp + k) (by omega) (by omega)
  rwa [← argWord ha.wf₁ ho, ← argWord ha.wf₂ ho, hsp] at this

/-! ### Keeping what is known about memory -/

theorem Wf.keep {τ τ' : T} {s s' : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) (hsp : s'.gpr .esp = s.gpr .esp)
    (hb : ∀ p ∈ τ'.bases, addr (s'.gpr p.1) p.2.2 = (region s' p.2.1).base) : Wf τ' s' where
  lens h := by rw [hwr, hl]; exact hw.lens (hl ▸ h)
  bases := hb
  wbases p h := by
    rw [hl]
    simp only [byteAddr, region, hwr, hm]
    exact hw.wbases p (hwb ▸ h)
  args h := by rw [hwr, hsp, hargs]; exact hw.args (hargs ▸ h)
  argBases p h := by
    rw [hargs, hsp, hm]
    simp only [region, hwr]
    exact hw.argBases p (hab ▸ h)

theorem Agree.keep {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem)
    (hsp₁ : s₁'.gpr .esp = s₁.gpr .esp) (hsp₂ : s₂'.gpr .esp = s₂.gpr .esp)
    (hb₁ : ∀ p ∈ τ'.bases, addr (s₁'.gpr p.1) p.2.2 = (region s₁' p.2.1).base)
    (hb₂ : ∀ p ∈ τ'.bases, addr (s₂'.gpr p.1) p.2.2 = (region s₂' p.2.1).base) :
    Agree τ' s₁' s₂' where
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ha.wf₁.keep hl hwb hargs hab hw₁ hm₁ hsp₁ hb₁
  wf₂ := ha.wf₂.keep hl hwb hargs hab hw₂ hm₂ hsp₂ hb₂
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    simp only [byteAddr, region, hw₁, hw₂, hm₁, hm₂]
    exact ha.slots sl (hs ▸ h) k h₁ h₂
  sp h := by rw [hsp₁, hsp₂]; exact ha.sp (hargs ▸ h)
  argMem k h4 hk := by
    simp only [argByte, hsp₁, hsp₂, hm₁, hm₂]
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
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d := by
      simp only [byteAddr]; bv_omega
    rw [h, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega)] at hlt
    rcases hsep with hsep | hsep
    · rw [Nat.mod_eq_of_lt (by omega)] at hlt; omega
    · rw [show 2 ^ 64 - d + k = (k - d) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hlt
      omega
  · have hA : (region s i).Contains (byteAddr s i d) n := by
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
    s.mem.write A n V (argByte s k) = s.mem (argByte s k) := by
  obtain ⟨hsp, hd⟩ := hw.args (by omega)
  obtain ⟨r, hr, hc⟩ := hA
  apply Mem.write_apply
  intro hlt
  refine hd r hr _ ?_ (hc.byte hlt)
  simp only [Region.Contains, argByte]
  rw [show (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k - (s.gpr .esp).setWidth 64 = BitVec.ofNat 64 k by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
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
    · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨h, hsep⟩ := h
      obtain ⟨hq, hv⟩ := hw.wbases q h
      refine ⟨hq, ?_⟩
      show addr ((s.mem.write (s.ea m) n V).readW (byteAddr s q.1 q.2.1) 32) 0 = (region s q.2.2).base
      rw [e, readW_other hw hn hfit hq (by tauto) V]
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
    congr 1
    refine Mem.readW_congr fun k hk => ?_
    rw [argWord hw hq]
    exact write_arg hw hA V (by omega)

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
    show s₁.mem.write (s₁.ea m) n V₁ (argByte s₁ k) = s₂.mem.write (s₂.ea m) n V₂ (argByte s₂ k)
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
        · have hp : p = true := by split at hsl <;> simp_all
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
    ∀ r ∈ τ.regs.filter (· != d), s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hr
  rw [h₁ r hr.2, h₂ r hr.2, h r hr.1]

theorem not_pub_set {τ : T} {d : Reg} {p : Bool} (hp : ¬ p = true) :
    set τ d p = τ.regs.filter (· != d) := by
  simp [set, hp]

theorem setReg_gpr_eq (s : State) (d : Reg) (v : BitVec 32) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then v else s.gpr r := by
  simp only [State.setReg]

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
        simp only [setReg_gpr_eq, arithFlags_gpr]
        split
        · rfl
        · rename_i hrd
          simp only [set, hp, ite_true, List.mem_cons, hrd, false_or] at hr
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
        simp [setReg_gpr_eq, hr]
    · rename_i hw
      simp only [hw, Bool.false_eq_true, ite_false] at hr
      simpa using ha.1 r hr

/-! ### Instructions that write a register -/

/-- The register an instruction may write, if it writes one (stores do not). -/
def dst : Instr → Option Reg
  | .mov d _ | .alu _ d _ | .shift _ d _ | .bswap d | .movzx8 d _ => some d
  | .store .. | .store8 .. => none

theorem exec_dst {i : Instr} {d : Reg} (hd : dst i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.wr = s.wr ∧ s'.mem = s.mem ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i with
  | mov d' src =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact ⟨rfl, rfl, fun r h => setReg_ne h⟩
  | alu op d' src =>
    simp only [dst, Option.some.injEq] at hd; subst hd
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, -, out, -, rfl⟩ := h
    split <;> exact ⟨rfl, rfl, fun r h => by simp [setReg_gpr_eq, h]⟩
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

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dst i = some d) (hesp : d ≠ .esp)
    {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hwb : τ'.wbases = τ.wbases) (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) : Agree τ' s₁' s₂' := by
  obtain ⟨hw₁, hm₁, hg₁⟩ := exec_dst hd e₁
  obtain ⟨hw₂, hm₂, hg₂⟩ := exec_dst hd e₂
  exact ha.keep hrf hl hs hwb hargs hab hw₁ hw₂ hm₁ hm₂ (hg₁ _ (Ne.symm hesp)) (hg₂ _ (Ne.symm hesp))
    (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h)) (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h))

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
  refine ⟨le_rfl, ?_⟩
  rw [Mem.readW_writeW_self32]
  simp only [regBases, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hi
  obtain ⟨q, ⟨hq, hr, h0⟩, rfl⟩ := hi
  have := hw.bases q hq
  rwa [hr, h0] at this

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
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

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hzf, hcf]

/-! ### Meets -/

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s where
  lens hne := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.lens (he ▸ hne)
    · simp [meet, he] at hne
  bases p hp := h.bases p (List.mem_filter.mp hp).1
  wbases p hp := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hp ⊢; exact he ▸ h.wbases p (List.mem_filter.mp hp).1
    · simp [meet, he] at hp
  args hpos := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hpos ⊢; exact he ▸ h.args (he ▸ hpos)
    · simp [meet, he] at hpos
  argBases p hp := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hp ⊢; exact he ▸ h.argBases p (List.mem_filter.mp hp).1
    · simp [meet, he] at hp

theorem Wf.meet_right {τ₁ τ₂ : T} {s : State} (h : Wf τ₂ s) : Wf (meet τ₁ τ₂) s where
  lens hne := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hne ⊢; exact h.lens hne
    · simp [meet, he] at hne
  bases p hp := h.bases p (by simpa using (List.mem_filter.mp hp).2)
  wbases p hp := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hp ⊢; exact h.wbases p (by simpa using (List.mem_filter.mp hp).2)
    · simp [meet, he] at hp
  args hpos := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hpos ⊢; exact h.args hpos
    · simp [meet, he] at hpos
  argBases p hp := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hp ⊢; exact h.argBases p (by simpa using (List.mem_filter.mp hp).2)
    · simp [meet, he] at hp

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (List.mem_filter.mp hr).1,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.1)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [exact h.wr hne; exact absurd rfl hne]
  wf₁ := h.wf₁.meet_left
  wf₂ := h.wf₂.meet_left
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact he ▸ h.ok sl (List.mem_filter.mp hsl).1
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (List.mem_filter.mp hsl).1; cases hsl]
  sp hpos := by
    simp only [meet] at hpos
    split at hpos <;> [exact h.sp hpos; cases hpos]
  argMem k h4 hk := by
    simp only [meet] at hk
    split at hk <;> [exact h.argMem k h4 hk; cases hk]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (pub_iff.mp (List.mem_filter.mp hr).2),
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.2)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [rename_i he; exact absurd rfl hne]
    exact h.wr (he ▸ hne)
  wf₁ := h.wf₁.meet_right
  wf₂ := h.wf₂.meet_right
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact h.ok sl (by simpa using (List.mem_filter.mp hsl).2)
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (by simpa using (List.mem_filter.mp hsl).2); cases hsl]
  sp hpos := by
    simp only [meet] at hpos
    split at hpos <;> [rename_i he; cases hpos]
    exact h.sp (he ▸ hpos)
  argMem k h4 hk := by
    simp only [meet] at hk
    split at hk <;> [rename_i he; cases hk]
    exact h.argMem k h4 (he ▸ hk)

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hwb⟩, ha⟩, hab⟩ := hle
  refine ⟨⟨fun r h' => h.rf.1 r (pub_iff.mp (hr r h')), fun hf' => h.rf.2 ?_⟩, fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.lens (hl ▸ hne), fun p hp => h.wf₁.bases p (hb p hp),
      fun p hp => hl ▸ h.wf₁.wbases p (hwb p hp),
      fun hp => ha ▸ h.wf₁.args (ha ▸ hp), fun p hp => ha ▸ h.wf₁.argBases p (hab p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.lens (hl ▸ hne), fun p hp => h.wf₂.bases p (hb p hp),
      fun p hp => hl ▸ h.wf₂.wbases p (hwb p hp),
      fun hp => ha ▸ h.wf₂.args (ha ▸ hp), fun p hp => ha ▸ h.wf₂.argBases p (hab p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl),
    fun hp => h.sp (ha ▸ hp), fun k h4 hk => h.argMem k h4 (ha ▸ hk)⟩
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
    rw [addr_eq (by omega)]
    generalize esp.setWidth 64 = e at *
    bv_omega

/-- Byte `k` above `esp`, as byte `k % 4` of argument word `(k - 4) / 4`. -/
theorem argByte_eq {s : State} {n : Nat} (hfit : (s.gpr .esp).toNat + n ≤ 2 ^ 32) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    argByte s k = argAddr s ((k - 4) / 4) + BitVec.ofNat 64 ((k - 4) % 4) := by
  simp only [argByte, argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * ((k - 4) / 4))).setWidth 64 =
    addr (s.gpr .esp) (4 + 4 * ((k - 4) / 4)) from rfl, addr_eq (by omega), BitVec.add_assoc,
    ← BitVec.ofNat_add]
  congr 2; omega

end VG.X86.Taint

namespace VG.X86

/-- Taint tracking for x86 (32-bit). -/
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
  -- Not analysed yet: a call moves `esp`, relative to which the arguments are tracked.
  call _ := none
  call_sound _ h := by cases h
  ret _ := none
  ret_sound _ h := by cases h

end VG.X86
