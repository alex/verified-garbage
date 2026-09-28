import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.TCB.Arm.Target

/-!
# Taint tracking for ARMv7

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public, whether the
flags are public, and what is known about memory. Memory is secret unless
known otherwise: an address must be computed from public registers, and a
value loaded from memory is secret unless it comes from a *public slot* or
from the stack arguments.

As on x86-64 (`VG.X86_64.Taint`), public slots let public values survive a
round trip through memory, e.g. registers saved and restored by inlined
code. They are byte ranges of the writable regions `s.wr` (identified by
index) that hold the same bytes in both runs. To keep them sound in the
presence of stores of secrets, the analysis knows the lengths of the writable
regions (`lens`, whose regions are then pairwise disjoint, the same in both
runs, and within the 32-bit address space) and which registers hold the base
address of which region (`bases`). A store through such a register can only
change bytes of its own region at the store's offset; any other store of a
secret forgets every slot.

The first `args` bytes at `sp` (the stack arguments) are public, the same
address in both runs, and outside every writable region, so no store changes
them; `argBases` records which of those words are the base address of a
writable region.
-/

namespace VG.Arm.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- The lengths of the writable regions `s.wr`, in order; `[]` if unknown. -/
  lens : List Nat := []
  /-- `(r, i)`: register `r` holds the base address of writable region `i`. -/
  bases : List (Reg × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  /-- The first `args` bytes at `sp` are public and never written. -/
  argLen : Nat := 0
  /-- `(o, i)`: the stack word at `sp + o` is the base address of writable region `i`. -/
  argBases : List (Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The address of byte `k` of the stack arguments. -/
def argByte (s : State) (k : Nat) : Addr := State.addr s.sp + BitVec.ofNat 64 k

/-- The registers `regs` and, if `flags`, the flags are the same in both states. -/
def AgreeRF (regs : RegSet Reg) (flags : Bool) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ regs, s₁.gpr r = s₂.gpr r) ∧
  (flags = true → s₁.n = s₂.n ∧ s₁.z = s₂.z ∧ s₁.c = s₂.c ∧ s₁.v = s₂.v)

/-- What `τ` says about each state on its own. -/
structure Wf (τ : T) (s : State) : Prop where
  lens : τ.lens ≠ [] →
    s.wr.map Region.len = τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  bases : ∀ p ∈ τ.bases, State.addr (s.gpr p.1) = (region s p.2).base
  args : 0 < τ.argLen →
    s.sp.toNat + τ.argLen ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, τ.argLen⟩ r
  argBases : ∀ p ∈ τ.argBases, p.1 + 4 ≤ τ.argLen ∧
    State.addr (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 p.1)) 32) = (region s p.2).base

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
  sp : 0 < τ.argLen → s₁.sp = s₂.sp
  argMem : ∀ k < τ.argLen, s₁.mem (argByte s₁ k) = s₂.mem (argByte s₂ k)

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat) := τ.bases.filter (·.1 != d)

def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r | .shifted r _ _ => pub τ r

/-- The region and offset addressed by `[n, #off]`, if known. -/
def addrOf (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (τ.bases.find? (·.1 == n)).map fun p => (p.2, off)

/-- `w` bytes at `[n, #off]` are within a public slot. -/
def slotPub (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOf τ n off with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

/-- The known region bases after `mov d, op2`. -/
def movBases (τ : T) (d : Reg) : Op2 → List (Reg × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | _ => kill τ d

/-- The public slots after storing `w` bytes at `[n, #off]`, a public value iff `p`. -/
def storeSlots (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ n off with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

/-- The known region bases after `ldr t, [sp, #off]`. -/
def spBases (τ : T) (t : Reg) (off : Nat) : List (Reg × Nat) :=
  kill τ t ++ (τ.argBases.filter fun p => p.1 == off).map fun p => (t, p.2)

def storeStep (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  if pub τ n then some { τ with slots := storeSlots τ n off w p } else none

def step (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := set τ d (op2Pub τ op2), bases := movBases τ d op2 }
  | .dp _ d n op2 => some { τ with regs := set τ d (pub τ n && op2Pub τ op2), bases := kill τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := set τ d p, flags := p, bases := kill τ d }
  | .adc d n op2 =>
    some { τ with regs := set τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := kill τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := set τ d true, bases := kill τ d }
  | .movt d _ => some { τ with regs := set τ d (pub τ d), bases := kill τ d }
  | .rev d m => some { τ with regs := set τ d (pub τ m), bases := kill τ d }
  | .ldr t n off =>
    if pub τ n then some { τ with regs := set τ t (slotPub τ n off 4), bases := kill τ t } else none
  | .str t n off => storeStep τ n off 4 (pub τ t)
  | .ldrb t n _ => if pub τ n then some { τ with regs := set τ t false, bases := kill τ t } else none
  | .strb t n off => storeStep τ n off 1 (pub τ t)
  | .ldrSp t off =>
    if off + 4 ≤ τ.argLen then some { τ with regs := set τ t true, bases := spBases τ t off } else none
  -- Frames are not analysed yet.
  | .push _ | .pop .. => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen then τ₁.argBases.filter (τ₂.argBases.contains ·) else []

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) && τ.argLen == σ.argLen &&
    τ.argBases.all (σ.argBases.contains ·)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := Iff.rfl

section
variable {τ : T} {s₁ s₂ : State}

theorem Agree.reg (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) : s₁.gpr r = s₂.gpr r :=
  h.rf.1 r (pub_iff.mp hr)

theorem Agree.op2 (h : Agree τ s₁ s₂) {o : Op2} (ho : op2Pub τ o = true) : o.eval s₁ = o.eval s₂ := by
  cases o with
  | imm v => rfl
  | reg r => simp only [Op2.eval, h.reg ho]
  | shifted r sh n => simp only [Op2.eval, h.reg ho]

theorem op2_some (h : Agree τ s₁ s₂) {o : Op2} {y₁ y₂ : BitVec 32}
    (e₁ : o.eval s₁ = some y₁) (e₂ : o.eval s₂ = some y₂) : op2Pub τ o = true → y₁ = y₂ :=
  fun ho => by rw [h.op2 ho, e₂] at e₁; cases e₁; rfl

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

/-! ### Keeping what is known about memory -/

theorem Wf.keep {τ τ' : T} {s s' : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases) (hwr : s'.wr = s.wr)
    (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hb : ∀ p ∈ τ'.bases, State.addr (s'.gpr p.1) = (region s' p.2).base) : Wf τ' s' where
  lens h := by rw [hwr, hl]; exact hw.lens (hl ▸ h)
  bases := hb
  args h := by rw [hwr, hsp, hargs]; exact hw.args (hargs ▸ h)
  argBases p h := by
    rw [hargs, hsp, hm]
    simp only [region, hwr]
    exact hw.argBases p (hab ▸ h)

theorem Agree.keep {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem)
    (hsp₁ : s₁'.sp = s₁.sp) (hsp₂ : s₂'.sp = s₂.sp)
    (hb₁ : ∀ p ∈ τ'.bases, State.addr (s₁'.gpr p.1) = (region s₁' p.2).base)
    (hb₂ : ∀ p ∈ τ'.bases, State.addr (s₂'.gpr p.1) = (region s₂' p.2).base) : Agree τ' s₁' s₂' where
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ha.wf₁.keep hl hargs hab hw₁ hm₁ hsp₁ hb₁
  wf₂ := ha.wf₂.keep hl hargs hab hw₂ hm₂ hsp₂ hb₂
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    simp only [byteAddr, region, hw₁, hw₂, hm₁, hm₂]
    exact ha.slots sl (hs ▸ h) k h₁ h₂
  sp h := by rw [hsp₁, hsp₂]; exact ha.sp (hargs ▸ h)
  argMem k hk := by
    simp only [argByte, hsp₁, hsp₂, hm₁, hm₂]
    exact ha.argMem k (hargs ▸ hk)

theorem kill_bases {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr) {d : Reg}
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) :
    ∀ p ∈ kill τ d, State.addr (s'.gpr p.1) = (region s' p.2).base := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [hg _ hp.2, hw.bases p hp.1]
  simp [region, hwr]

theorem kill_setReg {τ : T} {s : State} (hw : Wf τ s) (d : Reg) (v : BitVec 32) :
    ∀ p ∈ kill τ d, State.addr ((s.setReg d v).gpr p.1) = (region (s.setReg d v) p.2).base :=
  kill_bases (s' := s.setReg d v) hw rfl fun _ h => setReg_ne h

theorem movBases_ok {τ : T} {s : State} (hw : Wf τ s) {d : Reg} {o : Op2} {v : BitVec 32}
    (hv : o.eval s = some v) :
    ∀ p ∈ movBases τ d o, State.addr ((s.setReg d v).gpr p.1) = (region (s.setReg d v) p.2).base := by
  cases o with
  | reg r =>
    simp only [Op2.eval, Option.some.injEq] at hv
    subst hv
    intro p hp
    simp only [movBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    rcases hp with hp | ⟨q, ⟨hq, rfl⟩, rfl⟩
    · exact kill_setReg hw d _ p hp
    · simp only [State.setReg, ite_true]
      exact hw.bases q hq
  | imm _ => exact kill_setReg hw d _
  | shifted _ _ _ => exact kill_setReg hw d _

/-! ### Region addresses -/

theorem addrOf_some {τ : T} {n : Reg} {off i d : Nat} (h : addrOf τ n off = some (i, d)) :
    (n, i) ∈ τ.bases ∧ off = d := by
  unfold addrOf at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hq
  have hb := List.find?_some hq
  simp only [beq_iff_eq] at hb
  exact ⟨by rw [← hb]; exact hm, rfl⟩

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

theorem ea_of_addrOf {τ : T} {s : State} (hw : Wf τ s) {n : Reg} {off i d : Nat}
    (h : addrOf τ n off = some (i, d)) (hd : d < τ.lens.getD i 0) :
    State.addr (s.gpr n + BitVec.ofNat 32 off) = byteAddr s i d := by
  obtain ⟨hb, rfl⟩ := addrOf_some h
  have hbd := region_bound hw (i := i) (by omega)
  have e := hw.bases _ hb
  simp only at e
  have hn : (s.gpr n).toNat = (region s i).base.toNat := by
    rw [← e, State.addr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (s.gpr n).isLt; omega)]
  rw [addr_add (by omega), e]
  rfl

theorem byteAddr_add (s : State) (i d k : Nat) :
    byteAddr s i d + BitVec.ofNat 64 k = byteAddr s i (d + k) := by
  simp only [byteAddr, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

/-- Slots live in regions of the same address in both runs. -/
theorem Agree.byteAddr_eq {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {sl : Nat × Nat × Nat}
    (h : sl ∈ τ.slots) {k : Nat} (hk : k < sl.2.1 + sl.2.2) :
    byteAddr s₁ sl.1 k = byteAddr s₂ sl.1 k := by
  have := ha.ok sl h
  simp only [byteAddr, region, ha.wr (lens_ne (n := sl.2.1 + sl.2.2) (by omega) this)]

/-- A load of a word from a public slot. -/
theorem Agree.readW {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} {off : Nat}
    (hp : slotPub τ n off 4 = true) :
    s₁.mem.readW (State.addr (s₁.gpr n + BitVec.ofNat 32 off)) 32 =
      s₂.mem.readW (State.addr (s₂.gpr n + BitVec.ofNat 32 off)) 32 := by
  unfold slotPub at hp
  split at hp <;> [skip; cases hp]
  rename_i i d h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨sl, hsl, ⟨rfl, ho⟩, hd⟩ := hp
  have hok := ha.ok sl hsl
  rw [ea_of_addrOf ha.wf₁ h (by omega), ea_of_addrOf ha.wf₂ h (by omega),
    ha.byteAddr_eq hsl (k := d) (by omega)]
  refine Mem.readW_congr fun k hk => ?_
  rw [byteAddr_add]
  have := ha.slots sl hsl (d + k) (by omega) (by omega)
  rwa [ha.byteAddr_eq hsl (k := d + k) (by omega)] at this

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

theorem storeSlots_ok {τ : T} (hok : SlotsOk τ) (n : Reg) (off w : Nat) (p : Bool) :
    SlotsOk { τ with slots := storeSlots τ n off w p } := by
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
    (V : BitVec (8 * n)) {k : Nat} (hk : k < τ.argLen) : s.mem.write A n V (argByte s k) = s.mem (argByte s k) := by
  obtain ⟨hsp, hd⟩ := hw.args (by omega)
  obtain ⟨r, hr, hc⟩ := hA
  apply Mem.write_apply
  intro hlt
  refine hd r hr _ ?_ (hc.byte hlt)
  simp only [Region.Contains, argByte]
  rw [show State.addr s.sp + BitVec.ofNat 64 k - State.addr s.sp = BitVec.ofNat 64 k by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack argument word at offset `o`, byte by byte. -/
theorem argWord {τ : T} {s : State} (hw : Wf τ s) {o : Nat} (ho : o + 4 ≤ τ.argLen) (k : Nat) :
    State.addr (s.sp + BitVec.ofNat 32 o) + BitVec.ofNat 64 k = argByte s (o + k) := by
  have := (hw.args (by omega)).1
  rw [addr_add (by omega), argByte, BitVec.ofNat_add, BitVec.add_assoc]

theorem Wf.store {τ : T} {s : State} (hw : Wf τ s) {A : Addr} {n : Nat} (hA : InRegions s.wr A n)
    (V : BitVec (8 * n)) (τ' : T) (hl : τ'.lens = τ.lens) (hb : τ'.bases = τ.bases)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases) :
    Wf τ' { s with mem := s.mem.write A n V } where
  lens h := hl ▸ hw.lens (hl ▸ h)
  bases p h := hw.bases p (hb ▸ h)
  args h := hargs ▸ hw.args (hargs ▸ h)
  argBases p h := by
    obtain ⟨hp, he⟩ := hw.argBases p (hab ▸ h)
    rw [hargs]
    refine ⟨hp, ?_⟩
    simp only [region] at he ⊢
    rw [← he]
    congr 1
    refine Mem.readW_congr fun k hk => ?_
    rw [argWord hw hp]
    exact write_arg hw hA V (by omega)

/-- A store of `n` bytes at `[r, #off]`, of the same value in both runs if `p`. -/
theorem Agree.store {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {r : Reg} {off : Nat}
    (hr : pub τ r = true) {n : Nat} (hn : 0 < n) {V₁ V₂ : BitVec (8 * n)} {p : Bool}
    (hv : p = true → V₁ = V₂)
    (hA₁ : InRegions s₁.wr (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n)
    (hA₂ : InRegions s₂.wr (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n) :
    Agree { τ with slots := storeSlots τ r off n p }
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n V₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁.store hA₁ V₁ _ rfl rfl rfl rfl
  wf₂ := ha.wf₂.store hA₂ V₂ _ rfl rfl rfl rfl
  ok := storeSlots_ok ha.ok r off n p
  sp := ha.sp
  argMem k hk := by
    simp only [argByte] at *
    rw [show State.addr s₁.sp + BitVec.ofNat 64 k = argByte s₁ k from rfl,
      show State.addr s₂.sp + BitVec.ofNat 64 k = argByte s₂ k from rfl,
      write_arg ha.wf₁ hA₁ V₁ hk, write_arg ha.wf₂ hA₂ V₂ hk]
    exact ha.argMem k hk
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr]
    have hA : s₁.gpr r = s₂.gpr r := ha.reg hr
    have same : sl ∈ τ.slots → p = true →
        s₁.mem.write (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n V₁ (byteAddr s₁ sl.1 k) =
          s₂.mem.write (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n V₂ (byteAddr s₂ sl.1 k) :=
      fun h hp => by
        rw [hA, hv hp, ha.byteAddr_eq h hk₂]
        exact write_same _ (ha.byteAddr_eq h hk₂ ▸ ha.slots sl h k hk₁ hk₂)
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

/-! ### Instructions that write a register -/

/-- The register an instruction writes, if it writes one (`cmp` and stores
do not; a frame's pop writes its register). -/
def dst : Instr → Option Reg
  | .mov d _ | .dp _ d _ _ | .adds d _ _ | .adc d _ _ | .subs d _ _ | .movw d _ | .movt d _ | .rev d _
  | .ldr d _ _ | .ldrb d _ _ | .ldrSp d _ | .pop d _ => some d
  | .cmp .. | .str .. | .strb .. | .push _ => none

theorem exec_dst {i : Instr} {d : Reg} (hd : dst i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i <;> simp only [dst, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;>
  simp only [exec, Option.map_eq_some_iff, State.load32, State.load8] at h <;>
  (repeat' split at h) <;>
  (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
  first
  | (subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩)
  | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => by simp [State.setReg, addFlags, subFlags, h]⟩)
  | (cases h)

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dst i = some d) {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) : Agree τ' s₁' s₂' := by
  obtain ⟨hw₁, hm₁, hsp₁, hg₁⟩ := exec_dst hd e₁
  obtain ⟨hw₂, hm₂, hsp₂, hg₂⟩ := exec_dst hd e₂
  exact ha.keep hrf hl hs hargs hab hw₁ hw₂ hm₁ hm₂ hsp₁ hsp₂
    (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h)) (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h))

theorem setReg_flags (s : State) (d : Reg) (x : BitVec 32) :
    (s.setReg d x).n = s.n ∧ (s.setReg d x).z = s.z ∧ (s.setReg d x).c = s.c ∧ (s.setReg d x).v = s.v :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem spBases_ok {τ : T} {s : State} (hw : Wf τ s) {t : Reg} {off : Nat} :
    ∀ p ∈ spBases τ t off, State.addr ((s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)).gpr p.1) =
      (region (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) p.2).base := by
  intro p hp
  simp only [spBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
  rcases hp with hp | ⟨q, ⟨hq, hqo⟩, rfl⟩
  · exact kill_setReg hw t _ p hp
  · have := (hw.argBases q hq).2
    rw [hqo] at this
    simp only [State.setReg, ite_true, region] at this ⊢
    exact this

theorem ldrSp_sound {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {t : Reg} {off : Nat}
    (ho : off + 4 ≤ τ.argLen) :
    Agree { τ with regs := set τ t true, bases := spBases τ t off }
      (s₁.setReg t (s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 off)) 32))
      (s₂.setReg t (s₂.mem.readW (State.addr (s₂.sp + BitVec.ofNat 32 off)) 32)) := by
  have hsp := ha.sp (by omega)
  have hv : s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 off)) 32 =
      s₂.mem.readW (State.addr (s₂.sp + BitVec.ofNat 32 off)) 32 := by
    rw [hsp]
    refine Mem.readW_congr fun k hk => ?_
    have := ha.argMem (off + k) (by omega)
    simp only [argByte, hsp] at this
    rw [argWord ha.wf₂ ho]
    exact this
  exact ha.keep ⟨regs_set (d := t) (p := true) ha.rf.1 fun _ => hv, fun hf => ha.rf.2 hf⟩ rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (spBases_ok ha.wf₁) (spBases_ok ha.wf₂)

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop => simp only [step, reduceCtorEq] at hs
  | mov d o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    exact ⟨rfl, ha.keep ⟨regs_set ha.rf.1 (op2_some ha h₁ h₂), fun hf => ha.rf.2 hf⟩ rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl (movBases_ok ha.wf₁ h₁) (movBases_ok ha.wf₂ h₂)⟩
  | dp op d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
  | adds d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set (fun r hr => by simpa [addFlags] using ha.rf.1 r hr) fun hp => ?_, fun hp => ?_⟩ <;>
    · simp only [Bool.and_eq_true] at hp
      rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
      try simp [addFlags, State.setReg]
  | adc d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.1.2, ha.reg hp.1.1, (ha.rf.2 hp.2).2.2.1]
  | subs d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set (fun r hr => by simpa [subFlags] using ha.rf.1 r hr) fun hp => ?_, fun hp => ?_⟩ <;>
    · simp only [Bool.and_eq_true] at hp
      rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
      try simp [subFlags, State.setReg]
  | cmp n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨rfl, ha.keep ⟨fun r hr => by simpa [subFlags] using ha.rf.1 r hr, fun hp => ?_⟩ rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl (fun p h => by simpa [subFlags, region] using ha.wf₁.bases p h)
      (fun p h => by simpa [subFlags, region] using ha.wf₂.bases p h)⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
    simp [subFlags]
  | movw d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set (d := d) (p := true) ha.rf.1 fun _ => rfl, fun hf => ha.rf.2 hf⟩
  | movt d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set ha.rf.1 fun hp => by rw [ha.reg hp], fun hf => ha.rf.2 hf⟩
  | rev d m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set ha.rf.1 fun hp => by rw [ha.reg hp], fun hf => ha.rf.2 hf⟩
  | ldr t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ha.readW hp
  | str t n off =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 4) hn (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
  | ldrb t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, -, rfl⟩ := e₁; obtain ⟨x₂, -, rfl⟩ := e₂
    exact ⟨regs_set (p := false) ha.rf.1 (fun h => by cases h), fun hf => ha.rf.2 hf⟩
  | strb t n off =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 1) hn (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
  | ldrSp t off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i ho; cases hs
    have hsp := ha.sp (by omega)
    refine ⟨by simp only [addrs, hsp], ?_⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ldrSp_sound ha ho

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨-, hz, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hz]

/-! ### Meets -/

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s where
  lens hne := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.lens (he ▸ hne)
    · simp [meet, he] at hne
  bases p hp := h.bases p (List.mem_filter.mp hp).1
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
  args hpos := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hpos ⊢; exact h.args hpos
    · simp [meet, he] at hpos
  argBases p hp := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hp ⊢; exact h.argBases p (by simpa using (List.mem_filter.mp hp).2)
    · simp [meet, he] at hp

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).1,
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
  argMem k hk := by
    simp only [meet] at hk
    split at hk <;> [exact h.argMem k hk; cases hk]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).2,
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
  argMem k hk := by
    simp only [meet] at hk
    split at hk <;> [rename_i he; cases hk]
    exact h.argMem k (he ▸ hk)

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩ := hle
  refine ⟨⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hr h'), fun hf' => h.rf.2 ?_⟩, fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.lens (hl ▸ hne), fun p hp => h.wf₁.bases p (hb p hp),
      fun hp => ha ▸ h.wf₁.args (ha ▸ hp), fun p hp => ha ▸ h.wf₁.argBases p (hab p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.lens (hl ▸ hne), fun p hp => h.wf₂.bases p (hb p hp),
      fun hp => ha ▸ h.wf₂.args (ha ▸ hp), fun p hp => ha ▸ h.wf₂.argBases p (hab p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl),
    fun hp => h.sp (ha ▸ hp), fun k hk => h.argMem k (ha ▸ hk)⟩
  rcases hf with hf | hf
  · simp [hf'] at hf
  · exact hf

end VG.Arm.Taint

namespace VG.Arm

namespace Taint

/-- Whether a call leaves `r` unchanged (all but `lr` and `r12`). -/
def callKeeps (r : Reg) : Bool := r != .lr && r != .r12

/-- A call leaves unknown values in `lr` and `r12`. -/
def callStep (τ : T) : T :=
  { τ with regs := (τ.regs.erase .lr).erase .r12, bases := τ.bases.filter (callKeeps ·.1) }

theorem call_gpr {s s' : State} (e : isa.call s = some s') {r : Reg} (h : callKeeps r = true) :
    s'.gpr r = s.gpr r := by
  simp only [callKeeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [isa, call, Option.some.injEq] at e; subst e
  simp [State.setReg, h.1, h.2]

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : some (callStep τ) = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  cases hs
  have hr₁ := e₁; have hr₂ := e₂
  simp only [isa, call, Option.some.injEq] at hr₁ hr₂
  subst hr₁ hr₂
  refine ⟨rfl, ha.keep ⟨fun r hr => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun p hp => ?_) (fun p hp => ?_)⟩
  · simp only [callStep, RegSet.mem_erase] at hr
    obtain ⟨h12, hlr, hr⟩ := hr
    have hk : callKeeps r = true := by simp [callKeeps, hlr, h12]
    rw [call_gpr e₁ hk, call_gpr e₂ hk]; exact ha.rf.1 r hr
  · simp only [callStep, List.mem_filter] at hp
    rw [call_gpr e₁ hp.2]; exact ha.wf₁.bases p hp.1
  · simp only [callStep, List.mem_filter] at hp
    rw [call_gpr e₂ hp.2]; exact ha.wf₂.bases p hp.1

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : some τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  cases hs
  simp only [isa, ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨rfl, ha⟩

end Taint

/-- Taint tracking for ARMv7. -/
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
  call τ := some (Taint.callStep τ)
  call_sound := Taint.call_sound
  ret τ := some τ
  ret_sound := Taint.ret_sound

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := { regs := RegSet.ofList rs, flags := false }

theorem Taint.agree_ofRegs {rs : List Reg} {s₁ s₂ : State}
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Taint.Agree (Taint.ofRegs rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

end VG.Arm
