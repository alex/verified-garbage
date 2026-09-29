import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# AArch64: straight-line bitwise code, by evaluation

Untrusted: everything here is checked by Lean.

As `Framework/X86_64/Straight.lean`, for AArch64: a block of 64-bit `and`,
`orr`, `eor`, `ror`, `lsr`, `movz`, `movk`, `add`/`sub` of an immediate,
`ldr` and `str` instructions on registers and on two memory areas
(read-write *slots* `[base, #8k]`, `k < slots`, and read-only *external
words* `[ext, #8k]`, `k < exts`) is evaluated over an abstract domain
(`VG.Bitslice.Dom`) by `eval`. `run` says that the machine then runs the
block without faulting, and that its registers and memory words are related
to the abstract result as they were to the abstract initial values.

Constants are built with `movz` and `movk` (or an immediate added to or
subtracted from a known constant), so the evaluator also tracks the
registers whose concrete value it knows (`Env.cst`); such a register's
abstract value is the domain's constant, if the domain has one. `add d, n,
#0` is a move.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

namespace VG.AArch64.Straight

open VG.Bitslice

/-- The two memory areas: slots `[base, #8k]` for `k < slots` (read and
written), and external words `[ext, #8k]` for `k < exts` (only read). -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots (`none` if unknown), and
the registers whose concrete value is known. -/
structure Env (α : Type) where
  reg : Reg → Option α
  slot : Nat → Option α
  cst : Reg → Option (BitVec 64) := fun _ => none

variable {α : Type}

/-- Set register `d` to the abstract value `a` and the known value `c`. -/
def Env.set (e : Env α) (d : Reg) (a : Option α) (c : Option (BitVec 64)) : Env α :=
  { e with reg := fun r => if r = d then a else e.reg r,
           cst := fun r => if r = d then c else e.cst r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that `[n, #off]` (a 64-bit access) addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Where :=
  if off % 8 = 0 ∧ off < 32768 then
    if n = c.base ∧ off / 8 < c.slots then some (.slot (off / 8))
    else if n = c.ext ∧ off / 8 < c.exts then some (.ext (off / 8))
    else none
  else none

/-- The value of `movk` of `imm` at halfword `hw` into `v`. -/
def movkVal (v : BitVec 64) (imm : BitVec 16) (hw : Nat) : BitVec 64 :=
  (v &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) ||| (imm.setWidth 64 <<< (16 * hw))

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

def binop : LogicOp → α → α → Option α
  | .eor => D.xor
  | .and => D.and
  | .orr => D.or

/-- A known constant. -/
def constant (e : Env α) (d : Reg) (v : BitVec 64) : Env α := e.set d (D.const v) (some v)

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .logic op .x d n m =>
    if d = c.base ∨ d = c.ext then none else
    match e.reg n, e.reg m with
    | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
    | _, _ => none
  | .ror .x d n sh =>
    if d = c.base ∨ d = c.ext ∨ ¬ sh < 64 then none else
    match e.reg n with
    | some a => (D.ror sh a).map fun r => e.set d (some r) none
    | none => none
  | .lsr .x d n sh =>
    if d = c.base ∨ d = c.ext ∨ ¬ sh < 64 then none else
    match e.reg n with
    | some a => (D.shr sh a).map fun r => e.set d (some r) none
    | none => none
  | .addImm .x d n imm =>
    if d = c.base ∨ d = c.ext ∨ ¬ imm < 4096 then none else
    match e.cst n with
    | some v => some (constant D e d (v + BitVec.ofNat 64 imm))
    | none => if imm = 0 then (e.reg n).map fun a => e.set d (some a) none else none
  | .subImm .x d n imm =>
    if d = c.base ∨ d = c.ext ∨ ¬ imm < 4096 then none else
    match e.cst n with
    | some v => some (constant D e d (v - BitVec.ofNat 64 imm))
    | none => none
  | .movz .x d imm hw =>
    if d = c.base ∨ d = c.ext ∨ ¬ hw < 4 then none else
    some (constant D e d (imm.setWidth 64 <<< (16 * hw)))
  | .movk .x d imm hw =>
    if d = c.base ∨ d = c.ext ∨ ¬ hw < 4 then none else
    match e.cst d with
    | some v => some (constant D e d (movkVal v imm hw))
    | none => none
  | .ldr .x t n off =>
    if t = c.base ∨ t = c.ext then none else
    match c.loc n off with
    | some (.slot k) => (e.slot k).map fun a => e.set t (some a) none
    | some (.ext k) => (ext k).map fun a => e.set t (some a) none
    | none => none
  | .str .x t n off =>
    match c.loc n off with
    | some (.slot k) => (e.reg t).map (e.setSlot k)
    | _ => none
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

/-- Evaluates the block and checks `post` of the result: for `decide`. -/
def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c ext is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c ext is e post = true) : ∃ e', eval D c ext is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` (or external word `k`) of the base address `b`. -/
abbrev wordAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (8 * k)

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known, and the known constants are the
registers' values. -/
structure Rel (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 64)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 64)
  cst : ∀ r v, e.cst r = some v → s.gpr r = v

/-- What the machine needs for the memory areas: they are accessible, the
slots do not wrap around, and the external words do not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (wordAddr (s.gpr c.base) k) 8
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.ext) k) 8
  slots : 8 * c.slots < 2 ^ 64
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (wordAddr (s.gpr c.base) k) 8 (wordAddr (s.gpr c.ext) j) 8

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 8 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  slots := h.slots
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem slot_sep (b : Addr) {j k : Nat} (hj : 8 * j < 2 ^ 64) (hk : 8 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (wordAddr b j) 8 (wordAddr b k) 8 := by
  intro x h₁ h₂
  simp only [wordAddr] at h₁ h₂
  have : j < k ∨ k < j := by omega
  rcases this with h' | h' <;> bv_omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 8 * n < 2 ^ 64) :
    (⟨b, 8 * n⟩ : Region).Contains (wordAddr b k) (64 / 8) := by
  simp only [Region.Contains, wordAddr]
  rw [show b + BitVec.ofNat 64 (8 * k) - b = BitVec.ofNat 64 (8 * k) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loc_some_slot {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.slot k)) :
    n = c.base ∧ off = 8 * k ∧ k < c.slots ∧ off < 32768 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega, h2.2, h1.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.ext k)) :
    n = c.ext ∧ off = 8 * k ∧ k < c.exts ∧ off < 32768 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega, h2.2, h1.2⟩
      · cases h
  · cases h

theorem addr_word {s : State} {n : Reg} {k : Nat} (hk : 8 * k < 32768) :
    addr s 8 n (8 * k) = some (wordAddr (s.gpr n) k) := by
  simp only [addr, wordAddr]
  rw [ite_eq_left ⟨by omega, by omega⟩]

section
variable {D : Dom α 64} {R : α → BitVec 64 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : Reg → Prop) : Prop where
  rel : Rel R c ext e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : Reg → Prop}
    (p : Post R c ext e' s s' W) (h : ∀ r, W r → W' r) : Post R c ext e' s s' W' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw) }

theorem write_x_gpr (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [State.write, BitVec.setWidth_eq]

theorem read_x (s : State) (n : Reg) : s.read .x n = s.gpr n := by
  simp only [State.read, BitVec.setWidth_eq]

/-- Writing register `d` with a value related to `a` (if known) and equal to `cv` (if known). -/
theorem post_set {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg} {a : Option α}
    {cv : Option (BitVec 64)} {v : BitVec 64} (hv : ∀ x, a = some x → R x v)
    (hc : ∀ x, cv = some x → v = x) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.set d a cv) s (s.write .x d v) (· = d) := by
  have hbase : (s.write .x d v).gpr c.base = s.gpr c.base := by
    rw [write_x_gpr, ite_eq_right (Ne.symm hb)]
  have hext : (s.write .x d v).gpr c.ext = s.gpr c.ext := by
    rw [write_x_gpr, ite_eq_right (Ne.symm he)]
  refine ⟨⟨fun r x h => ?_, fun k x hk h => ?_, fun k x hk h => ?_, fun r x h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.set] at h
    rw [write_x_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hv x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.reg r x h
  · rw [hbase]; exact hrel.slot k x hk h
  · rw [hext]; exact hrel.ext k x hk h
  · simp only [Env.set] at h
    rw [write_x_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hc x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.cst r x h
  · rw [write_x_gpr, ite_eq_right hr]

theorem const_ok {e : Env α} {s : State} (hD : D.Sound R) (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg} {v : BitVec 64}
    (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (constant D e d v) s (s.write .x d v) (· = d) :=
  post_set hok hrel (fun _ h => hD.const h) (fun _ h => Option.some.inj h) hb he

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dstOf i = some r) := by
  cases i with
  | logic op sz d n m =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i a b ha hb
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      have hRa := hrel.reg n a ha
      have hRb := hrel.reg m b hb
      refine ⟨_, rfl, ?_⟩
      refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_) (fun _ h => by cases h)
        hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      cases op <;> simp only [binop, read_x] at hr ⊢
      · exact hD.and hRa hRb hr
      · exact hD.or hRa hRb hr
      · exact hD.xor hRa hRb hr
    · cases h
  | ror sz d n sh =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, hsh⟩ := hd
    split at h
    · rename_i a ha
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [exec, Size.bits, hsh, ite_true, Option.some.injEq, exists_eq_left']
      exact (post_set hok hrel (a := some r) (cv := none)
        (fun x hx => by cases hx; rw [read_x]; exact hD.ror (hrel.reg n a ha) hr)
        (fun _ h => by cases h) hdb hde).writes fun r h => by simp [dstOf, h]
    · cases h
  | lsr sz d n sh =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, hsh⟩ := hd
    split at h
    · rename_i a ha
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [exec, Size.bits, hsh, ite_true, Option.some.injEq, exists_eq_left']
      exact (post_set hok hrel (a := some r) (cv := none)
        (fun x hx => by cases hx; rw [read_x]; exact hD.shr (hrel.reg n a ha) hr)
        (fun _ h => by cases h) hdb hde).writes fun r h => by simp [dstOf, h]
    · cases h
  | addImm sz d n imm =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, himm⟩ := hd
    split at h
    · rename_i v hv
      cases h
      simp only [exec, himm, ite_true, Option.some.injEq, exists_eq_left']
      rw [read_x, hrel.cst n v hv]
      exact (const_ok hD hok hrel hdb hde).writes fun r h => by simp [dstOf, h]
    · split at h
      · rename_i h0
        subst h0
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [exec, himm, ite_true, Option.some.injEq, exists_eq_left']
        refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hdb hde).writes fun r h => by simp [dstOf, h]
        cases hx
        rw [read_x]
        simpa using hrel.reg n a ha
      · cases h
  | subImm sz d n imm =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, himm⟩ := hd
    split at h
    · rename_i v hv
      cases h
      simp only [exec, himm, ite_true, Option.some.injEq, exists_eq_left']
      rw [read_x, hrel.cst n v hv]
      exact (const_ok hD hok hrel hdb hde).writes fun r h => by simp [dstOf, h]
    · cases h
  | movz sz d imm hw' =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, hh⟩ := hd
    cases h
    simp only [exec, Size.bits, show 16 * hw' < 64 by omega, ite_true, Option.some.injEq, exists_eq_left']
    exact (const_ok hD hok hrel hdb hde).writes fun r h => by simp [dstOf, h]
  | movk sz d imm hw' =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨hdb, hde, hh⟩ := hd
    split at h
    · rename_i v hv
      cases h
      simp only [exec, Size.bits, show 16 * hw' < 64 by omega, ite_true, Option.some.injEq, exists_eq_left']
      rw [read_x, hrel.cst d v hv]
      exact (const_ok hD hok hrel hdb hde).writes fun r h => by simp [dstOf, h]
    · cases h
  | ldr sz t n off =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_slot hk
      subst hb hoff
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 8 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      simp only [exec_ldr_x ⟨by omega, h32⟩ hin, Option.some.injEq, exists_eq_left']
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.slot k a hlt ha
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_ext hk
      subst hb hoff
      simp only [exec_ldr_x ⟨by omega, h32⟩ (hok.extIn k hlt), Option.some.injEq, exists_eq_left']
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.ext k a hlt ha
    · cases h
  | str sz t n off =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_slot hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      simp only [exec_str_x ⟨by omega, h32⟩ hin, Option.some.injEq, exists_eq_left']
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (64 / 8)
          (wordAddr (s.gpr c.base) k) (64 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_,
          fun r v h => hrel.cst r v h⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          have := Mem.readW_writeW_self64 s.mem (wordAddr (s.gpr c.base) j) (s.gpr t)
          rw [this]
          exact hrel.reg t a ha
        · rename_i hjk
          have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) (hsep j hj hjk) (by decide)
          rw [this]
          exact hrel.slot j b hj hjb
      · have hs : Mem.Sep (wordAddr (s.gpr c.ext) j) (64 / 8) (wordAddr (s.gpr c.base) k) (64 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) hs (by decide)
        rw [this]
        exact hrel.ext j b hj hjb
      · have := (Frame.refl [slotRegion c s] s.mem).writeW (List.mem_singleton_self _) (s.gpr t)
          (slot_contains _ hlt hok.slots)
        exact this
    · cases h
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => dstOf i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.sp.trans p₁.sp, p.base.trans p₁.base,
      p.ext.trans p₁.ext, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

/-- `Ok` for slots at the start of a writable region `r` of `s.wr` and no
external words. -/
theorem Ok.of_region {c : Cfg} {s : State} {r : Region} (hr : r ∈ s.wr)
    (hb : r.base = s.gpr c.base) (hlen : 8 * c.slots ≤ r.len) (hn : 8 * c.slots < 2 ^ 64)
    (he : c.exts = 0) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    have := slot_contains (s.gpr c.base) hk hn
    simp only [Region.Contains] at this ⊢
    rw [hb]; omega⟩
  extIn k hk := by omega
  slots := hn
  sep k _ j hj := by omega

/-- The machine runs a block that the abstract evaluator accepts, and the
result is the same whatever the domain: facts about it can be gathered
from several domains and relations. -/
theorem run_unique {s s₁ s₂ : State} {is : List Instr} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa is s = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

theorem contains_word {r : Region} {a : Addr} {off k n : Nat} (ha : a = r.base + BitVec.ofNat 64 off)
    (hk : off + 8 * k + 8 ≤ n) (hn : n ≤ r.len) (hlen : r.len < 2 ^ 64) :
    r.Contains (wordAddr a k) 8 := by
  simp only [Region.Contains, wordAddr, ha]
  rw [show r.base + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) - r.base =
    BitVec.ofNat 64 (off + 8 * k) by rw [BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `Ok` for slots at offset `off` of a writable region, and no external words. -/
theorem Ok.of_off {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 8 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) (he : c.exts = 0) : Ok c s where
  slotIn k hk := ⟨r, hr, contains_word hb (by omega) (Nat.le_refl _) hn⟩
  extIn k hk := by omega
  slots := by omega
  sep k _ j hj := by omega

/-- `Ok` for external words at offset `off` of a readable region, and no slots. -/
theorem Ok.of_ext {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.rd ++ s.wr)
    (hb : s.gpr c.ext = r.base + BitVec.ofNat 64 off) (hlen : off + 8 * c.exts ≤ r.len)
    (hn : r.len < 2 ^ 64) (hs : c.slots = 0) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := ⟨r, hr, contains_word hb (by omega) (Nat.le_refl _) hn⟩
  slots := by omega
  sep k hk := by omega

end VG.AArch64.Straight
