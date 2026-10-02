import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# ARMv7: straight-line bitwise code, by evaluation

As `Framework/AArch64/Straight.lean`, for ARMv7: a block of `and`, `orr`,
`eor` (with a register, an immediate, or a register rotated or shifted
right as the second operand), `mov`, `add`/`sub` of known constants,
`movw`, `movt`, `ldr` and `str` instructions on registers and on two memory
areas (read-write *slots* `[base, #4k]`, `k < slots`, and read-only
*external words* `[ext, #4k]`, `k < exts`) is evaluated over an abstract
domain (`VG.Bitslice.Dom`) by `eval`. `run` says that the machine then runs
the block without faulting, and that its registers and memory words are
related to the abstract result as they were to the abstract initial values.

Constants are built with `mov` of an immediate, `movw` and `movt` (or an
immediate added to or subtracted from a known constant), so the evaluator
also tracks the registers whose concrete value it knows (`Env.cst`); such a
register's abstract value is the domain's constant, if the domain has one.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

namespace VG.Arm.Straight

open VG.Bitslice

/-- The two memory areas: slots `[base, #4k]` for `k < slots` (read and
written), and external words `[ext, #4k]` for `k < exts` (only read). -/
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
  cst : Reg → Option (BitVec 32) := fun _ => none

variable {α : Type}

/-- Set register `d` to the abstract value `a` and the known value `c`. -/
def Env.set (e : Env α) (d : Reg) (a : Option α) (c : Option (BitVec 32)) : Env α :=
  { e with reg := fun r => if r = d then a else e.reg r,
           cst := fun r => if r = d then c else e.cst r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that `[n, #off]` addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Where :=
  if off % 4 = 0 ∧ off < 4096 then
    if n = c.base ∧ off / 4 < c.slots then some (.slot (off / 4))
    else if n = c.ext ∧ off / 4 < c.exts then some (.ext (off / 4))
    else none
  else none

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

def binop : DpOp → α → α → Option α
  | .eor => D.xor
  | .and => D.and
  | .orr => D.or
  | _ => fun _ _ => none

/-- A known constant. -/
def constant (e : Env α) (d : Reg) (v : BitVec 32) : Env α := e.set d (D.const v) (some v)

/-- The abstract value of a second operand. -/
def op2Abs (e : Env α) : Op2 → Option α
  | .imm v => if encodable v then D.const v else none
  | .reg r => e.reg r
  | .shifted r .ror n => if 1 ≤ n ∧ n ≤ 31 then (e.reg r).bind (D.ror n) else none
  | .shifted r .lsr n => if 1 ≤ n ∧ n ≤ 31 then (e.reg r).bind (D.shr n) else none
  | .shifted _ .lsl _ => none

/-- The known value of a second operand. -/
def op2Cst (e : Env α) : Op2 → Option (BitVec 32)
  | .imm v => if encodable v then some v else none
  | .reg r => e.cst r
  | .shifted .. => none

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .mov d o =>
    if d = c.base ∨ d = c.ext then none else
    match op2Cst e o with
    | some v => some (constant D e d v)
    | none => (op2Abs D e o).map fun a => e.set d (some a) none
  | .dp op d n o =>
    if d = c.base ∨ d = c.ext then none else
    match op with
    | .add => match e.cst n, op2Cst e o with
      | some x, some y => some (constant D e d (x + y))
      | _, _ => none
    | .sub => match e.cst n, op2Cst e o with
      | some x, some y => some (constant D e d (x - y))
      | _, _ => none
    | _ => match e.reg n, op2Abs D e o with
      | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
      | _, _ => none
  | .movw d imm =>
    if d = c.base ∨ d = c.ext then none else some (constant D e d (imm.setWidth 32))
  | .movt d imm =>
    if d = c.base ∨ d = c.ext then none else
    match e.cst d with
    | some v => some (constant D e d (imm ++ v.extractLsb' 0 16 : BitVec 32))
    | none => none
  | .ldr t n off =>
    if t = c.base ∨ t = c.ext then none else
    match c.loc n off with
    | some (.slot k) => (e.slot k).map fun a => e.set t (some a) none
    | some (.ext k) => (ext k).map fun a => e.set t (some a) none
    | none => none
  | .str t n off =>
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

/-- The address of word `k` (slot or external word) from the base `b`. -/
abbrev wordAddr (b : BitVec 32) (k : Nat) : Addr := State.addr (b + BitVec.ofNat 32 (4 * k))

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known, and the known constants are the
registers' values. -/
structure Rel (R : α → BitVec 32 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 32)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 32)
  cst : ∀ r v, e.cst r = some v → s.gpr r = v

/-- What the machine needs for the memory areas: they are accessible, the
slots do not wrap around, and the external words do not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (wordAddr (s.gpr c.base) k) 4
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.ext) k) 4
  slots : (s.gpr c.base).toNat + 4 * c.slots ≤ 2 ^ 32
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (wordAddr (s.gpr c.base) k) 4 (wordAddr (s.gpr c.ext) j) 4

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨State.addr (s.gpr c.base), 4 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  slots := by rw [hb]; exact h.slots
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- Word `k` from `b`, when it does not wrap around. -/
theorem wordAddr_toNat (b : BitVec 32) {k : Nat} (h : b.toNat + 4 * k < 2 ^ 32) :
    (wordAddr b k).toNat = b.toNat + 4 * k := by
  rw [wordAddr, toNat_addr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * k) (by omega),
    Nat.mod_eq_of_lt h]

theorem slot_sep (b : BitVec 32) {j k : Nat} (hj : b.toNat + 4 * j < 2 ^ 32)
    (hk : b.toNat + 4 * k < 2 ^ 32) (h : j ≠ k) :
    Mem.Sep (wordAddr b j) 4 (wordAddr b k) 4 := by
  intro x h₁ h₂
  have e1 := wordAddr_toNat b hj
  have e2 := wordAddr_toNat b hk
  generalize wordAddr b j = A at h₁ e1
  generalize wordAddr b k = B at h₂ e2
  have : j < k ∨ k < j := by omega
  rcases this with h' | h' <;> bv_omega

theorem slot_contains (b : BitVec 32) {n k : Nat} (hk : k < n) (hn : b.toNat + 4 * n ≤ 2 ^ 32) :
    (⟨State.addr b, 4 * n⟩ : Region).Contains (wordAddr b k) (32 / 8) := by
  simp only [Region.Contains]
  have e1 := wordAddr_toNat b (k := k) (by omega)
  have e2 := toNat_addr b
  generalize wordAddr b k = A at e1
  generalize State.addr b = B at e2
  rw [show (32 : Nat) / 8 = 4 from rfl]
  have : (A - B).toNat = 4 * k := by bv_omega
  omega

theorem loc_some_slot {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.slot k)) :
    n = c.base ∧ off = 4 * k ∧ k < c.slots ∧ off < 4096 := by
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
    n = c.ext ∧ off = 4 * k ∧ k < c.exts ∧ off < 4096 := by
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

section
variable {D : Dom α 32} {R : α → BitVec 32 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 32 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
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

theorem setReg_gpr (s : State) (d : Reg) (v : BitVec 32) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl

/-- Writing register `d` with a value related to `a` (if known) and equal to `cv` (if known). -/
theorem post_set {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : Option α} {cv : Option (BitVec 32)} {v : BitVec 32} (hv : ∀ x, a = some x → R x v)
    (hc : ∀ x, cv = some x → v = x) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.set d a cv) s (s.setReg d v) (· = d) := by
  have hbase : (s.setReg d v).gpr c.base = s.gpr c.base := by
    rw [setReg_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm hb)]
  have hext : (s.setReg d v).gpr c.ext = s.gpr c.ext := by
    rw [setReg_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm he)]
  refine ⟨⟨fun r x h => ?_, fun k x hk h => ?_, fun k x hk h => ?_, fun r x h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.set] at h
    rw [setReg_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hv x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.reg r x h
  · rw [hbase]; exact hrel.slot k x hk h
  · rw [hext]; exact hrel.ext k x hk h
  · simp only [Env.set] at h
    rw [setReg_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hc x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.cst r x h
  · rw [setReg_gpr, ite_eq_right hr]

theorem const_ok {e : Env α} {s : State} (hD : D.Sound R) (hok : Ok c s) (hrel : Rel R c ext e s)
    {d : Reg} {v : BitVec 32} (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (constant D e d v) s (s.setReg d v) (· = d) :=
  post_set hok hrel (fun _ h => hD.const h) (fun _ h => Option.some.inj h) hb he

theorem op2Abs_ok (hD : D.Sound R) {e : Env α} {s : State} (hrel : Rel R c ext e s) {o : Op2}
    {a : α} (h : op2Abs D e o = some a) : ∃ v, o.eval s = some v ∧ R a v := by
  cases o with
  | imm v =>
    simp only [op2Abs] at h
    split at h
    · rename_i hv; exact ⟨v, by simp [Op2.eval, hv], hD.const h⟩
    · cases h
  | reg r => exact ⟨_, rfl, hrel.reg r a h⟩
  | shifted r sh n =>
    cases sh with
    | lsl => simp [op2Abs] at h
    | ror =>
      simp only [op2Abs] at h
      split at h
      · rename_i hn
        obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, by simp [Op2.eval, hn], hD.ror (hrel.reg r b hb) hr⟩
      · cases h
    | lsr =>
      simp only [op2Abs] at h
      split at h
      · rename_i hn
        obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, by simp [Op2.eval, hn], hD.shr (hrel.reg r b hb) hr⟩
      · cases h

theorem op2Cst_ok {e : Env α} {s : State} (hrel : Rel R c ext e s) {o : Op2} {v : BitVec 32}
    (h : op2Cst e o = some v) : o.eval s = some v := by
  cases o with
  | imm w =>
    simp only [op2Cst] at h
    split at h
    · rename_i hw; cases h; simp [Op2.eval, hw]
    · cases h
  | reg r => simp only [op2Cst] at h; simp [Op2.eval, hrel.cst r v h]
  | shifted => simp [op2Cst] at h

theorem addr_word {s : State} {n : Reg} {k : Nat} :
    State.addr (s.gpr n + BitVec.ofNat 32 (4 * k)) = wordAddr (s.gpr n) k := rfl

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dstOf i = some r) := by
  cases i with
  | mov d o =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i v hv
      cases h
      refine ⟨s.setReg d v, by simp [exec, op2Cst_ok hrel hv], ?_⟩
      exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
    · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel ha
      refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
      exact (post_set hok hrel (a := some a) (cv := none) (fun x hx => by cases hx; exact hR)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
  | dp op d n o =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    cases op with
    | add =>
      simp only at h
      split at h
      · rename_i x y hx hy
        cases h
        refine ⟨_, by simp only [exec, op2Cst_ok hrel hy, hrel.cst n x hx, Option.map_some]; rfl, ?_⟩
        exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      · cases h
    | sub =>
      simp only at h
      split at h
      · rename_i x y hx hy
        cases h
        refine ⟨_, by simp only [exec, op2Cst_ok hrel hy, hrel.cst n x hx, Option.map_some]; rfl, ?_⟩
        exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      · cases h
    | and | orr | eor =>
      simp only at h
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel hb
        have hRa := hrel.reg n a ha
        refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
        refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_) (fun _ h => by cases h)
          hd.1 hd.2).writes fun r h => by simp [dstOf, h]
        cases hx
        simp only [binop] at hr
        first
        | exact hD.and hRa hR hr
        | exact hD.or hRa hR hr
        | exact hD.xor hRa hR hr
      · cases h
  | movw d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    cases h
    exact ⟨_, rfl, (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]⟩
  | movt d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i v hv
      cases h
      refine ⟨_, rfl, ?_⟩
      rw [hrel.cst d v hv]
      exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
    · cases h
  | ldr t n off =>
    simp only [step] at h
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
      have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 4 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨_, exec_ldr h32 hin, ?_⟩
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.slot k a hlt ha
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_ext hk
      subst hb hoff
      refine ⟨_, exec_ldr h32 (hok.extIn k hlt), ?_⟩
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.ext k a hlt ha
    · cases h
  | str t n off =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_slot hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      refine ⟨_, exec_str h32 hin, ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (32 / 8)
          (wordAddr (s.gpr c.base) k) (32 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_,
          fun r v h => hrel.cst r v h⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          have := Mem.readW_writeW_self32 s.mem (wordAddr (s.gpr c.base) j) (s.gpr t)
          rw [addr_word, this]
          exact hrel.reg t a ha
        · rename_i hjk
          have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) (hsep j hj hjk) (by decide)
          rw [addr_word, this]
          exact hrel.slot j b hj hjb
      · have hs : Mem.Sep (wordAddr (s.gpr c.ext) j) (32 / 8) (wordAddr (s.gpr c.base) k) (32 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) hs (by decide)
        rw [addr_word, this]
        exact hrel.ext j b hj hjb
      · exact (Frame.refl [slotRegion c s] s.mem).writeW (List.mem_singleton_self _) (s.gpr t)
          (slot_contains _ hlt hok.slots)
    all_goals cases h
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

/-- The machine runs a block that the abstract evaluator accepts, and the
result is the same whatever the domain: facts about it can be gathered
from several domains and relations. -/
theorem run_unique {s s₁ s₂ : State} {is : List Instr} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa is s = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-! ## Memory areas in regions -/

theorem add_ofNat_ofNat (b : BitVec 32) (x y : Nat) :
    b + BitVec.ofNat 32 x + BitVec.ofNat 32 y = b + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- An access at an offset of a region that does not wrap around. -/
theorem contains_off {b : BitVec 32} {len off n : Nat} (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + n ≤ len) (hn : 0 < n) :
    (⟨State.addr b, len⟩ : Region).Contains (State.addr (b + BitVec.ofNat 32 off)) n := by
  rw [addr_add (by omega)]
  simp only [Region.Contains]
  rw [show State.addr b + BitVec.ofNat 64 off - State.addr b = BitVec.ofNat 64 off by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

theorem in_off {rs : List Region} {b : BitVec 32} {len off n : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ rs) (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + n ≤ len) (hn : 0 < n) : InRegions rs (State.addr (b + BitVec.ofNat 32 off)) n :=
  ⟨_, hr, contains_off hfit h hn⟩

/-- `Ok` for slots at offset `off` of a writable region, and no external words. -/
theorem Ok.of_off {c : Cfg} {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr c.base = b + BitVec.ofNat 32 off) (hlen : off + 4 * c.slots ≤ len)
    (he : c.exts = 0) : Ok c s where
  slotIn k hk := by
    rw [hb, wordAddr, add_ofNat_ofNat]; exact in_off hr hfit (by omega) (by omega)
  extIn k hk := by omega
  slots := by
    rcases Nat.eq_zero_or_pos c.slots with h0 | h0
    · rw [h0]; have := (s.gpr c.base).isLt; omega
    · rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega
  sep k _ j hj := by omega

/-- `Ok` for external words at offset `off` of a readable region, and no slots. -/
theorem Ok.of_ext {c : Cfg} {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.rd ++ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (he : s.gpr c.ext = b + BitVec.ofNat 32 off) (hlen : off + 4 * c.exts ≤ len)
    (hs : c.slots = 0) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := by
    rw [he, wordAddr, add_ofNat_ofNat]; exact in_off hr hfit (by omega) (by omega)
  slots := by rw [hs]; have := (s.gpr c.base).isLt; omega
  sep k hk := by omega

end VG.Arm.Straight
