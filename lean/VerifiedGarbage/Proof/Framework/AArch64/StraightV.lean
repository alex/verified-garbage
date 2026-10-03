import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# AArch64: straight-line bitwise AdvSIMD code, doubleword lane by doubleword lane

As `Straight`, for the 128-bit vector registers and 16-byte slots
`[base, #16k]` (`k < slots`): a block of `and`, `orr`, `eor`, `bic`, `not`,
`mov`, doubleword shifts (`shl`, `ushr` of 1 to 63), `ldr q` and `str q` of
slots computes each of the two doublewords of its results from the same
doubleword of its operands. `eval` runs it once over an abstract domain on
64-bit words, and `run` relates doubleword `q` of every register and slot by
`R q`, for each `q < 2`. A constant in both doublewords (a mask) is made by
`movz` and `movk` into a general-purpose register (whose value the
evaluator tracks) and `dup v.2d`; `movi v.2d, #0` is the constant 0.
-/

namespace VG.AArch64.StraightV

open VG.Bitslice

/-- The slots: `[base, #16k]` for `k < slots`, read and written. -/
structure Cfg where
  base : Reg
  slots : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the vector registers and slots, and the known
constants of general-purpose registers. -/
structure Env (α : Type) where
  reg : VReg → Option α
  slot : Nat → Option α
  gc : Reg → Option (BitVec 64) := fun _ => none

variable {α : Type}

def Env.setReg (e : Env α) (d : VReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

def Env.setG (e : Env α) (d : Reg) (v : BitVec 64) : Env α :=
  { e with gc := fun r => if r = d then some v else e.gc r }

/-- The slot that `[n, #off]` (a 16-byte access) addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Nat :=
  if n = c.base ∧ off % 16 = 0 ∧ off / 16 < c.slots ∧ off < 65536 then some (off / 16) else none

/-- The value of `movk` of `imm` at halfword `hw` into `v`. -/
def movkVal (v : BitVec 64) (imm : BitVec 16) (hw : Nat) : BitVec 64 :=
  (v &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) ||| (imm.setWidth 64 <<< (16 * hw))

section
variable (D : Dom α 64) (c : Cfg)

/-- `a ∧ ¬b`. -/
def bic (a b : α) : Option α :=
  ((D.const (BitVec.allOnes 64)).bind (D.xor b)).bind (D.and a)

/-- `¬a`. -/
def vnot (a : α) : Option α := (D.const (BitVec.allOnes 64)).bind (D.xor a)

/-- `a <<< n`: the bits `63 - n … 0`, rotated left by `n`. -/
def shl (n : Nat) (a : α) : Option α :=
  ((D.const (BitVec.allOnes 64 >>> n)).bind (D.and a)).bind (D.ror (64 - n))

def binop : VLogicOp → α → α → Option α
  | .eor => D.xor
  | .and => D.and
  | .orr => D.or
  | .bic => bic D
  | .orn => fun _ _ => none

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .vop (.logic op d n m) =>
    match e.reg n, e.reg m with
    | some a, some b => (binop D op a b).map (e.setReg d)
    | _, _ => none
  | .vop (.not d n) => (e.reg n).bind fun a => (vnot D a).map (e.setReg d)
  | .vop (.mov d n) => (e.reg n).map (e.setReg d)
  | .vop (.movi0 d) => (D.const 0).map (e.setReg d)
  | .vop (.dup .d2 d n) => (e.gc n).bind fun v => (D.const v).map (e.setReg d)
  | .vop (.shift .ushr .d2 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 63 then (e.reg n).bind fun a => (D.shr sh a).map (e.setReg d) else none
  | .vop (.shift .shl .d2 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 63 then (e.reg n).bind fun a => (shl D sh a).map (e.setReg d) else none
  | .ldrq t n off => match c.loc n off with
    | some k => (e.slot k).map (e.setReg t)
    | none => none
  | .strq t n off => match c.loc n off with
    | some k => (e.reg t).map (e.setSlot k)
    | none => none
  | .movz .x d imm hw => if d = c.base ∨ ¬ hw < 4 then none else
    some (e.setG d (imm.setWidth 64 <<< (16 * hw)))
  | .movk .x d imm hw => if d = c.base ∨ ¬ hw < 4 then none else
    (e.gc d).map fun v => e.setG d (movkVal v imm hw)
  | _ => none

def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c e i).bind (eval is)

def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c is e post = true) : ∃ e', eval D c is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Doublewords -/

theorem getLsbD_vdword (x : BitVec 128) {q i : Nat} (hi : i < 64) :
    (vdword x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [vdword, hi]

theorem vdword_xor (a b : BitVec 128) (q : Nat) : vdword (a ^^^ b) q = vdword a q ^^^ vdword b q := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [vdword, hj]

theorem vdword_and (a b : BitVec 128) (q : Nat) : vdword (a &&& b) q = vdword a q &&& vdword b q := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [vdword, hj]

theorem vdword_or (a b : BitVec 128) (q : Nat) : vdword (a ||| b) q = vdword a q ||| vdword b q := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [vdword, hj]

theorem vdword_not (a : BitVec 128) {q : Nat} (hq : q < 2) : vdword (~~~a) q = ~~~vdword a q := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, decide_eq_true hj,
    Bool.true_and, decide_eq_true (show 64 * q + j < 128 by omega)]

theorem vdword_zero (q : Nat) : vdword 0 q = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [vdword]

theorem vdword_dwords (a b : BitVec 64) {q : Nat} (hq : q < 2) :
    vdword (ofVDwords a b) q = if q = 0 then a else b := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · simp [vdword_ofVDwords_0]
  · simp [vdword_ofVDwords_1]

theorem vdword_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {q : Nat}
    (hq : q < 2) : vdword (VArr.d2.map2 f x y) q = f 64 (vdword x q) (vdword y q) := by
  simp only [VArr.map2]
  rw [vdword_dwords _ _ hq]
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> rfl

/-- `bic`'s doublewords, as `bic` computes them. -/
theorem bic_eq (x y : BitVec 64) : x &&& (y ^^^ BitVec.allOnes 64) = x &&& ~~~y := by
  rw [BitVec.xor_allOnes]

/-- `shl`'s doublewords, as `shl` computes them. -/
theorem shl_eq (x : BitVec 64) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    (x &&& BitVec.allOnes 64 >>> n).rotateRight (64 - n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateRight_of_lt (by omega)]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes]
  by_cases h : i < 64 - (64 - n)
  · simp only [h, ite_true]
    simp [show i < n by omega, hi]
    omega
  · simp only [h, ite_false]
    simp only [show ¬ i < n by omega, decide_true, hi, Bool.true_and,
      show i - (64 - (64 - n)) = i - n by omega]
    simp [show n + (i - n) < 64 by omega]

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` of the base address `b`. -/
abbrev vAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (16 * k)

structure Rel (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ∀ q < 2, R q a (vdword (s.v r) q)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    ∀ q < 2, R q a (vdword (s.mem.readW (vAddr (s.gpr c.base) k) 128) q)
  gc : ∀ r v, e.gc r = some v → s.gpr r = v

structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (vAddr (s.gpr c.base) k) 16
  slots : 16 * c.slots < 2 ^ 64

def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 16 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  slots := h.slots

theorem slot_sep (b : Addr) {j k : Nat} (hj : 16 * j < 2 ^ 64) (hk : 16 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (vAddr b j) 16 (vAddr b k) 16 := by
  intro x h₁ h₂
  simp only [vAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 16 * n < 2 ^ 64) :
    (⟨b, 16 * n⟩ : Region).Contains (vAddr b k) (128 / 8) := by
  simp only [Region.Contains, vAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loc_some {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some k) :
    n = c.base ∧ off = 16 * k ∧ k < c.slots ∧ off < 65536 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    cases h
    obtain ⟨hb, hm, hlt, h64⟩ := h1
    exact ⟨hb, by omega, hlt, h64⟩
  · cases h

theorem addr_slot {s : State} {n : Reg} {k : Nat} (hk : 16 * k < 65536) :
    addr s 16 n (16 * k) = some (vAddr (s.gpr n) k) := by
  simp only [addr, vAddr]
  rw [ite_eq_left ⟨by omega, by omega⟩]

theorem read16_readW (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp [Mem.readW]

theorem write16_writeW (m : Mem) (a : Addr) (v : BitVec 128) : m.write a 16 v = m.writeW a v := by
  simp [Mem.writeW]

section
variable {D : Dom α 64} {R : Nat → α → BitVec 64 → Prop} {c : Cfg}

structure Post (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e' : Env α) (s s' : State)
    (writes : VReg → Prop) (gwrites : Reg → Prop) : Prop where
  rel : Rel R c e' s'
  ok : Ok c s'
  base : s'.gpr c.base = s.gpr c.base
  gpr : ∀ r, ¬ gwrites r → s'.gpr r = s.gpr r
  carry : s'.c = s.c
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  other : ∀ r, ¬ writes r → s'.v r = s.v r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : VReg → Prop} {G G' : Reg → Prop}
    (p : Post R c e' s s' W G) (h : ∀ r, W r → W' r) (hg : ∀ r, G r → G' r) :
    Post R c e' s s' W' G' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw),
           gpr := fun r hr => p.gpr r fun hw => hr (hg r hw) }

/-- A register written by `setV` whose doublewords are related. -/
theorem post_setV {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : VReg} {a : α}
    {v : BitVec 128} (hv : ∀ q < 2, R q a (vdword v q)) :
    Post R c (e.setReg d a) s (s.setV d v) (· = d) (fun _ => False) where
  rel := {
    reg := fun r b h q hq => by
      simp only [Env.setReg] at h
      simp only [State.setV]
      split at h
      · rename_i hr; cases h; simp only [hr, ite_true]; exact hv q hq
      · rename_i hr; simp only [hr, ite_false]; exact hrel.reg r b h q hq
    slot := fun k b hk h q hq => by
      simpa [State.setV] using hrel.slot k b hk h q hq
    gc := fun r v h => by simpa [State.setV] using hrel.gc r v h }
  ok := hok.congr (by simp [State.setV]) (by simp [State.setV])
  base := by simp [State.setV]
  gpr _ _ := by simp [State.setV]
  carry := by simp [State.setV]
  sp := by simp [State.setV]
  rd := by simp [State.setV]
  wr := by simp [State.setV]
  other r hr := by simp [State.setV, hr]
  frame := by simp only [State.setV]; exact Frame.refl _ _

/-- A general-purpose register written with a known constant. -/
theorem post_setG {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : Reg}
    (hb : d ≠ c.base) (v : BitVec 64) :
    Post R c (e.setG d v) s (s.write .x d v) (fun _ => False) (· = d) := by
  have hbase : (s.write .x d v).gpr c.base = s.gpr c.base := by
    simp [State.write, Ne.symm hb]
  refine ⟨⟨fun r b h q hq => ?_, fun k b hk h q hq => ?_, fun r w h => ?_⟩, hok.congr hbase rfl,
    hbase, fun r hr => ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hrel.reg r b h q hq
  · rw [hbase]; exact hrel.slot k b hk h q hq
  · simp only [Env.setG] at h
    simp only [State.write, BitVec.setWidth_eq]
    split at h
    · rename_i hrd; cases h; simp [hrd]
    · rename_i hrd; simp only [hrd, ite_false]; exact hrel.gc r w h
  · simp [State.write, hr]

theorem exec_vop_some {s : State} {op : VOp} {d : VReg} {v : BitVec 128}
    (h : op.eval s = some (d, v)) : exec (.vop op) s = some (s.setV d v) := by
  simp [exec, h]

theorem step_ok (hD : ∀ q < 2, D.Sound (R q)) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) {i : Instr} (h : step D c e i = some e') :
    ∃ s', exec i s = some s' ∧
      Post R c e' s s' (fun r => vdstOf i = some r) (fun r => dstOf i = some r) := by
  have wv : ∀ (d : VReg), (∀ r, (· = d) r → (fun r => vdstOf (.vop (.mov d d)) = some r) r) :=
    fun d r hr => by simp [vdstOf, VOp.dst, hr]
  cases i with
  | vop op =>
    cases op with
    | logic op d n m =>
      simp only [step] at h
      split at h
      · rename_i a b ha hb
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hRa := hrel.reg n a ha
        have hRb := hrel.reg m b hb
        refine ⟨_, exec_vop_some rfl, (post_setV hok hrel fun q hq => ?_).writes
          (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
        cases op <;> simp only [binop, reduceCtorEq] at ht
        · rw [vdword_and]; exact (hD q hq).and (hRa q hq) (hRb q hq) ht
        · rw [vdword_or]; exact (hD q hq).or (hRa q hq) (hRb q hq) ht
        · rw [vdword_xor]; exact (hD q hq).xor (hRa q hq) (hRb q hq) ht
        · simp only [bic, Option.bind_eq_some_iff] at ht
          obtain ⟨t', ⟨o, ho, ht'⟩, hc⟩ := ht
          rw [vdword_and, vdword_not _ hq, ← bic_eq]
          exact (hD q hq).and (hRa q hq) ((hD q hq).xor (hRb q hq) ((hD q hq).const ho) ht') hc
      · cases h
    | not d n =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, exec_vop_some rfl, (post_setV hok hrel fun q hq => ?_).writes
        (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
      simp only [vnot, Option.bind_eq_some_iff] at ht
      obtain ⟨o, ho, ht⟩ := ht
      rw [vdword_not _ hq, ← BitVec.xor_allOnes]
      exact (hD q hq).xor (hrel.reg n a ha q hq) ((hD q hq).const ho) ht
    | mov d n =>
      simp only [step] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨_, exec_vop_some rfl, (post_setV hok hrel fun q hq => hrel.reg n a ha q hq).writes
        (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
    | movi0 d =>
      simp only [step] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨_, exec_vop_some rfl, (post_setV hok hrel fun q hq => by
          rw [vdword_zero]; exact (hD q hq).const ha).writes
        (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
    | dup a d n =>
      cases a <;> simp only [step] at h <;> try cases h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have hg := hrel.gc n v hv
      exact ⟨_, exec_vop_some rfl, (post_setV hok hrel fun q hq => by
          rw [vdword_dwords _ _ hq, hg]; split <;> exact (hD q hq).const ha).writes
        (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
    | shift op a d n sh =>
      cases a <;> cases op <;> simp only [step] at h <;> try cases h
      all_goals
        split at h
        · rename_i hsh
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨x, hx, h⟩ := h
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨_, exec_vop_some (by
              simp only [VOp.eval]
              split
              · rfl
              · rename_i hc; simp only [VShiftOp.ok, VArr.esize] at hc; simp at hc; omega),
            (post_setV hok hrel fun q hq => ?_).writes
            (fun r h => by simp [vdstOf, VOp.dst, h]) (fun _ h => h.elim)⟩
          rw [vdword_map2 _ _ _ hq]
          simp only [VShiftOp.eval]
          first
            | exact (hD q hq).shr (hrel.reg n x hx q hq) hb
            | (rw [← shl_eq _ hsh.1 hsh.2]
               simp only [shl, Option.bind_eq_some_iff] at hb
               obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hb
               exact (hD q hq).ror ((hD q hq).and (hrel.reg n x hx q hq) ((hD q hq).const ho) ht) hc)
        · cases h
    | _ => simp [step] at h
  | ldrq t n off =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h64⟩ := loc_some hk
      subst hb hoff
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (vAddr (s.gpr c.base) k) 16 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨s.setV t (s.mem.readW (vAddr (s.gpr c.base) k) 128), ?_, ?_⟩
      · simp [exec, addr_slot h64, State.load, hin, read16_readW]
      · exact (post_setV hok hrel fun q hq => hrel.slot k a hlt ha q hq).writes
          (fun r h => by simp [vdstOf, h]) (fun _ h => h.elim)
    · cases h
  | strq t n off =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h64⟩ := loc_some hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      refine ⟨{ s with mem := s.mem.writeW (vAddr (s.gpr c.base) k) (s.v t) }, ?_, ?_⟩
      · simp [exec, addr_slot h64, State.store, hin, write16_writeW]
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (vAddr (s.gpr c.base) j) (128 / 8)
          (vAddr (s.gpr c.base) k) (128 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_,
        fun r' w hw => hrel.gc r' w hw⟩,
        hok.congr rfl rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          intro q hq
          have e := Mem.readW_writeW_self s.mem (vAddr (s.gpr c.base) j) 16 (s.v t) (by decide)
          simp only at e ⊢
          rw [e]
          exact hrel.reg t a ha q hq
        · rename_i hjk
          intro q hq
          simp only
          rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
          exact hrel.slot j b hj hjb q hq
      · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (slot_contains _ hlt hok.slots)
    · cases h
  | movz sz d imm hw =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    cases h
    refine ⟨_, ?_, (post_setG hok hrel hd.1 _).writes (fun _ h => h.elim)
      (fun r h => by simp [dstOf, h])⟩
    simp only [exec, Size.bits, show 16 * hw < 16 * 4 from (Nat.mul_lt_mul_left (by decide)).mpr hd.2,
      ite_true]
  | movk sz d imm hw =>
    cases sz <;> simp only [step] at h
    · cases h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Classical.not_not] at hd
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    have hg := hrel.gc d v hv
    refine ⟨_, ?_, (post_setG hok hrel hd.1 _).writes (fun _ h => h.elim)
      (fun r h => by simp [dstOf, h])⟩
    simp only [exec, Size.bits, show 16 * hw < 16 * 4 from (Nat.mul_lt_mul_left (by decide)).mpr hd.2,
      ite_true, State.read, BitVec.setWidth_eq, hg, movkVal]
  | _ => simp [step] at h

theorem run (hD : ∀ q < 2, D.Sound (R q)) {is : List Instr} {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c e s) (h : eval D c is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c e' s s' (fun r => (is.all fun i => vdstOf i != some r) = false)
        (fun r => (is.all fun i => dstOf i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.base.trans p₁.base, fun r hr => ?_, p.carry.trans p₁.carry, p.sp.trans p₁.sp, p.rd.trans p₁.rd,
      p.wr.trans p₁.wr, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.gpr r hr.2).trans (p₁.gpr r hr.1)
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

/-- `Ok` for slots at offset `off` of a writable region. -/
theorem Ok.of_off {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 16 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    simp only [Region.Contains, vAddr, hb]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega⟩
  slots := by omega

end VG.AArch64.StraightV
