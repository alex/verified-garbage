import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# x86-64: straight-line bitwise AVX2 code, quadword lane by lane

A block of 256-bit `vpxor`, `vpand`, `vpor`, `vpandn`, `vmovdqa`,
quadword shifts (`vpsllq`, `vpsrlq`) and `vmovdqu` loads and stores of
32-byte *slots* `[base + 32k]` (`k < slots`) computes each of the four
quadwords of its results from the same quadword of its operands, by the
same 64-bit operations. `eval` runs it once over an abstract domain on
64-bit words (`VG.Bitslice.Dom`), and `run` says that the machine then runs
the block without faulting and that quadword `q` of every register and slot
is related by `R q` to its abstract result, for each `q < 4`, as it was to
the abstract initial values: one evaluation (one `decide`) proves what the
code computes in all four lanes, each with its own relation (e.g. its own
assignment of inputs).

`vpandn` is `(a ⊕ 1…1) ∧ b`, and `vpsllq` by `n` is a rotation of the bits
`63 - n … 0` (`(a ∧ 1…1 >>> n)` rotated right by `64 - n`), so the domain
needs only its usual operations. A constant in every quadword (a mask) is
made by `movabs r, v`, `vmovq x, r` and `vpbroadcastq y, x`: the evaluator
tracks the known constants of general-purpose registers and of the low
quadwords of vector registers to give it. It rejects (`none`) any other
instruction or memory operand, and the use of an unknown value; nothing it
accepts writes a flag, nor a general-purpose register but by `movabs`.
-/

namespace VG.X86_64.StraightY

open VG.Bitslice

/-- Quadword `q` of a 256-bit word. -/
def qw (x : BitVec 256) (q : Nat) : BitVec 64 := x.extractLsb' (64 * q) 64

/-- The slots: `[base + 32k]` for `k < slots`, read and written. -/
structure Cfg where
  base : Reg
  slots : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots, the known constants of
general-purpose registers and of the low quadword of vector registers; `none`
if unknown. -/
structure Env (α : Type) where
  reg : XReg → Option α
  slot : Nat → Option α
  gc : Reg → Option (BitVec 64) := fun _ => none
  xc : XReg → Option (BitVec 64) := fun _ => none

variable {α : Type}

/-- Register `d` holds `v` in every quadword; its low quadword is not known
to be a constant. -/
def Env.setReg (e : Env α) (d : XReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r,
           xc := fun r => if r = d then none else e.xc r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- The slot that a memory operand addresses, if any. -/
def Cfg.loc (c : Cfg) (m : MemOp) : Option Nat :=
  if m.index = none ∧ m.base = c.base ∧ 0 ≤ m.disp ∧ m.disp % 32 = 0 ∧ m.disp.toNat / 32 < c.slots
  then some (m.disp.toNat / 32) else none

/-- The memory operand of slot `k` of base register `b`. -/
def slotOp (b : Reg) (k : Nat) : MemOp := { base := b, disp := ((32 * k : Nat) : Int) }

/-- The register a vector instruction writes, if any. -/
def ydst : Instr → Option XReg
  | .vop (.vbin _ _ d _ _) | .vop (.vmovdqa _ d _) | .vop (.vshift _ _ d _ _) => some d
  | .vop (.vmovq d _) | .vop (.vpbroadcastq _ d _) => some d
  | .vmovdquLoad _ d _ => some d
  | _ => none

section
variable (D : Dom α 64) (c : Cfg)

/-- `¬a ∧ b`. -/
def andn (a b : α) : Option α :=
  ((D.const (BitVec.allOnes 64)).bind (D.xor a)).bind (D.and · b)

/-- `a <<< n`: the bits `63 - n … 0`, rotated left by `n`. -/
def shl (n : Nat) (a : α) : Option α :=
  ((D.const (BitVec.allOnes 64 >>> n)).bind (D.and a)).bind (D.ror (64 - n))

def binop : VBinOp → Option (α → α → Option α)
  | .vpxor => some D.xor
  | .vpand => some D.and
  | .vpor => some D.or
  | .vpandn => some (andn D)
  | _ => none

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .vop (.vbin op .l256 d a b) =>
    match binop D op, e.reg a, e.reg b with
    | some f, some x, some y => (f x y).map (e.setReg d)
    | _, _, _ => none
  | .vop (.vmovdqa .l256 d r) => (e.reg r).map (e.setReg d)
  | .vop (.vshift op .l256 d r n) =>
    if 1 ≤ n.toNat ∧ n.toNat ≤ 63 then
      match op, e.reg r with
      | .psrlq, some a => (D.shr n.toNat a).map (e.setReg d)
      | .psllq, some a => (shl D n.toNat a).map (e.setReg d)
      | _, _ => none
    else none
  | .vmovdquLoad .l256 d m => match c.loc m with
    | some k => (e.slot k).map (e.setReg d)
    | none => none
  | .vmovdquStore .l256 m r => match c.loc m with
    | some k => (e.reg r).map (e.setSlot k)
    | none => none
  | .movImm64 d v => if d = c.base then none else
    some { e with gc := fun r => if r = d then some v else e.gc r }
  | .vop (.vmovq d r) => (e.gc r).map fun v =>
    { e with reg := fun x => if x = d then none else e.reg x,
             xc := fun x => if x = d then some v else e.xc x }
  | .vop (.vpbroadcastq .l256 d x) => (e.xc x).bind fun v => (D.const v).map fun a =>
    { e with reg := fun r => if r = d then some a else e.reg r,
             xc := fun r => if r = d then some v else e.xc r }
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c e i).bind (eval is)

/-- Evaluates the block and checks `post` of the result: for `decide`. -/
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

/-! ## Quadwords -/

theorem cases4 {q : Nat} (hq : q < 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega

theorem getLsbD_qw (x : BitVec 256) {q i : Nat} (hi : i < 64) :
    (qw x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qw, hi]

/-- A quadword of two lanes. -/
theorem qw_app (f : Nat → BitVec 128) {q : Nat} (hq : q < 4) :
    qw (f 1 ++ f 0) q = qword (f (q / 2)) (q % 2) := by
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qw, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj,
      Bool.true_and, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul]
    split <;> first | (exfalso; omega) | exact congrArg _ (by omega)

/-- A quadword of a register is a quadword of one of its lanes. -/
theorem qw_ymm (s : State) (r : XReg) {q : Nat} (hq : q < 4) :
    qw (s.ymm r) q = qword (s.lane r (q / 2)) (q % 2) :=
  qw_app (s.lane r) hq

theorem qword_xor (a b : BitVec 128) (i : Nat) : qword (a ^^^ b) i = qword a i ^^^ qword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem qword_and (a b : BitVec 128) (i : Nat) : qword (a &&& b) i = qword a i &&& qword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem qword_or (a b : BitVec 128) (i : Nat) : qword (a ||| b) i = qword a i ||| qword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem qword_andn (a b : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (~~~a &&& b) i = ~~~qword a i &&& qword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_not,
    decide_eq_true hj, Bool.true_and, decide_eq_true (show 64 * i + j < 128 by omega)]

theorem qword_app (x y : BitVec 64) {i : Nat} (hi : i < 2) :
    qword (x ++ y) i = if i = 0 then y else x := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj,
      Bool.true_and, Nat.reduceMul, ↓reduceIte, Nat.one_ne_zero]
    split <;> first | (exfalso; omega) | exact congrArg _ (by omega)

theorem qword_psrlq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat ≤ 63) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq a n) i = qword a i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rw [qword_app _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

theorem qword_psllq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat ≤ 63) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psllq a n) i = qword a i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rw [qword_app _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

/-- `vpandn`'s quadwords. -/
theorem andn_eq (x y : BitVec 64) : (x ^^^ BitVec.allOnes 64) &&& y = ~~~x &&& y := by
  rw [BitVec.xor_allOnes]

/-- `vpsllq`'s quadwords, as `shl` computes them. -/
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
abbrev yAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (32 * k)

/-- Quadword `q` of every register and slot that is known is related by
`R q` to its abstract value. -/
structure Rel (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ∀ q < 4, R q a (qw (s.ymm r) q)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    ∀ q < 4, R q a (qw (s.mem.readW (yAddr (s.gpr c.base) k) 256) q)
  gc : ∀ r v, e.gc r = some v → s.gpr r = v
  xc : ∀ r v, e.xc r = some v → qw (s.ymm r) 0 = v

/-- The slots are writable and do not wrap around. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (yAddr (s.gpr c.base) k) 32
  slots : 32 * c.slots < 2 ^ 64

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 32 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  slots := h.slots

theorem slot_sep (b : Addr) {j k : Nat} (hj : 32 * j < 2 ^ 64) (hk : 32 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (yAddr b j) 32 (yAddr b k) 32 := by
  intro x h₁ h₂
  simp only [yAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 32 * n < 2 ^ 64) :
    (⟨b, 32 * n⟩ : Region).Contains (yAddr b k) (256 / 8) := by
  simp only [Region.Contains, yAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loc_some {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some k) :
    m.base = c.base ∧ m.index = none ∧ m.disp = ((32 * k : Nat) : Int) ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    cases h
    obtain ⟨hi, hb, h0, hm, hlt⟩ := h1
    exact ⟨hb, hi, by omega, hlt⟩
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hi : m.index = none)
    (hd : m.disp = ((32 * k : Nat) : Int)) : s.ea m = yAddr (s.gpr b) k := by
  simp only [State.ea, hi, hb, hd, yAddr]
  congr 1

/-- The register after a `setV .l256`. -/
theorem ymm_setV (s : State) (d r : XReg) (lo hi : BitVec 128) :
    (s.setV .l256 d lo hi).ymm r = if r = d then hi ++ lo else s.ymm r := by
  simp only [State.ymm, State.setV]
  by_cases h : r = d <;> simp [h]

theorem split_eq (v : BitVec 256) : v.extractLsb' 128 128 ++ v.extractLsb' 0 128 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]

section
variable {D : Dom α 64} {R : Nat → α → BitVec 64 → Prop} {c : Cfg}

/-- The facts about one step, and so about a block: it writes no vector
register but `writes`, and no general-purpose register but `gwrites`. -/
structure Post (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e' : Env α) (s s' : State)
    (writes : XReg → Prop) (gwrites : Reg → Prop) : Prop where
  rel : Rel R c e' s'
  ok : Ok c s'
  base : s'.gpr c.base = s.gpr c.base
  gpr : ∀ r, ¬ gwrites r → s'.gpr r = s.gpr r
  cf : s'.cf = s.cf
  zf : s'.zf = s.zf
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  other : ∀ r, ¬ writes r → s'.ymm r = s.ymm r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : XReg → Prop} {G G' : Reg → Prop}
    (p : Post R c e' s s' W G) (h : ∀ r, W r → W' r) (hg : ∀ r, G r → G' r) :
    Post R c e' s s' W' G' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw),
           gpr := fun r hr => p.gpr r fun hw => hr (hg r hw) }

/-- The register after a `setV .l128`. -/
theorem ymm_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) :
    (s.setV .l128 d lo hi).ymm r = if r = d then (0 : BitVec 128) ++ lo else s.ymm r := by
  simp only [State.ymm, State.setV]
  by_cases h : r = d <;> simp [h]

/-- A register written by a `setV .l256` whose quadwords are related. -/
theorem post_setV {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : XReg} {a : α}
    {lo hi : BitVec 128} (hv : ∀ q < 4, R q a (qw (hi ++ lo) q)) :
    Post R c (e.setReg d a) s (s.setV .l256 d lo hi) (· = d) (fun _ => False) where
  rel := {
    reg := fun r b h q hq => by
      simp only [Env.setReg] at h
      rw [ymm_setV]
      split at h
      · rename_i hr; cases h; simp only [hr, ite_true]; exact hv q hq
      · rename_i hr; simp only [hr, ite_false]; exact hrel.reg r b h q hq
    slot := fun k b hk h q hq => by
      simpa [State.setV] using hrel.slot k b hk h q hq
    gc := fun r v h => by simpa [State.setV] using hrel.gc r v h
    xc := fun r v h => by
      simp only [Env.setReg] at h
      rw [ymm_setV]
      split at h
      · cases h
      · rename_i hr; simp only [hr, ite_false]; exact hrel.xc r v h }
  ok := hok.congr (by simp [State.setV]) (by simp [State.setV])
  base := by simp [State.setV]
  gpr _ _ := by simp [State.setV]
  cf := by simp [State.setV]
  zf := by simp [State.setV]
  rd := by simp [State.setV]
  wr := by simp [State.setV]
  other r hr := by rw [ymm_setV]; simp [hr]
  frame := by simp only [State.setV]; exact Frame.refl _ _

theorem qw_bcast (x : BitVec 64) {q : Nat} (hq : q < 4) : qw ((x ++ x) ++ (x ++ x)) q = x := by
  have e := qw_app (fun _ => x ++ x) hq
  rw [e, qword_app _ _ (Nat.mod_lt _ (by decide))]
  split <;> rfl

theorem qw_zero_app (lo : BitVec 128) : qw ((0 : BitVec 128) ++ lo) 0 = qword lo 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qw, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj,
    Bool.true_and, Nat.mul_zero, Nat.zero_add]
  simp [show j < 128 by omega]

theorem step_ok (hD : ∀ q < 4, D.Sound (R q)) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) {i : Instr} (h : step D c e i = some e') :
    ∃ s', exec i s = some s' ∧
      Post R c e' s s' (fun r => ydst i = some r) (fun r => i.dst = some r) := by
  cases i with
  | vop o =>
    cases o with
    | vbin op len d a b =>
      cases len with
      | l128 => simp [step] at h
      | l256 =>
        simp only [step] at h
        split at h
        · rename_i f x y hf hx hy
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          have hRx := hrel.reg a x hx
          have hRy := hrel.reg b y hy
          refine ⟨_, rfl, (post_setV hok hrel fun q hq => ?_).writes (fun r h => by simp [ydst, h])
            (fun _ h => h.elim)⟩
          have e := qw_app (fun l => op.sse.eval (s.lane a l) (s.lane b l)) hq
          rw [e]
          have hl : q % 2 < 2 := Nat.mod_lt _ (by decide)
          have ex := qw_ymm s a hq
          have ey := qw_ymm s b hq
          cases op <;> simp only [binop, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
            simp only [VBinOp.sse, XBinOp.eval]
          · rw [qword_xor, ← ex, ← ey]; exact (hD q hq).xor (hRx q hq) (hRy q hq) hr
          · rw [qword_or, ← ex, ← ey]; exact (hD q hq).or (hRx q hq) (hRy q hq) hr
          · rw [qword_and, ← ex, ← ey]; exact (hD q hq).and (hRx q hq) (hRy q hq) hr
          · rw [qword_andn _ _ hl, ← ex, ← ey]
            simp only [andn, Option.bind_eq_some_iff] at hr
            obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hr
            rw [← andn_eq]
            exact (hD q hq).and ((hD q hq).xor (hRx q hq) ((hD q hq).const ho) ht) (hRy q hq) hc
        · cases h
    | vmovdqa len d r =>
      cases len with
      | l128 => simp [step] at h
      | l256 =>
        simp only [step] at h
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, rfl, (post_setV hok hrel fun q hq => ?_).writes (fun r h => by simp [ydst, h])
          (fun _ h => h.elim)⟩
        rw [← State.ymm_eq]; exact hrel.reg r a ha q hq
    | vshift op len d r n =>
      cases len with
      | l128 => simp [step] at h
      | l256 =>
        simp only [step] at h
        split at h
        · rename_i hn
          refine ⟨_, rfl, ?_⟩
          have hl (q : Nat) : q % 2 < 2 := Nat.mod_lt _ (by decide)
          split at h
          · rename_i a ha
            obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
            refine (post_setV hok hrel fun q hq => ?_).writes (fun r h => by simp [ydst, h])
              (fun _ h => h.elim)
            have e := qw_app (fun l => XShiftOp.eval .psrlq (s.lane r l) n) hq
            rw [e, qword_psrlq _ (by omega) (hl q), ← qw_ymm s r hq]
            exact (hD q hq).shr (hrel.reg r a ha q hq) hb
          · rename_i a ha
            obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
            refine (post_setV hok hrel fun q hq => ?_).writes (fun r h => by simp [ydst, h])
              (fun _ h => h.elim)
            have e := qw_app (fun l => XShiftOp.eval .psllq (s.lane r l) n) hq
            rw [e, qword_psllq _ (by omega) (hl q), ← qw_ymm s r hq, ← shl_eq _ hn.1 hn.2]
            simp only [shl, Option.bind_eq_some_iff] at hb
            obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hb
            exact (hD q hq).ror ((hD q hq).and (hrel.reg r a ha q hq) ((hD q hq).const ho) ht) hc
          · cases h
        · cases h
    | vmovq d r =>
      simp only [step] at h
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
      have hg := hrel.gc r v hv
      refine ⟨_, rfl, ⟨⟨fun x b hx q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
        fun x w hw => ?_⟩, hok.congr (by simp [VOp.exec]) (by simp [VOp.exec]),
        by simp [VOp.exec], fun _ _ => by simp [VOp.exec], by simp [VOp.exec, State.setV],
        by simp [VOp.exec, State.setV], by simp [VOp.exec], by simp [VOp.exec],
        fun x hx => ?_, by simp only [VOp.exec_mem]; exact Frame.refl _ _⟩⟩
      · simp only at hx
        split at hx
        · cases hx
        · rename_i hxd
          simp only [VOp.exec, ymm_setV128, hxd, ite_false]
          exact hrel.reg x b hx q hq
      · simpa [VOp.exec] using hrel.slot k b hk hb q hq
      · simpa [VOp.exec] using hrel.gc r' w hw
      · simp only at hw
        simp only [VOp.exec, ymm_setV128]
        split at hw
        · rename_i hxd; cases hw; simp only [hxd, ite_true, qw_zero_app]
          rw [qword_app _ _ (by decide)]; simp [hg]
        · rename_i hxd; simp only [hxd, ite_false]; exact hrel.xc x w hw
      · simp only [ydst, Option.some.injEq] at hx
        simp only [VOp.exec, ymm_setV128, Ne.symm hx, ite_false]
    | vpbroadcastq len d x =>
      cases len with
      | l128 => simp [step] at h
      | l256 =>
        simp only [step, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, h⟩ := h
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        have hx := hrel.xc x v hv
        rw [qw_ymm s x (by decide)] at hx
        simp only [Nat.zero_div, Nat.zero_mod, State.lane, ite_true] at hx
        have hq4 : ∀ q < 4, qw ((qword (s.xmm x) 0 ++ qword (s.xmm x) 0) ++
            (qword (s.xmm x) 0 ++ qword (s.xmm x) 0)) q = v := fun q hq =>
          hx ▸ qw_bcast _ hq
        refine ⟨_, rfl, ⟨⟨fun r b hr q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
          fun r w hw => ?_⟩, hok.congr (by simp [VOp.exec]) (by simp [VOp.exec]),
          by simp [VOp.exec], fun _ _ => by simp [VOp.exec], by simp [VOp.exec, State.setV],
          by simp [VOp.exec, State.setV], by simp [VOp.exec], by simp [VOp.exec],
          fun r hr => ?_, by simp only [VOp.exec_mem]; exact Frame.refl _ _⟩⟩
        · simp only at hr
          simp only [VOp.exec, ymm_setV]
          split at hr
          · rename_i hrd; cases hr; simp only [hrd, ite_true, hq4 q hq]
            exact (hD q hq).const ha
          · rename_i hrd; simp only [hrd, ite_false]; exact hrel.reg r b hr q hq
        · simpa [VOp.exec] using hrel.slot k b hk hb q hq
        · simpa [VOp.exec] using hrel.gc r' w hw
        · simp only at hw
          simp only [VOp.exec, ymm_setV]
          split at hw
          · rename_i hrd; cases hw; simp only [hrd, ite_true, hq4 0 (by decide)]
          · rename_i hrd; simp only [hrd, ite_false]; exact hrel.xc r w hw
        · simp only [ydst, Option.some.injEq] at hr
          simp only [VOp.exec, ymm_setV, Ne.symm hr, ite_false]
    | _ => simp [step] at h
  | vmovdquLoad len d m =>
    cases len with
    | l128 => simp [step] at h
    | l256 =>
      simp only [step] at h
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
        have hea := ea_of (s := s) hb hi hd
        obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
        have hin : InRegions (s.rd ++ s.wr) (yAddr (s.gpr c.base) k) 32 :=
          ⟨r, List.mem_append_right _ hr, hc⟩
        let v := s.mem.readW (yAddr (s.gpr c.base) k) 256
        refine ⟨s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128),
          by simp [exec, State.load256, hea, hin, v], ?_⟩
        refine (post_setV hok hrel fun q hq => ?_).writes (fun r h => by simp [ydst, h])
          (fun _ h => h.elim)
        rw [split_eq]
        exact hrel.slot k a hlt ha q hq
      · cases h
  | vmovdquStore len m r =>
    cases len with
    | l128 => simp [step] at h
    | l256 =>
      simp only [step] at h
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
        have hea := ea_of (s := s) hb hi hd
        have hin := hok.slotIn k hlt
        refine ⟨{ s with mem := s.mem.writeW (yAddr (s.gpr c.base) k) (s.ymm r) },
          by simp [exec, State.store256, hea, hin], ?_⟩
        have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (yAddr (s.gpr c.base) j) (256 / 8)
            (yAddr (s.gpr c.base) k) (256 / 8) := fun j hj hjk =>
          slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
        refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_,
          fun r' w hw => hrel.gc r' w hw, fun r' w hw => hrel.xc r' w hw⟩,
          hok.congr rfl rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
        · simp only [Env.setSlot] at hjb
          split at hjb
          · rename_i hjk
            subst hjk
            rw [← Option.some.inj hjb]
            intro q hq
            have e := Mem.readW_writeW_self s.mem (yAddr (s.gpr c.base) j) 32 (s.ymm r) (by decide)
            simp only at e ⊢
            rw [e]
            exact hrel.reg r a ha q hq
          · rename_i hjk
            intro q hq
            simp only
            rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
            exact hrel.slot j b hj hjb q hq
        · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (slot_contains _ hlt hok.slots)
      · cases h
  | movImm64 d v =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hdb
      cases h
      refine ⟨s.setReg d v, rfl, ⟨⟨fun r b hr q hq => ?_, fun k b hk hb q hq => ?_,
        fun r w hw => ?_, fun r w hw => ?_⟩, hok.congr ?_ (by simp [State.setReg]), ?_,
        fun r hr => ?_, by simp [State.setReg], by simp [State.setReg], by simp [State.setReg],
        by simp [State.setReg], fun r _ => by simp [State.setReg, State.ymm], ?_⟩⟩
      · simpa [State.setReg, State.ymm] using hrel.reg r b hr q hq
      · simpa [State.setReg, Ne.symm hdb] using hrel.slot k b hk hb q hq
      · simp only at hw
        simp only [State.setReg]
        split at hw
        · rename_i hrd; cases hw; simp [hrd]
        · rename_i hrd; simp only [hrd, ite_false]; exact hrel.gc r w hw
      · simpa [State.setReg, State.ymm] using hrel.xc r w hw
      · simp [State.setReg, Ne.symm hdb]
      · simp [State.setReg, Ne.symm hdb]
      · simp only [Instr.dst, Option.some.injEq] at hr
        simp [State.setReg, Ne.symm hr]
      · simp only [State.setReg]; exact Frame.refl _ _
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : ∀ q < 4, D.Sound (R q)) {is : List Instr} {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c e s) (h : eval D c is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c e' s s' (fun r => (is.all fun i => ydst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
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
      p.base.trans p₁.base, fun r hr => ?_, p.cf.trans p₁.cf, p.zf.trans p₁.zf, p.rd.trans p₁.rd,
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
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 32 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    simp only [Region.Contains, yAddr, hb]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega⟩
  slots := by omega

end VG.X86_64.StraightY
