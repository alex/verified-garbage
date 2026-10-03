import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# x86-64: straight-line bitwise AVX-512 code, quadword lane by quadword lane

As `StraightY`, for 512-bit `zmm` registers and 64-byte slots: a block of
`vpxord`, `vpandq`, `vporq`, `vpandnq`, `vpternlogd`, `vmovdqa64`, quadword
shifts (`vpsllq`, `vpsrlq`) and `vmovdqu32` loads and stores of 64-byte
slots `[base + 64k]` computes each of the eight quadwords of its results from
the same quadword of its operands. `eval` runs it once over an abstract
domain on 64-bit words, and `run` relates quadword `q` of every register
and slot by `R q`, for each `q < 8`. `vpternlogd` (whose destination is also
its first input) is the disjunction of the minterms its immediate selects,
as the model defines it (`ternlog`), in the domain's operations. Masks are
made by `movabs`, `vmovq` and `vpbroadcastq` from known constants.
-/

namespace VG.X86_64.StraightZ

open VG.Bitslice
open VG.X86_64.StraightY (andn shl binop qword_xor qword_and qword_or qword_andn qword_app
  qword_psrlq qword_psllq andn_eq shl_eq cases4)

/-- Quadword `q` of a 512-bit word. -/
def qw (x : BitVec 512) (q : Nat) : BitVec 64 := x.extractLsb' (64 * q) 64

/-- The slots: `[base + 64k]` for `k < slots`, read and written. -/
structure Cfg where
  base : Reg
  slots : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots, the known constants of
general-purpose registers and of the low quadword of vector registers. -/
structure Env (α : Type) where
  reg : XReg → Option α
  slot : Nat → Option α
  gc : Reg → Option (BitVec 64) := fun _ => none
  xc : XReg → Option (BitVec 64) := fun _ => none

variable {α : Type}

def Env.setReg (e : Env α) (d : XReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r,
           xc := fun r => if r = d then none else e.xc r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

def Cfg.loc (c : Cfg) (m : MemOp) : Option Nat :=
  if m.index = none ∧ m.base = c.base ∧ 0 ≤ m.disp ∧ m.disp % 64 = 0 ∧ m.disp.toNat / 64 < c.slots
  then some (m.disp.toNat / 64) else none

/-- The register a vector instruction writes, if any. -/
def zdst : Instr → Option XReg
  | .zop (.zbin _ d _ _) | .zop (.vmovdqa64 d _) | .zop (.vshift _ d _ _)
  | .zop (.vpternlogd d _ _ _) | .zop (.vpbroadcastq d _) | .vop (.vmovq d _) => some d
  | .vmovdqu32Load d _ => some d
  | _ => none

section
variable (D : Dom α 64) (c : Cfg)

/-- `x` if `bit`, else `¬x`. -/
def selA (bit : Bool) (x : α) : Option α :=
  if bit then some x else (D.const (BitVec.allOnes 64)).bind (D.xor x)

/-- The ternary function `imm` of `a`, `b` and `c`, as `ternlog` computes it. -/
def tern (a b c : α) (imm : BitVec 8) : Option α :=
  (List.range 8).foldl (fun acc m => acc.bind fun t =>
    if imm.getLsbD m then
      (selA D (m.testBit 2) a).bind fun x => (selA D (m.testBit 1) b).bind fun y =>
        (selA D (m.testBit 0) c).bind fun z => (D.and x y).bind fun xy => (D.and xy z).bind (D.or t)
    else some t) (D.const 0)

def zbinop : ZBinOp → Option (α → α → Option α)
  | .vpxord => some D.xor
  | .vpandq => some D.and
  | .vporq => some D.or
  | .vpandnq => some (andn D)
  | _ => none

def step (e : Env α) : Instr → Option (Env α)
  | .zop (.zbin op d a b) =>
    match zbinop D op, e.reg a, e.reg b with
    | some f, some x, some y => (f x y).map (e.setReg d)
    | _, _, _ => none
  | .zop (.vpternlogd d a b imm) =>
    match e.reg d, e.reg a, e.reg b with
    | some x, some y, some z => (tern D x y z imm).map (e.setReg d)
    | _, _, _ => none
  | .zop (.vmovdqa64 d r) => (e.reg r).map (e.setReg d)
  | .zop (.vshift op d r n) =>
    if 1 ≤ n.toNat ∧ n.toNat ≤ 63 then
      match op, e.reg r with
      | .vpsrlq, some a => (D.shr n.toNat a).map (e.setReg d)
      | .vpsllq, some a => (shl D n.toNat a).map (e.setReg d)
      | _, _ => none
    else none
  | .vmovdqu32Load d m => match c.loc m with
    | some k => (e.slot k).map (e.setReg d)
    | none => none
  | .vmovdqu32Store m r => match c.loc m with
    | some k => (e.reg r).map (e.setSlot k)
    | none => none
  | .movImm64 d v => if d = c.base then none else
    some { e with gc := fun r => if r = d then some v else e.gc r }
  | .vop (.vmovq d r) => (e.gc r).map fun v =>
    { e with reg := fun x => if x = d then none else e.reg x,
             xc := fun x => if x = d then some v else e.xc x }
  | .zop (.vpbroadcastq d x) => (e.xc x).bind fun v => (D.const v).map fun a =>
    { e with reg := fun r => if r = d then some a else e.reg r,
             xc := fun r => if r = d then some v else e.xc r }
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

/-! ## Quadwords -/

theorem cases8 {q : Nat} (hq : q < 8) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega

theorem getLsbD_qw (x : BitVec 512) {q i : Nat} (hi : i < 64) :
    (qw x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qw, hi]

/-- A quadword of four lanes. -/
theorem qw_app4 (f : Nat → BitVec 128) {q : Nat} (hq : q < 8) :
    qw ((f 3 ++ f 2) ++ (f 1 ++ f 0)) q = qword (f (q / 2)) (q % 2) := by
  rcases cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [qw, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj,
      Bool.true_and, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul]
    split <;> (try split) <;> first | (exfalso; omega) | exact congrArg _ (by omega)

theorem split256 (v : BitVec 256) : v.extractLsb' 128 128 ++ v.extractLsb' 0 128 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]

theorem zmm_lanes (s : State) (r : XReg) :
    s.zmm r = (s.zlane r 3 ++ s.zlane r 2) ++ (s.zlane r 1 ++ s.zlane r 0) := by
  simp only [State.zmm, State.ymm, State.zlane, State.lane, Nat.reduceLT, ↓reduceIte,
    Nat.reduceSub, Nat.reduceMul, Nat.one_ne_zero]
  rw [split256]

/-- A quadword of a register is a quadword of one of its lanes. -/
theorem qw_zmm (s : State) (r : XReg) {q : Nat} (hq : q < 8) :
    qw (s.zmm r) q = qword (s.zlane r (q / 2)) (q % 2) := by
  rw [zmm_lanes]; exact qw_app4 (s.zlane r) hq

/-- The quadwords of a `setZ` result. -/
theorem qw_setZ (s : State) (d : XReg) (l0 l1 l2 l3 : BitVec 128) {q : Nat} (hq : q < 8) :
    qw ((s.setZ d l0 l1 l2 l3).zmm d) q =
      qword (VG.X86_64.pick4 l0 l1 l2 l3 (q / 2)) (q % 2) := by
  rw [qw_zmm _ _ hq, State.zlane_setZ _ _ _ _ _ _ _ (by omega)]
  simp

theorem zmm_setZ_other (s : State) {d r : XReg} (h : r ≠ d) (l0 l1 l2 l3 : BitVec 128) :
    (s.setZ d l0 l1 l2 l3).zmm r = s.zmm r := by
  simp [State.zmm, State.ymm, State.setZ, h]

theorem split_eq (v : BitVec 512) :
    (v.extractLsb' 384 128 ++ v.extractLsb' 256 128) ++
      ((v.extractLsb' 128 128 ++ v.extractLsb' 0 128)) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 256
  · by_cases h2 : i < 128
    · simp [h1, h2]
    · simp [h1, h2, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]
  · by_cases h3 : i - 256 < 128
    · simp [h1, h3, show 256 + (i - 256) = i by omega]
    · simp [h1, h3, show i - 256 - 128 < 128 by omega, show 384 + (i - 256 - 128) = i by omega]

/-- The register after a load of `v`. -/
theorem zmm_load (s : State) (d : XReg) (v : BitVec 512) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)).zmm d = v := by
  simp only [State.zmm, State.ymm, State.setZ, ite_true]
  exact split_eq v

/-- The ternary function of 64-bit words, as `ternlog` computes it on lanes. -/
def ternlog64 (a b c : BitVec 64) (imm : BitVec 8) : BitVec 64 :=
  let sel (bit : Bool) (x : BitVec 64) : BitVec 64 := if bit then x else ~~~x
  (List.range 8).foldl (fun acc m =>
    if imm.getLsbD m then acc ||| (sel (m.testBit 2) a &&& sel (m.testBit 1) b &&& sel (m.testBit 0) c)
    else acc) 0

theorem qword_not (a : BitVec 128) {i : Nat} (hi : i < 2) : qword (~~~a) i = ~~~qword a i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, decide_eq_true hj,
    Bool.true_and, decide_eq_true (show 64 * i + j < 128 by omega)]

theorem qword_zero (i : Nat) : qword 0 i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword]

theorem qword_sel (b : Bool) (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (if b then a else ~~~a) i = if b then qword a i else ~~~qword a i := by
  cases b <;> simp [qword_not _ hi]

theorem qword_ternlog (a b c : BitVec 128) (imm : BitVec 8) {i : Nat} (hi : i < 2) :
    qword (ternlog a b c imm) i = ternlog64 (qword a i) (qword b i) (qword c i) imm := by
  simp only [ternlog, ternlog64]
  have key : ∀ (l : List Nat) (acc : BitVec 128), qword (l.foldl (fun acc m =>
      if imm.getLsbD m then acc ||| ((if m.testBit 2 then a else ~~~a) &&&
        (if m.testBit 1 then b else ~~~b) &&& (if m.testBit 0 then c else ~~~c)) else acc) acc) i =
      l.foldl (fun acc m =>
      if imm.getLsbD m then acc ||| ((if m.testBit 2 then qword a i else ~~~qword a i) &&&
        (if m.testBit 1 then qword b i else ~~~qword b i) &&&
        (if m.testBit 0 then qword c i else ~~~qword c i)) else acc) (qword acc i) := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons m l ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      split
      · rw [qword_or, qword_and, qword_and, qword_sel _ _ hi, qword_sel _ _ hi, qword_sel _ _ hi]
      · rfl
  rw [key, qword_zero]

theorem selA_sound {D : Dom α 64} {R : α → BitVec 64 → Prop} (hD : D.Sound R) {bit : Bool} {a t : α}
    {x : BitVec 64} (ha : R a x) (h : selA D bit a = some t) :
    R t (if bit then x else ~~~x) := by
  cases bit
  · simp only [selA, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at h
    obtain ⟨o, ho, ht⟩ := h
    have := hD.xor ha (hD.const ho) ht
    rw [BitVec.xor_allOnes] at this
    simpa using this
  · simp only [selA, ite_true, Option.some.injEq] at h
    subst h; simpa using ha

theorem tern_sound {D : Dom α 64} {R : α → BitVec 64 → Prop} (hD : D.Sound R) {a b c t : α}
    {x y z : BitVec 64} (ha : R a x) (hb : R b y) (hc : R c z) (imm : BitVec 8)
    (h : tern D a b c imm = some t) : R t (ternlog64 x y z imm) := by
  simp only [tern, ternlog64] at h ⊢
  have key : ∀ (l : List Nat) (acc : Option α) (v : BitVec 64),
      (∀ t₀, acc = some t₀ → R t₀ v) → ∀ t',
      l.foldl (fun acc m => acc.bind fun t =>
        if imm.getLsbD m then
          (selA D (m.testBit 2) a).bind fun x => (selA D (m.testBit 1) b).bind fun y =>
            (selA D (m.testBit 0) c).bind fun z => (D.and x y).bind fun xy => (D.and xy z).bind (D.or t)
        else some t) acc = some t' →
      R t' (l.foldl (fun acc m =>
        if imm.getLsbD m then acc ||| ((if m.testBit 2 then x else ~~~x) &&&
          (if m.testBit 1 then y else ~~~y) &&& (if m.testBit 0 then z else ~~~z)) else acc) v) := by
    intro l
    induction l with
    | nil => intro acc v hacc t' h; exact hacc t' h
    | cons m l ih =>
      intro acc v hacc t' h
      simp only [List.foldl_cons] at h ⊢
      refine ih _ _ (fun t₀ h₀ => ?_) t' h
      rcases hac : acc with _ | t₁
      · rw [hac] at h₀; cases h₀
      · rw [hac] at h₀
        have hv := hacc t₁ hac
        simp only [Option.bind_some] at h₀
        split at h₀
        · rename_i hm
          simp only [hm, ite_true]
          simp only [Option.bind_eq_some_iff] at h₀
          obtain ⟨p, hp, q, hq, r, hr, s, hs, u, hu, ht⟩ := h₀
          exact hD.or hv (hD.and (hD.and (selA_sound hD ha hp) (selA_sound hD hb hq) hs)
            (selA_sound hD hc hr) hu) ht
        · rename_i hm
          simp only [hm, Bool.false_eq_true, ite_false]
          cases h₀; exact hv
  exact key _ _ 0 (fun t₀ h₀ => hD.const h₀) t h

/-! ## Relating abstract and machine states -/

abbrev zAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (64 * k)

structure Rel (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ∀ q < 8, R q a (qw (s.zmm r) q)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    ∀ q < 8, R q a (qw (s.mem.readW (zAddr (s.gpr c.base) k) 512) q)
  gc : ∀ r v, e.gc r = some v → s.gpr r = v
  xc : ∀ r v, e.xc r = some v → qw (s.zmm r) 0 = v

structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (zAddr (s.gpr c.base) k) 64
  slots : 64 * c.slots < 2 ^ 64

def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 64 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  slots := h.slots

theorem slot_sep (b : Addr) {j k : Nat} (hj : 64 * j < 2 ^ 64) (hk : 64 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (zAddr b j) 64 (zAddr b k) 64 := by
  intro x h₁ h₂
  simp only [zAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 64 * n < 2 ^ 64) :
    (⟨b, 64 * n⟩ : Region).Contains (zAddr b k) (512 / 8) := by
  simp only [Region.Contains, zAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loc_some {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some k) :
    m.base = c.base ∧ m.index = none ∧ m.disp = ((64 * k : Nat) : Int) ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    cases h
    obtain ⟨hi, hb, h0, hm, hlt⟩ := h1
    exact ⟨hb, hi, by omega, hlt⟩
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hi : m.index = none)
    (hd : m.disp = ((64 * k : Nat) : Int)) : s.ea m = zAddr (s.gpr b) k := by
  simp only [State.ea, hi, hb, hd, zAddr]
  congr 1

section
variable {D : Dom α 64} {R : Nat → α → BitVec 64 → Prop} {c : Cfg}

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
  other : ∀ r, ¬ writes r → s'.zmm r = s.zmm r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : XReg → Prop} {G G' : Reg → Prop}
    (p : Post R c e' s s' W G) (h : ∀ r, W r → W' r) (hg : ∀ r, G r → G' r) :
    Post R c e' s s' W' G' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw),
           gpr := fun r hr => p.gpr r fun hw => hr (hg r hw) }

/-- A register written by a `setZ` whose quadwords are related. -/
theorem post_setZ {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : XReg} {a : α}
    {l0 l1 l2 l3 : BitVec 128}
    (hv : ∀ q < 8, R q a (qword (VG.X86_64.pick4 l0 l1 l2 l3 (q / 2)) (q % 2))) :
    Post R c (e.setReg d a) s (s.setZ d l0 l1 l2 l3) (· = d) (fun _ => False) where
  rel := {
    reg := fun r b h q hq => by
      simp only [Env.setReg] at h
      split at h
      · rename_i hr; cases h; subst hr; rw [qw_setZ _ _ _ _ _ _ hq]; exact hv q hq
      · rename_i hr; rw [zmm_setZ_other _ hr]; exact hrel.reg r b h q hq
    slot := fun k b hk h q hq => by
      simpa [State.setZ] using hrel.slot k b hk h q hq
    gc := fun r v h => by simpa [State.setZ] using hrel.gc r v h
    xc := fun r v h => by
      simp only [Env.setReg] at h
      split at h
      · cases h
      · rename_i hr; rw [zmm_setZ_other _ hr]; exact hrel.xc r v h }
  ok := hok.congr (by simp [State.setZ]) (by simp [State.setZ])
  base := by simp [State.setZ]
  gpr _ _ := by simp [State.setZ]
  cf := by simp [State.setZ]
  zf := by simp [State.setZ]
  rd := by simp [State.setZ]
  wr := by simp [State.setZ]
  other r hr := zmm_setZ_other _ hr _ _ _ _
  frame := by simp only [State.setZ]; exact Frame.refl _ _

theorem pick4_f (f : Nat → BitVec 128) {q : Nat} (hq : q < 8) :
    VG.X86_64.pick4 (f 0) (f 1) (f 2) (f 3) (q / 2) = f (q / 2) :=
  VG.X86_64.pick4_lanes f (by omega)

theorem step_ok (hD : ∀ q < 8, D.Sound (R q)) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) {i : Instr} (h : step D c e i = some e') :
    ∃ s', exec i s = some s' ∧
      Post R c e' s s' (fun r => zdst i = some r) (fun r => i.dst = some r) := by
  cases i with
  | zop o =>
    cases o with
    | zbin op d a b =>
      simp only [step] at h
      split at h
      · rename_i f x y hf hx hy
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have hRx := hrel.reg a x hx
        have hRy := hrel.reg b y hy
        refine ⟨_, rfl, (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
          (fun _ h => h.elim)⟩
        rw [pick4_f (fun i => op.sse.eval (s.zlane a i) (s.zlane b i)) hq]
        have hl : q % 2 < 2 := Nat.mod_lt _ (by decide)
        have ex := qw_zmm s a hq
        have ey := qw_zmm s b hq
        cases op <;> simp only [zbinop, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
          simp only [ZBinOp.sse, XBinOp.eval]
        · rw [qword_xor, ← ex, ← ey]; exact (hD q hq).xor (hRx q hq) (hRy q hq) hr
        · rw [qword_and, ← ex, ← ey]; exact (hD q hq).and (hRx q hq) (hRy q hq) hr
        · rw [qword_or, ← ex, ← ey]; exact (hD q hq).or (hRx q hq) (hRy q hq) hr
        · rw [qword_andn _ _ hl, ← ex, ← ey]
          simp only [andn, Option.bind_eq_some_iff] at hr
          obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hr
          rw [← andn_eq]
          exact (hD q hq).and ((hD q hq).xor (hRx q hq) ((hD q hq).const ho) ht) (hRy q hq) hc
      · cases h
    | vpternlogd d a b imm =>
      simp only [step] at h
      split at h
      · rename_i x y z hx hy hz
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, rfl, (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
          (fun _ h => h.elim)⟩
        rw [pick4_f (fun i => ternlog (s.zlane d i) (s.zlane a i) (s.zlane b i) imm) hq,
          qword_ternlog _ _ _ _ (Nat.mod_lt _ (by decide)), ← qw_zmm s d hq, ← qw_zmm s a hq,
          ← qw_zmm s b hq]
        exact tern_sound (hD q hq) (hrel.reg d x hx q hq) (hrel.reg a y hy q hq)
          (hrel.reg b z hz q hq) imm hr
      · cases h
    | vmovdqa64 d r =>
      simp only [step] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, rfl, (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
        (fun _ h => h.elim)⟩
      rw [pick4_f (fun i => s.zlane r i) hq, ← qw_zmm s r hq]
      exact hrel.reg r a ha q hq
    | vshift op d r n =>
      simp only [step] at h
      split at h
      · rename_i hn
        refine ⟨_, rfl, ?_⟩
        have hl (q : Nat) : q % 2 < 2 := Nat.mod_lt _ (by decide)
        split at h
        · rename_i a ha
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          refine (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
            (fun _ h => h.elim)
          rw [pick4_f (fun i => ZShiftOp.vpsrlq.sse.eval (s.zlane r i) n) hq]
          simp only [ZShiftOp.sse]
          rw [qword_psrlq _ (by omega) (hl q), ← qw_zmm s r hq]
          exact (hD q hq).shr (hrel.reg r a ha q hq) hb
        · rename_i a ha
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          refine (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
            (fun _ h => h.elim)
          rw [pick4_f (fun i => ZShiftOp.vpsllq.sse.eval (s.zlane r i) n) hq]
          simp only [ZShiftOp.sse]
          rw [qword_psllq _ (by omega) (hl q), ← qw_zmm s r hq, ← shl_eq _ hn.1 hn.2]
          simp only [shl, Option.bind_eq_some_iff] at hb
          obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hb
          exact (hD q hq).ror ((hD q hq).and (hrel.reg r a ha q hq) ((hD q hq).const ho) ht) hc
        · cases h
      · cases h
    | vpbroadcastq d x =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have hx := hrel.xc x v hv
      rw [qw_zmm s x (by decide)] at hx
      simp only [Nat.zero_div, Nat.zero_mod, State.zlane, State.lane, ite_true,
        show (0 : Nat) < 2 by decide] at hx
      have hq8 : ∀ q < 8, qw (((ZOp.vpbroadcastq d x).exec s).zmm d) q = v := by
        intro q hq
        rw [qw_zmm _ _ hq, zlane_vpbroadcastq _ _ _ _ (by omega)]
        simp only [ite_true]
        rw [qword_app _ _ (Nat.mod_lt _ (by decide)), hx]
        split <;> rfl
      refine ⟨_, rfl, ⟨⟨fun r b hr q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
        fun r w hw => ?_⟩, hok.congr (by simp) (by simp),
        by simp, fun _ _ => by simp, by simp [ZOp.exec, State.setZ],
        by simp [ZOp.exec, State.setZ], by simp, by simp,
        fun r hr => ?_, by simp only [ZOp.exec_mem]; exact Frame.refl _ _⟩⟩
      · simp only at hr
        split at hr
        · rename_i hrd; cases hr; subst hrd; rw [hq8 q hq]; exact (hD q hq).const ha
        · rename_i hrd; simp only [ZOp.exec]; rw [zmm_setZ_other _ hrd]; exact hrel.reg r b hr q hq
      · simpa using hrel.slot k b hk hb q hq
      · simpa using hrel.gc r' w hw
      · simp only at hw
        split at hw
        · rename_i hrd; cases hw; subst hrd; exact hq8 0 (by decide)
        · rename_i hrd; simp only [ZOp.exec]; rw [zmm_setZ_other _ hrd]; exact hrel.xc r w hw
      · simp only [zdst, Option.some.injEq] at hr
        simp only [ZOp.exec]; rw [zmm_setZ_other _ (Ne.symm hr)]
    | _ => simp [step] at h
  | vop o =>
    cases o with
    | vmovq d r =>
      simp only [step] at h
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
      have hg := hrel.gc r v hv
      have other : ∀ x, x ≠ d → ((VOp.vmovq d r).exec s).zmm x = s.zmm x := by
        intro x hx; simp [VOp.exec, State.zmm, State.ymm, State.setV, hx]
      refine ⟨_, rfl, ⟨⟨fun x b hx q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
        fun x w hw => ?_⟩, hok.congr (by simp) (by simp),
        by simp, fun _ _ => by simp, by simp [VOp.exec, State.setV],
        by simp [VOp.exec, State.setV], by simp, by simp,
        fun x hx => other x (fun h => hx (by simp [zdst, h])),
        by simp only [VOp.exec_mem]; exact Frame.refl _ _⟩⟩
      · simp only at hx
        split at hx
        · cases hx
        · rename_i hxd; rw [other x hxd]; exact hrel.reg x b hx q hq
      · simpa using hrel.slot k b hk hb q hq
      · simpa using hrel.gc r' w hw
      · simp only at hw
        split at hw
        · rename_i hxd; cases hw; subst hxd
          rw [qw_zmm _ _ (by decide)]
          simp only [Nat.zero_div, Nat.zero_mod, State.zlane, State.lane, ite_true,
            show (0 : Nat) < 2 by decide, VOp.exec, State.setV]
          rw [qword_app _ _ (by decide)]; simp [hg]
        · rename_i hxd; rw [other x hxd]; exact hrel.xc x w hw
    | _ => simp [step] at h
  | vmovdqu32Load d m =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
      have hea := ea_of (s := s) hb hi hd
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (zAddr (s.gpr c.base) k) 64 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      let v := s.mem.readW (zAddr (s.gpr c.base) k) 512
      refine ⟨s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
        (v.extractLsb' 384 128), by simp [exec, State.load512, hea, hin, v], ?_⟩
      refine (post_setZ hok hrel fun q hq => ?_).writes (fun r h => by simp [zdst, h])
        (fun _ h => h.elim)
      have e := qw_setZ s d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
        (v.extractLsb' 384 128) hq
      rw [zmm_load] at e
      rw [← e]
      exact hrel.slot k a hlt ha q hq
    · cases h
  | vmovdqu32Store m r =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
      have hea := ea_of (s := s) hb hi hd
      have hin := hok.slotIn k hlt
      refine ⟨{ s with mem := s.mem.writeW (zAddr (s.gpr c.base) k) (s.zmm r) },
        by simp [exec, State.store512, hea, hin], ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (zAddr (s.gpr c.base) j) (512 / 8)
          (zAddr (s.gpr c.base) k) (512 / 8) := fun j hj hjk =>
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
          have e := Mem.readW_writeW_self s.mem (zAddr (s.gpr c.base) j) 64 (s.zmm r) (by decide)
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
        by simp [State.setReg], fun r _ => by simp [State.setReg, State.zmm, State.ymm], ?_⟩⟩
      · simpa [State.setReg, State.zmm, State.ymm] using hrel.reg r b hr q hq
      · simpa [State.setReg, Ne.symm hdb] using hrel.slot k b hk hb q hq
      · simp only at hw
        simp only [State.setReg]
        split at hw
        · rename_i hrd; cases hw; simp [hrd]
        · rename_i hrd; simp only [hrd, ite_false]; exact hrel.gc r w hw
      · simpa [State.setReg, State.zmm, State.ymm] using hrel.xc r w hw
      · simp [State.setReg, Ne.symm hdb]
      · simp [State.setReg, Ne.symm hdb]
      · simp only [Instr.dst, Option.some.injEq] at hr
        simp [State.setReg, Ne.symm hr]
      · simp only [State.setReg]; exact Frame.refl _ _
  | _ => simp [step] at h

theorem run (hD : ∀ q < 8, D.Sound (R q)) {is : List Instr} {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c e s) (h : eval D c is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c e' s s' (fun r => (is.all fun i => zdst i != some r) = false)
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
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 64 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    simp only [Region.Contains, zAddr, hb]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega⟩
  slots := by omega

end VG.X86_64.StraightZ
