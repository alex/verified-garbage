import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym

/-!
# X25519 on x86-64 with AVX512_IFMA: straight-line vector code, lane by lane

Untrusted: everything here is checked by Lean. The vector code of
`vg_x25519_ifma` computes on the four quadwords (lanes) of `ymm` registers,
and loads and stores 32 bytes at constant offsets from the working space
(`rdi`). `Sym.run` computes each quadword after a block of such
instructions as a term (`T`) in the quadwords, general-purpose registers and
memory before it, and the stores as a list of terms; `srun_ok` proves the
machine agrees. The quadword lemmas of the instructions are Poly1305's
(`Proof/Poly1305/X86_64/Avx2/Sym.lean`), with those of `vpsubq`, `vpxor`,
`vpmadd52luq`, `vpmadd52huq` and `vperm2i128` added here.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qw qword_app0 qword_app1 qword_and
  qword_or qword_paddq qword_punpcklqdq qword_punpckhqdq qword_psllq qword_psrlq pick2
  qword_blendDwords qword256_eq qword256_ymm sel4 sel4_lt qw_setV256 qw_setV128 qw_lane lane_sel
  qw_vbin qw_vshift qw_vmovdqa qw_vpblendd qw_vpbroadcastq qw_vmovq qw_vpermq mod2_lt hv_of)

/-! ## Quadwords of the instructions added here -/

theorem qword_psubq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .psubq x y) i = qword x i - qword y i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

/-- The 52-bit multiply-add of `vpmadd52luq` (`h = false`) and `vpmadd52huq`
on one quadword. -/
def mad52 (h : Bool) (c a b : BitVec 64) : BitVec 64 :=
  let t : BitVec 128 := (a.extractLsb' 0 52).setWidth 128 * (b.extractLsb' 0 52).setWidth 128
  c + (if h then t.extractLsb' 52 52 else t.extractLsb' 0 52).setWidth 64

theorem qword_madd52 (h : Bool) (d a b : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (madd52 h d a b) i = mad52 h (qword d i) (qword a i) (qword b i) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [madd52, qword_app0, qword_app1] <;>
    rfl

theorem mad52_toNat (h : Bool) (c a b : BitVec 64) :
    (mad52 h c a b).toNat = (c.toNat + (if h then a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52
      else a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) % 2 ^ 52)) % 2 ^ 64 := by
  have ha : a.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hb : b.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hp : a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by decide)) (by decide)
  have hq : a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52 < 2 ^ 52 :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by decide))
      (by decide))
  have e : ∀ x : BitVec 64, (x.extractLsb' 0 52).toNat = x.toNat % 2 ^ 52 := fun x => by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have h1 : a.toNat % 2 ^ 52 % 2 ^ 128 = a.toNat % 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  have h2 : b.toNat % 2 ^ 52 % 2 ^ 128 = b.toNat % 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  cases h
  · simp only [mad52, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_mul, e, h1, h2, Nat.mod_eq_of_lt hp]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide) :
      a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) % 2 ^ 52 < 2 ^ 64)]
  · simp only [mad52, ite_true, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
      BitVec.toNat_mul, e, Nat.shiftRight_eq_div_pow, h1, h2, Nat.mod_eq_of_lt hp]
    rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hq (by decide) :
      a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52 < 2 ^ 64)]

theorem qw_madd52 (h : Bool) (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((if h then VOp.vpmadd52huq .l256 d a b else VOp.vpmadd52luq .l256 d a b).exec s) r k =
      if r = d then mad52 h (qw s d k) (qw s a k) (qw s b k) else qw s r k := by
  have e : (if h then VOp.vpmadd52huq .l256 d a b else VOp.vpmadd52luq .l256 d a b).exec s =
      s.setV .l256 d (madd52 h (s.lane d 0) (s.lane a 0) (s.lane b 0))
        (madd52 h (s.lane d 1) (s.lane a 1) (s.lane b 1)) := by
    cases h <;> rfl
  rw [e, qw_setV256]
  split
  · have e2 : (if k / 2 = 0 then madd52 h (s.lane d 0) (s.lane a 0) (s.lane b 0)
        else madd52 h (s.lane d 1) (s.lane a 1) (s.lane b 1)) =
        madd52 h (s.lane d (k / 2)) (s.lane a (k / 2)) (s.lane b (k / 2)) := by
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e2, qword_madd52 _ _ _ _ (mod2_lt k), qw_lane, qw_lane, qw_lane]
  · rfl

theorem qw_lo (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpmadd52luq .l256 d a b).exec s) r k =
      if r = d then mad52 false (qw s d k) (qw s a k) (qw s b k) else qw s r k :=
  qw_madd52 false s d a b r hk

theorem qw_hi (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpmadd52huq .l256 d a b).exec s) r k =
      if r = d then mad52 true (qw s d k) (qw s a k) (qw s b k) else qw s r k :=
  qw_madd52 true s d a b r hk

/-- `vperm2i128 d, a, b, 0x20` (`hi = false`: the low lanes of `a` and `b`)
and `0x31` (the high lanes). -/
def p2imm (hi : Bool) : BitVec 8 := if hi then 0x31 else 0x20

theorem qw_vperm2i128 (s : State) (d a b r : XReg) (hi : Bool) {k : Nat} (hk : k < 4) :
    qw ((VOp.vperm2i128 d a b (p2imm hi)).exec s) r k =
      if r = d then (if k < 2 then qw s a (if hi then k + 2 else k)
        else qw s b (if hi then k else k - 2)) else qw s r k := by
  simp only [VOp.exec, qw_setV256]
  split
  · cases hi <;> rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive T
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  | zero
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : T)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : T)
  /-- Quadword `k` of the 32 bytes at `rdi + d`. -/
  | ld (d : Nat)
  | add (a b : T)
  | sub (a b : T)
  | and (a b : T)
  | xor (a b : T)
  | or (a b : T)
  | shl (a : T) (n : Nat)
  | shr (a : T) (n : Nat)
  | unpl (a b : T)
  | unph (a b : T)
  | perm (a : T) (o : Nat)
  | blend (a b : T) (sel : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : T)
  /-- `vperm2i128` with `p2imm hi`. -/
  | p2 (a b : T) (hi : Bool)
  /-- `a` in quadwords 0 and 1, zero in the others (`vzeroupper`). -/
  | low (a : T)
  deriving DecidableEq, Repr

def T.eval (s₀ : State) : T → Nat → BitVec 64
  | .reg r, k => qw s₀ (xr r) k
  | .gpr r, _ => s₀.gpr r
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld d, k => s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .sub a b, k => a.eval s₀ k - b.eval s₀ k
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .xor a b, k => a.eval s₀ k ^^^ b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .blend a b sel, k => pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .p2 a b hi, k => if k < 2 then a.eval s₀ (if hi then k + 2 else k)
    else b.eval s₀ (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.eval s₀ k else 0

/-- The 256 bits of four quadwords. -/
def T.val (s₀ : State) (t : T) : BitVec 256 :=
  t.eval s₀ 3 ++ t.eval s₀ 2 ++ t.eval s₀ 1 ++ t.eval s₀ 0

/-! ## The machine -/

/-- The terms of the vector registers (by number), and the stores so far
(offset and term), the last first. -/
structure Sym where
  reg : Nat → T
  st : List (Nat × T)

def Sym.init : Sym := ⟨.reg, []⟩

def Sym.set (σ : Sym) (d : XReg) (t : T) : Sym := { σ with reg := fun r => if r = xi d then t else σ.reg r }

def Sym.bin (σ : Sym) (op : VBinOp) (d a b : XReg) : Option Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpsubq => some (σ.set d (.sub A B))
  | .vpand => some (σ.set d (.and A B))
  | .vpxor => some (σ.set d (if a = b then .zero else .xor A B))
  | .vpor => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.shift (σ : Sym) (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Option Sym :=
  if n.toNat < 64 then
    match op with
    | .psllq => some (σ.set d (.shl (σ.reg (xi a)) n.toNat))
    | .psrlq => some (σ.set d (.shr (σ.reg (xi a)) n.toNat))
    | _ => none
  else none

def Sym.vop (σ : Sym) : VOp → Option Sym
  | .vbin op .l256 d a b => σ.bin op d a b
  | .vshift op .l256 d a n => σ.shift op d a n
  | .vmovdqa .l256 d a => some (σ.set d (σ.reg (xi a)))
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (xi a)) (σ.reg (xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vmovq d r => some (σ.set d (.lane0 (.gpr r)))
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (xi a)) o.toNat))
  | .vpmadd52luq .l256 d a b =>
    some (σ.set d (.mad false (σ.reg (xi d)) (σ.reg (xi a)) (σ.reg (xi b))))
  | .vpmadd52huq .l256 d a b =>
    some (σ.set d (.mad true (σ.reg (xi d)) (σ.reg (xi a)) (σ.reg (xi b))))
  | .vperm2i128 d a b sel =>
    if sel = p2imm false then some (σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) false))
    else if sel = p2imm true then some (σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) true))
    else none
  | .vzeroupper => some { σ with reg := fun r => .low (σ.reg r) }
  | _ => none

/-- The offset of `[rdi + d]`. -/
def rdiOff (m : MemOp) : Option Nat :=
  if m.base = .rdi ∧ m.index = none then
    match m.disp with
    | .ofNat n => some n
    | _ => none
  else none

/-- Whether the 32 bytes at `d` miss every store. -/
def Sym.fresh (σ : Sym) (d : Nat) : Bool := σ.st.all fun (e, _) => d + 32 ≤ e || e + 32 ≤ d

/-- One instruction. Loads read only what no store wrote. -/
def Sym.step (σ : Sym) : Instr → Option Sym
  | .vop o => σ.vop o
  | .vmovdquLoad .l256 d m => (rdiOff m).bind fun o =>
    if o + 32 ≤ 4096 ∧ σ.fresh o then some (σ.set d (.ld o)) else none
  | .vmovdquStore .l256 m r => (rdiOff m).bind fun o =>
    if o + 32 ≤ 4096 then some { σ with st := (o, σ.reg (xi r)) :: σ.st } else none
  | _ => none

def Sym.run (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step i).bind fun σ' => σ'.run is

/-! ## The machine agrees -/

/-- The stores `st` (the last first) applied to `m`, at `base + d`. -/
def stores (s₀ : State) (base : Addr) : List (Nat × T) → Mem → Mem
  | [], m => m
  | (d, t) :: st, m => (stores s₀ base st m).writeW (base + BitVec.ofNat 64 d) (t.val s₀)

/-- `s₀` with the vector registers and memory of `s`. -/
def vm (s₀ s : State) : State := { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, mem := s.mem }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and the stores of `σ`. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qw s r k = (σ.reg (xi r)).eval s₀ k
  eq : vm s₀ s = s
  mem : s.mem = stores s₀ (s₀.gpr .rdi) σ.st s₀.mem

theorem SRel.gpr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem SRel.rd {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by
  rw [← h.eq]; rfl
theorem SRel.flags {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, T.eval, xr_xi], rfl, rfl⟩

theorem vm_vop {s₀ s : State} (h : vm s₀ s = s) (o : VOp) : vm s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vm_setV {s₀ s : State} (h : vm s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vm s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem SRel.set {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {d : XReg} {t : T} {s' : State}
    (hv : ∀ r k, k < 4 → qw s' r k = if r = d then t.eval s₀ k else qw s r k)
    (he : vm s₀ s' = s') (hm : s'.mem = s.mem) : SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he, hm.trans h.mem⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- The working space the code may load from and store to: every offset
`d` of a load or store is readable and writable at `rdi + d`. -/
def Ctx (s₀ : State) : Prop :=
  ∀ d, d + 32 ≤ 4096 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 d) 32

theorem rdiOff_ok {m : MemOp} {o : Nat} (h : rdiOff m = some o) (s : State) :
    s.ea m = s.gpr .rdi + BitVec.ofNat 64 o := by
  unfold rdiOff at h
  split at h
  · rename_i hb
    split at h
    · rename_i n hn
      cases h
      simp only [State.ea, hb.1, hb.2, hn]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    · cases h
  · cases h

theorem eq_of_qword256 {x y : BitVec 256} (h : ∀ k < 4, qword256 x k = qword256 y k) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun v => v.getLsbD (j % 64)) (h (j / 64) (by omega))
  simp only [qword256, BitVec.getLsbD_extractLsb', show j % 64 < 64 by omega, decide_true,
    Bool.true_and, show 64 * (j / 64) + j % 64 = j by omega] at this
  exact this

theorem ymm_eq_qw (s : State) (r : XReg) :
    s.ymm r = qw s r 3 ++ qw s r 2 ++ qw s r 1 ++ qw s r 0 := by
  refine eq_of_qword256 fun k hk => ?_
  rw [qword256_ymm _ _ hk, VG.Proof.Poly1305.X86_64.Avx2.qword256_cat _ _ _ _ hk]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- A read of the 32 bytes at `d` that miss every store. -/
theorem stores_fresh (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × T)) {d : Nat}, d < 2 ^ 62 → (∀ e ∈ st, e.1 < 2 ^ 62) →
      (st.all fun (e, _) => d + 32 ≤ e || e + 32 ≤ d) = true →
      (stores s₀ base st m).readW (base + BitVec.ofNat 64 d) 256 = m.readW (base + BitVec.ofNat 64 d) 256
  | [], _, _, _, _ => rfl
  | (e, t) :: st, d, hd, he, hf => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    have e1 := readW_writeW_off (stores s₀ base st m) base (t.val s₀) (d := d) (e := e) (n := 32)
      (by omega) (by have := he _ (List.mem_cons_self ..); simp at this; omega) (by omega)
    have e2 := stores_fresh s₀ base m st hd (fun x hx => he x (List.mem_cons_of_mem _ hx)) hf.2
    exact e1.trans e2

theorem qw_load' (s : State) (d r : XReg) (a : Addr) (v : BitVec 256) (hv : v = s.mem.readW a 256)
    {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qw s r k := by
  subst hv; exact VG.Proof.Poly1305.X86_64.Avx2.qw_load s d r a hk

/-- Offsets are small. -/
def Sym.small (σ : Sym) : Prop := ∀ e ∈ σ.st, e.1 < 4096

theorem sstep_ok {s₀ : State} (hc : Ctx s₀) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) (hs : σ.small) {i : Instr} (e : σ.step i = some σ') :
    ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' ∧ σ'.small := by
  have hR : ∀ a k, k < 4 → (σ.reg (xi a)).eval s₀ k = qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := vm_vop h.eq o
    have hm : (o.exec s).mem = s.mem := VOp.exec_mem o s
    unfold Sym.vop at e
    split at e
    · rename_i op d a b
      unfold Sym.bin at e
      split at e <;> cases e <;>
        refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hm,
          hs⟩ <;>
        rw [qw_vbin, ite_eq_left rfl] <;> simp only [VBinOp.sse, T.eval]
      · rw [qword_paddq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [qword_psubq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_and, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_xor, qw_lane, qw_lane]
        split
        · subst_vars; simp [T.eval]
        · rw [T.eval, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_or, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, qw, h0]
        · rw [hR b (k - 1) (by omega), qw, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), qw, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, qw, show k % 2 = 1 by omega]
    · rename_i op d a n
      unfold Sym.shift at e
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vshift, ite_eq_right hr]))
            he hm, hs⟩ <;>
          rw [qw_vshift, ite_eq_left rfl] <;> simp only [T.eval]
        · rw [qword_psllq _ hn (mod2_lt k), qw_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), qw_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact ⟨h.set (hv_of (fun k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b n
      cases e
      exact ⟨h.set (hv_of (fun k hk => by
          rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a
      cases e
      exact ⟨h.set (hv_of (fun k _ => by rw [qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [qw_vpbroadcastq, ite_eq_right hr])) he hm, hs⟩
    · rename_i d g
      cases e
      exact ⟨h.set (hv_of (fun k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval, h.gpr])
        (fun r hr k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a o
      cases e
      exact ⟨h.set (hv_of (fun k hk => by
          rw [qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR a _ (sel4_lt _ _)])
        (fun r hr k hk => by rw [qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b
      cases e
      have q := fun r k (hk : k < 4) => qw_lo s d a b r hk
      exact ⟨h.set (hv_of (fun k hk => by
          rw [q d k hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR d k hk, hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [q r k hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b
      cases e
      have q := fun r k (hk : k < 4) => qw_hi s d a b r hk
      exact ⟨h.set (hv_of (fun k hk => by
          rw [q d k hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR d k hk, hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [q r k hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b sel
      have p2ok : ∀ hi, sel = p2imm hi → σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) hi) = σ' →
          SRel σ' s₀ ((VOp.vperm2i128 d a b sel).exec s) ∧ σ'.small := by
        intro hi hs' e'
        subst hs' e'
        refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by
          rw [qw_vperm2i128 _ _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
        rw [qw_vperm2i128 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]
        split
        · rw [hR a _ (by split <;> omega)]
        · rw [hR b _ (by split <;> omega)]
      split at e
      · rename_i h0; cases e; exact p2ok false h0 rfl
      · split at e
        · rename_i h1; cases e; exact p2ok true h1 rfl
        · cases e
    · cases e
      refine ⟨⟨fun r k hk => ?_, he, hm.trans h.mem⟩, hs⟩
      simp only [T.eval]
      simp only [VOp.exec, qw, State.lane]
      rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp [hR] <;> rfl
    · cases e
  · rename_i d m
    obtain ⟨o, ho, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hf
    cases e
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 o) 32 := by
      rw [h.wr]
      obtain ⟨r, hr, hc⟩ := hc o (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine ⟨s.setV .l256 d ((s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 o) 256).extractLsb' 0 128)
      ((s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 o) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_, hs⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qw_load' _ _ _ _ _ rfl hk, ite_eq_right hr]))
      (vm_setV h.eq _ _ _ _) rfl
    rw [qw_load' _ _ _ _ _ rfl hk, ite_eq_left rfl]
    simp only [T.eval]
    have r1 := readW_extract s.mem (s₀.gpr .rdi + BitVec.ofNat 64 o) (w := 256) (k := 8 * k) (n := 8)
      (by omega)
    have r2 := readW_extract s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 o) (w := 256) (k := 8 * k) (n := 8)
      (by omega)
    rw [h.mem, stores_fresh _ _ _ _ (by omega) (fun e he => by have := hs e he; omega) hf.2] at r1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at r2
    rw [h.mem]
    exact r1.symm.trans r2
  · rename_i m r
    obtain ⟨o, ho, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, h.gpr]
    have hin : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 o) 32 := by
      rw [h.wr]; exact hc o (by omega)
    have hy : s.ymm r = (σ.reg (xi r)).val s₀ := by
      rw [ymm_eq_qw, T.val, h.reg r 3 (by decide), h.reg r 2 (by decide), h.reg r 1 (by decide),
        h.reg r 0 (by decide)]
    refine ⟨{ s with mem := s.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 o) (s.ymm r) },
      by simp only [exec, ea, State.store256, hin, ite_true], ⟨fun r' k hk => h.reg r' k hk, ?_, ?_⟩,
      fun e he => ?_⟩
    · rw [← h.eq]; rfl
    · simp only [stores, hy, h.mem]
    · simp only [List.mem_cons] at he
      rcases he with rfl | he
      · simp only; omega
      · exact hs e he
  · cases e

/-- A block of instructions. -/
theorem srun_ok {s₀ : State} (hc : Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.small → σ.run is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, _, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, hs, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁, hs₁⟩ := sstep_ok hc h hs e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ hs₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {s₀ : State} (hc : Ctx s₀) {is : List Instr} {σ : Sym}
    (e : Sym.init.run is = some σ) : WP isa (.block is) s₀ (SRel σ s₀) :=
  srun_ok hc is (SRel.init s₀) (fun _ h => by cases h) e

end VG.Proof.X25519.X86_64.Ifma
