import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# AArch64: interleaving independent code

Untrusted: everything here is checked by Lean. Each instruction of a class
(the scalar arithmetic, loads and stores at `[x3, #off]`, and the AdvSIMD
arithmetic, permutations and multiplications) has a *footprint*: the
registers, vector registers and bytes (at offsets from `x3`) it may read and
write, and whether it reads or writes the carry. Two instructions whose
footprints are independent (neither writes what the other reads or writes)
commute (`exec_comm`), so any interleaving of two blocks whose footprints are
independent runs as the first block and then the second (`run_merge`).
Independence is checked on the union of each block's footprints, by
evaluation (`Fp.indep`): register sets and byte sets are bit masks.
-/

namespace VG.AArch64.Interleave

open VG

/-- Bit `r` of a register mask. -/
def gbit (r : Reg) : Nat := 2 ^ r.ctorIdx
/-- Bit `r` of a vector register mask. -/
def vbit (r : VReg) : Nat := 2 ^ r.ctorIdx
/-- The bytes `[off, off + n)`. -/
def range (off n : Nat) : Nat := (2 ^ n - 1) * 2 ^ off

/-- What an instruction may read and write: registers and vector registers
by `ctorIdx`, memory by byte offset from `x3`. -/
structure Fp where
  gr : Nat
  gw : Nat
  vr : Nat
  vw : Nat
  cr : Bool
  cw : Bool
  mr : Nat
  mw : Nat
  deriving DecidableEq, Repr

def Fp.empty : Fp := ⟨0, 0, 0, 0, false, false, 0, 0⟩

def Fp.union (a b : Fp) : Fp :=
  ⟨a.gr ||| b.gr, a.gw ||| b.gw, a.vr ||| b.vr, a.vw ||| b.vw, a.cr || b.cr, a.cw || b.cw,
    a.mr ||| b.mr, a.mw ||| b.mw⟩

/-- Neither writes what the other reads or writes, and neither writes `x3`. -/
def Fp.indep (a b : Fp) : Bool :=
  (a.gw &&& (b.gr ||| b.gw)) == 0 && (b.gw &&& a.gr) == 0 &&
  (a.vw &&& (b.vr ||| b.vw)) == 0 && (b.vw &&& a.vr) == 0 &&
  !(a.cw && (b.cr || b.cw)) && !(b.cw && a.cr) &&
  (a.mw &&& (b.mr ||| b.mw)) == 0 && (b.mw &&& a.mr) == 0 &&
  !(a.gw.testBit Reg.x3.ctorIdx) && !(b.gw.testBit Reg.x3.ctorIdx) &&
  a.mr >>> 65536 == 0 && a.mw >>> 65536 == 0 && b.mr >>> 65536 == 0 && b.mw >>> 65536 == 0

def regFp (r w : Nat) : Fp := ⟨r, w, 0, 0, false, false, 0, 0⟩
def vecFp (r w : Nat) : Fp := ⟨0, 0, r, w, false, false, 0, 0⟩

def VOp.fp : VOp → Option Fp
  | .mov d n => some (vecFp (vbit n) (vbit d))
  | .movi0 d => some (vecFp 0 (vbit d))
  | .dup _ d n => some ⟨gbit n, 0, 0, vbit d, false, false, 0, 0⟩
  | .logic _ d n m | .add _ d n m | .sub _ d n m | .ext d n m _ | .perm _ _ d n m
  | .umull _ d n m => some (vecFp (vbit n ||| vbit m) (vbit d))
  | .shift _ _ d n _ => some (vecFp (vbit d ||| vbit n) (vbit d))
  | .umlal _ d n m => some (vecFp (vbit d ||| vbit n ||| vbit m) (vbit d))
  | _ => none

/-- The footprint of an instruction of the class, `none` for any other. -/
def fp : Instr → Option Fp
  | .add _ d n m | .sub _ d n m | .logic _ _ d n m | .extr _ d n m _ | .mul _ d n m
  | .umulh d n m => some (regFp (gbit n ||| gbit m) (gbit d))
  | .adds _ d n m | .subs _ d n m => some ⟨gbit n ||| gbit m, gbit d, 0, 0, false, true, 0, 0⟩
  | .adcs _ d n m | .sbcs _ d n m => some ⟨gbit n ||| gbit m, gbit d, 0, 0, true, true, 0, 0⟩
  | .adc _ d n m | .sbc _ d n m => some ⟨gbit n ||| gbit m, gbit d, 0, 0, true, false, 0, 0⟩
  | .addImm _ d n _ | .subImm _ d n _ | .lsr _ d n _ | .lsl _ d n _ =>
    some (regFp (gbit n) (gbit d))
  | .madd _ d n m a => some (regFp (gbit n ||| gbit m ||| gbit a) (gbit d))
  | .movz _ d _ _ => some (regFp 0 (gbit d))
  | .movk _ d _ _ => some (regFp (gbit d) (gbit d))
  | .ldr sz t n off =>
    if n = .x3 then some ⟨gbit .x3, gbit t, 0, 0, false, false, range off sz.bytes, 0⟩ else none
  | .str sz t n off =>
    if n = .x3 then some ⟨gbit .x3 ||| gbit t, 0, 0, 0, false, false, 0, range off sz.bytes⟩ else none
  | .ldrq t n off =>
    if n = .x3 then some ⟨gbit .x3, 0, 0, vbit t, false, false, range off 16, 0⟩ else none
  | .strq t n off =>
    if n = .x3 then some ⟨gbit .x3, 0, vbit t, 0, false, false, 0, range off 16⟩ else none
  | .vop op => VOp.fp op
  | _ => none

/-- The union of the footprints of a block, `none` if one is outside the class. -/
def blockFp : List Instr → Option Fp
  | [] => some .empty
  | i :: is => (fp i).bind fun a => (blockFp is).map fun b => a.union b

/-! ## What a footprint promises -/

/-- `s` and `t` agree on what `F` reads (and on `x3` and the regions). -/
structure Reads (F : Fp) (s t : State) : Prop where
  gpr : ∀ r : Reg, F.gr.testBit r.ctorIdx → s.gpr r = t.gpr r
  v : ∀ r : VReg, F.vr.testBit r.ctorIdx → s.v r = t.v r
  c : F.cr → s.c = t.c
  x3 : s.gpr .x3 = t.gpr .x3
  mem : ∀ o, F.mr.testBit o → s.mem (s.gpr .x3 + BitVec.ofNat 64 o) = t.mem (s.gpr .x3 + BitVec.ofNat 64 o)
  rd : s.rd = t.rd
  wr : s.wr = t.wr

/-- `s'` and `t'` agree on what `F` writes. -/
structure Writes (F : Fp) (s' t' : State) : Prop where
  gpr : ∀ r : Reg, F.gw.testBit r.ctorIdx → s'.gpr r = t'.gpr r
  v : ∀ r : VReg, F.vw.testBit r.ctorIdx → s'.v r = t'.v r
  c : F.cw → s'.c = t'.c
  mem : ∀ o, F.mw.testBit o → s'.mem (s'.gpr .x3 + BitVec.ofNat 64 o) = t'.mem (s'.gpr .x3 + BitVec.ofNat 64 o)

/-- `s'` is `s` but for what `F` writes. -/
structure Frame (F : Fp) (s s' : State) : Prop where
  gpr : ∀ r : Reg, F.gw.testBit r.ctorIdx = false → s'.gpr r = s.gpr r
  v : ∀ r : VReg, F.vw.testBit r.ctorIdx = false → s'.v r = s.v r
  c : F.cw = false → s'.c = s.c
  mem : ∀ x, (∀ o, F.mw.testBit o → x ≠ s.gpr .x3 + BitVec.ofNat 64 o) → s'.mem x = s.mem x
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unknowns : s'.unknowns = s.unknowns


/-! ## Bits -/

theorem ctorIdx_inj {a b : Reg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]

theorem vctorIdx_inj {a b : VReg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← VReg.ofNat_ctorIdx a, h, VReg.ofNat_ctorIdx]

@[simp] theorem testBit_gbit (r q : Reg) : (gbit r).testBit q.ctorIdx = decide (q = r) := by
  rw [gbit, Nat.testBit_two_pow]
  by_cases h : q = r
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not]
    exact fun e => h (ctorIdx_inj e.symm)

@[simp] theorem testBit_vbit (r q : VReg) : (vbit r).testBit q.ctorIdx = decide (q = r) := by
  rw [vbit, Nat.testBit_two_pow]
  by_cases h : q = r
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not]
    exact fun e => h (vctorIdx_inj e.symm)

theorem testBit_range (off n o : Nat) : (range off n).testBit o = decide (off ≤ o ∧ o < off + n) := by
  rw [range, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : off ≤ o
  · have : o - off < n ↔ o < off + n := by omega
    simp [h, this]
  · simp [h]

/-! ## States -/

theorem state_ext {s t : State} (hg : s.gpr = t.gpr) (hsp : s.sp = t.sp) (hc : s.c = t.c)
    (hv : s.v = t.v) (hm : s.mem = t.mem) (hrd : s.rd = t.rd) (hwr : s.wr = t.wr)
    (hu : s.unknowns = t.unknowns) : s = t := by
  cases s; cases t; simp only at hg hsp hc hv hm hrd hwr hu; subst hg hsp hc hv hm hrd hwr hu; rfl

theorem read_congr {m m' : Mem} {a : Addr} {n : Nat}
    (h : ∀ k < n, m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) : m.read a n = m'.read a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun k hk => by
      have := h (k + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this]

theorem write_frame (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr)
    (h : ∀ k < n, x ≠ a + BitVec.ofNat 64 k) : m.write a n v x = m x := by
  simp only [Mem.write]
  rw [ite_eq_right_iff.mpr fun hk => absurd (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_comm, BitVec.sub_add_cancel]) (h _ hk)]

theorem write_at (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) {k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    m.write a n v (a + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8 := by
  simp only [Mem.write]
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    ite_eq_left_iff.mpr fun h => absurd hk h]


/-! ## Frames of the instructions' effects -/

theorem Frame.write {F : Fp} {s : State} (sz : Size) (d : Reg) (v : BitVec sz.bits)
    (hd : F.gw.testBit d.ctorIdx = true) : Frame F s (s.write sz d v) where
  gpr r hr := by
    have : r ≠ d := fun e => by rw [e, hd] at hr; exact Bool.noConfusion hr
    simp only [State.write, this, ite_false]
  v _ _ := rfl
  c _ := rfl
  mem _ _ := rfl
  sp := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl

theorem Frame.awc {F : Fp} {s : State} (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool)
    (hd : F.gw.testBit d.ctorIdx = true) (hc : F.cw = true) : Frame F s (s.addWithCarry sz d a b c) where
  gpr r hr := (Frame.write (s := s) sz d (a + b + BitVec.ofNat sz.bits c.toNat) hd).gpr r hr
  v _ _ := rfl
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem _ _ := rfl
  sp := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl

theorem Frame.setV {F : Fp} {s : State} (d : VReg) (x : BitVec 128)
    (hd : F.vw.testBit d.ctorIdx = true) : Frame F s (s.setV d x) where
  gpr _ _ := rfl
  v r hr := by
    have : r ≠ d := fun e => by rw [e, hd] at hr; exact Bool.noConfusion hr
    simp only [State.setV, this, ite_false]
  c _ := rfl
  mem _ _ := rfl
  sp := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl

theorem Frame.store {F : Fp} {s s' : State} {off n : Nat} {v : BitVec (8 * n)}
    (hm : ∀ o, off ≤ o → o < off + n → F.mw.testBit o = true)
    (h : s.store (s.gpr .x3 + BitVec.ofNat 64 off) n v = some s') : Frame F s s' := by
  simp only [State.store] at h
  split at h
  · cases h
    exact {
      gpr := fun _ _ => rfl, v := fun _ _ => rfl, c := fun _ => rfl,
      mem := fun x hx => write_frame _ _ _ _ _ fun k hk e => hx (off + k) (hm _ (by omega) (by omega))
        (by rw [e, BitVec.add_assoc, BitVec.ofNat_add]),
      sp := rfl, rd := rfl, wr := rfl, unknowns := rfl }
  · cases h


theorem testBit_union_left {a b i : Nat} (h : a.testBit i = true) : (a ||| b).testBit i = true := by
  simp [Nat.testBit_or, h]

theorem testBit_union_right {a b i : Nat} (h : b.testBit i = true) : (a ||| b).testBit i = true := by
  simp [Nat.testBit_or, h]

theorem VOp.frame {op : VOp} {F : Fp} (hf : VOp.fp op = some F) {s s' : State}
    (he : (op.eval s).map (fun (p : VReg × BitVec 128) => s.setV p.1 p.2) = some s') : Frame F s s' := by
  cases op <;> simp only [VOp.fp, reduceCtorEq] at hf <;> cases hf <;>
    simp only [VOp.eval, Option.map_some, Option.some.injEq] at he
  all_goals first
    | (subst he; exact Frame.setV _ _ (by simp [vecFp]))
    | (split at he
       · simp only [Option.map_some, Option.some.injEq] at he
         subst he; exact Frame.setV _ _ (by simp [vecFp])
       · cases he)
    | (rename_i a _ _; cases a <;> simp only [Option.map_some, Option.some.injEq] at he <;> subst he <;>
        exact Frame.setV _ _ (by simp))

theorem frame {i : Instr} {F : Fp} (hf : fp i = some F) {s s' : State} (he : exec i s = some s') :
    Frame F s s' := by
  cases i <;> simp only [fp, reduceCtorEq] at hf
  case vop op => exact VOp.frame hf he
  all_goals first
    | (cases hf; simp only [exec, Option.some.injEq] at he; subst he
       first
       | exact Frame.write _ _ _ (by simp [regFp])
       | exact Frame.awc _ _ _ _ _ (by simp) rfl)
    | (cases hf; simp only [exec] at he; split at he
       · simp only [Option.some.injEq] at he; subst he; exact Frame.write _ _ _ (by simp [regFp])
       · cases he)
    | (split at hf
       · rename_i hn; subst hn; cases hf
         simp only [exec, addr] at he
         split at he
         · simp only [Option.bind_some] at he
           first
           | exact Frame.store (fun o h1 h2 => by simp [testBit_range]; omega) he
           | (simp only [State.load] at he
              split at he
              · simp only [Option.map_some, Option.some.injEq] at he; subst he
                first
                | exact Frame.write _ _ _ (by simp)
                | exact Frame.setV _ _ (by simp)
              · cases he)
         · cases he
       · cases hf)

/-! ## Reads determine writes -/

theorem Reads.symm {F : Fp} {s t : State} (h : Reads F s t) : Reads F t s where
  gpr r hr := (h.gpr r hr).symm
  v r hr := (h.v r hr).symm
  c hc := (h.c hc).symm
  x3 := h.x3.symm
  mem o ho := by rw [← h.x3]; exact (h.mem o ho).symm
  rd := h.rd.symm
  wr := h.wr.symm

theorem Writes.write {F : Fp} {s t : State} (sz : Size) (d : Reg) (v : BitVec sz.bits)
    (hF : ∀ r : Reg, F.gw.testBit r.ctorIdx → r = d) (hv : F.vw = 0) (hc : F.cw = false) (hm : F.mw = 0) :
    Writes F (s.write sz d v) (t.write sz d v) where
  gpr r hr := by rw [hF r hr]; simp only [State.write, ite_true]
  v r hr := by rw [hv] at hr; simp at hr
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem o ho := by rw [hm] at ho; simp at ho


theorem Writes.setV {F : Fp} {s t : State} (d : VReg) (x : BitVec 128)
    (hF : ∀ r : VReg, F.vw.testBit r.ctorIdx → r = d) (hg : F.gw = 0) (hc : F.cw = false) (hm : F.mw = 0) :
    Writes F (s.setV d x) (t.setV d x) where
  gpr r hr := by rw [hg] at hr; simp at hr
  v r hr := by rw [hF r hr]; simp only [State.setV, ite_true]
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem o ho := by rw [hm] at ho; simp at ho

theorem Writes.awc {F : Fp} {s t : State} (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool)
    (hF : ∀ r : Reg, F.gw.testBit r.ctorIdx → r = d) (hv : F.vw = 0) (hm : F.mw = 0) :
    Writes F (s.addWithCarry sz d a b c) (t.addWithCarry sz d a b c) where
  gpr r hr := by rw [hF r hr]; simp only [State.addWithCarry, State.write, ite_true]
  v r hr := by rw [hv] at hr; simp at hr
  c _ := rfl
  mem o ho := by rw [hm] at ho; simp at ho

/-- What two runs of a footprint's instruction from states that agree on its reads share. -/
def Det (i : Instr) (F : Fp) : Prop :=
  ∀ s t, Reads F s t → ∀ s', exec i s = some s' → ∃ t', exec i t = some t' ∧ Writes F s' t'

theorem only_gbit {d r : Reg} (h : (gbit d).testBit r.ctorIdx = true) : r = d := by simpa using h

theorem only_vbit {d r : VReg} (h : (vbit d).testBit r.ctorIdx = true) : r = d := by simpa using h


theorem load_congr {F : Fp} {s t : State} (h : Reads F s t) {off n : Nat}
    (hr : ∀ o, off ≤ o → o < off + n → F.mr.testBit o = true) :
    s.load (s.gpr .x3 + BitVec.ofNat 64 off) n = t.load (t.gpr .x3 + BitVec.ofNat 64 off) n := by
  simp only [State.load, ← h.x3, ← h.rd, ← h.wr]
  rw [read_congr (m' := t.mem) fun k hk => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.mem _ (hr _ (by omega) (by omega))]

theorem store_det {F : Fp} {s t : State} (h : Reads F s t) {off n : Nat} (v : BitVec (8 * n))
    (hn : n ≤ 16) (hw : ∀ o, F.mw.testBit o = true → off ≤ o ∧ o < off + n)
    (hg : F.gw = 0) (hv : F.vw = 0) (hc : F.cw = false) (s' : State)
    (he : s.store (s.gpr .x3 + BitVec.ofNat 64 off) n v = some s') :
    ∃ t', t.store (t.gpr .x3 + BitVec.ofNat 64 off) n v = some t' ∧ Writes F s' t' := by
  simp only [State.store] at he ⊢
  rw [← h.x3, ← h.wr]
  split at he
  · cases he
    rename_i hin
    refine ⟨_, by rw [ite_eq_left_iff.mpr fun h => absurd hin h], ?_⟩
    refine ⟨fun r hr => by rw [hg] at hr; simp at hr, fun r hr => by rw [hv] at hr; simp at hr,
      fun c => by rw [hc] at c; exact Bool.noConfusion c, fun o ho => ?_⟩
    · obtain ⟨h1, h2⟩ := hw o ho
      simp only
      rw [show s.gpr .x3 + BitVec.ofNat 64 o = (s.gpr .x3 + BitVec.ofNat 64 off) + BitVec.ofNat 64 (o - off) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h1]]
      rw [write_at _ _ _ _ (by omega) (by omega), write_at _ _ _ _ (by omega) (by omega)]
  · cases he



theorem VOp.det {op : VOp} {F : Fp} (hf : VOp.fp op = some F) {s t : State} (h : Reads F s t) :
    VOp.eval s op = VOp.eval t op := by
  have hv := h.v
  have hg := h.gpr
  cases op <;> simp only [VOp.fp, reduceCtorEq] at hf <;> cases hf
  case dup a d n => cases a <;> simp (disch := simp) only [VOp.eval, hg]
  all_goals simp (disch := simp [vecFp, Nat.testBit_or]) only [VOp.eval, hv]

theorem VOp.fp_shape {op : VOp} {F : Fp} (hf : VOp.fp op = some F) : F.gw = 0 ∧ F.cw = false ∧ F.mw = 0 := by
  cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
    exact ⟨rfl, rfl, rfl⟩

theorem VOp.dst_eq {op : VOp} {F : Fp} (hf : VOp.fp op = some F) {s : State} {d : VReg} {x : BitVec 128}
    (he : VOp.eval s op = some (d, x)) : ∀ r : VReg, F.vw.testBit r.ctorIdx → r = d := by
  intro r hr
  cases op <;> simp only [VOp.fp, reduceCtorEq] at hf <;> cases hf
  case dup a d' n =>
    cases a <;> simp only [VOp.eval, Option.some.injEq, Prod.mk.injEq] at he <;>
      obtain ⟨rfl, -⟩ := he <;> simpa using hr
  all_goals simp only [VOp.eval, Option.some.injEq, Prod.mk.injEq] at he
  all_goals first
    | (obtain ⟨rfl, -⟩ := he; simpa [vecFp] using hr)
    | (split at he
       · simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he; simpa [vecFp] using hr
       · cases he)

theorem det_add {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.add sz d n m) = some F) :
    Det (.add sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_sub {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.sub sz d n m) = some F) :
    Det (.sub sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_mul {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.mul sz d n m) = some F) :
    Det (.mul sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_umulh {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.umulh d n m) = some F) :
    Det (.umulh d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_madd {sz : Size} {d : Reg} {n : Reg} {m : Reg} {a : Reg} {F : Fp} (hf : fp (.madd sz d n m a) = some F) :
    Det (.madd sz d n m a) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_logic {op : LogicOp} {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.logic op sz d n m) = some F) :
    Det (.logic op sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_adc {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.adc sz d n m) = some F) :
    Det (.adc sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  have hc := h.c
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, hc, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_sbc {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.sbc sz d n m) = some F) :
    Det (.sbc sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  have hc := h.c
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg, hc, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  rfl

theorem det_adds {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.adds sz d n m) = some F) :
    Det (.adds sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.awc (t := t) _ _ _ _ _ (fun r hr => only_gbit hr) rfl rfl⟩
  rfl

theorem det_subs {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.subs sz d n m) = some F) :
    Det (.subs sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [Nat.testBit_or]) only [exec, State.read, hg, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.awc (t := t) _ _ _ _ _ (fun r hr => only_gbit hr) rfl rfl⟩
  rfl

theorem det_adcs {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.adcs sz d n m) = some F) :
    Det (.adcs sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  have hc := h.c
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [Nat.testBit_or]) only [exec, State.read, hg, hc, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.awc (t := t) _ _ _ _ _ (fun r hr => only_gbit hr) rfl rfl⟩
  rfl

theorem det_sbcs {sz : Size} {d : Reg} {n : Reg} {m : Reg} {F : Fp} (hf : fp (.sbcs sz d n m) = some F) :
    Det (.sbcs sz d n m) F := by
  intro s t h s' he
  have hg := h.gpr
  have hc := h.c
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [Nat.testBit_or]) only [exec, State.read, hg, hc, Option.some.injEq] at he
  subst he
  refine ⟨_, ?_, Writes.awc (t := t) _ _ _ _ _ (fun r hr => only_gbit hr) rfl rfl⟩
  rfl

theorem det_addImm {sz : Size} {d : Reg} {n : Reg} {imm : Nat} {F : Fp} (hf : fp (.addImm sz d n imm) = some F) :
    Det (.addImm sz d n imm) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_subImm {sz : Size} {d : Reg} {n : Reg} {imm : Nat} {F : Fp} (hf : fp (.subImm sz d n imm) = some F) :
    Det (.subImm sz d n imm) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_lsr {sz : Size} {d : Reg} {n : Reg} {sh : Nat} {F : Fp} (hf : fp (.lsr sz d n sh) = some F) :
    Det (.lsr sz d n sh) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_lsl {sz : Size} {d : Reg} {n : Reg} {sh : Nat} {F : Fp} (hf : fp (.lsl sz d n sh) = some F) :
    Det (.lsl sz d n sh) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_extr {sz : Size} {d : Reg} {n : Reg} {m : Reg} {lsb : Nat} {F : Fp} (hf : fp (.extr sz d n m lsb) = some F) :
    Det (.extr sz d n m lsb) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_movz {sz : Size} {d : Reg} {imm : BitVec 16} {hw : Nat} {F : Fp} (hf : fp (.movz sz d imm hw) = some F) :
    Det (.movz sz d imm hw) F := by
  intro s t h s' he
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp only [exec] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, hcond, ite_true]
  · cases he

theorem det_movk {sz : Size} {d : Reg} {imm : BitVec 16} {hw : Nat} {F : Fp} (hf : fp (.movk sz d imm hw) = some F) :
    Det (.movk sz d imm hw) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp, Option.some.injEq] at hf
  subst hf
  simp (disch := simp [regFp, Nat.testBit_or]) only [exec, State.read, hg] at he
  split at he
  · rename_i hcond
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨_, ?_, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    simp only [exec, State.read, hcond, ite_true]
  · cases he

theorem det_str {sz : Size} {r n : Reg} {off : Nat} {F : Fp} (hf : fp (.str sz r n off) = some F) :
    Det (.str sz r n off) F := by
  intro s t h s' he
  have hg := h.gpr
  simp only [fp] at hf
  split at hf
  · rename_i hn; subst hn
    simp only [Option.some.injEq] at hf
    subst hf
    simp only [exec, addr] at he ⊢
    split at he
    · rename_i ha
      simp only [Option.bind_some, ha, and_self, ite_true] at he ⊢
      simp (disch := simp [Nat.testBit_or]) only [State.read, hg] at he
      rw [← h.x3] at he
      exact store_det h _ (by cases sz <;> decide) (fun o ho => by simpa [testBit_range] using ho)
        rfl rfl rfl s' he
    · cases he
  · cases hf

theorem det_strq {r : VReg} {n : Reg} {off : Nat} {F : Fp} (hf : fp (.strq r n off) = some F) :
    Det (.strq r n off) F := by
  intro s t h s' he
  have hv := h.v
  simp only [fp] at hf
  split at hf
  · rename_i hn; subst hn
    simp only [Option.some.injEq] at hf
    subst hf
    simp only [exec, addr] at he ⊢
    split at he
    · rename_i ha
      simp only [Option.bind_some, ha, and_self, ite_true] at he ⊢
      simp (disch := simp) only [hv] at he
      exact store_det h _ (by decide) (fun o ho => by simpa [testBit_range] using ho) rfl rfl rfl s' he
    · cases he
  · cases hf

theorem det_ldr {sz : Size} {r n : Reg} {off : Nat} {F : Fp} (hf : fp (.ldr sz r n off) = some F) :
    Det (.ldr sz r n off) F := by
  intro s t h s' he
  simp only [fp] at hf
  split at hf
  · rename_i hn; subst hn
    simp only [Option.some.injEq] at hf
    subst hf
    simp only [exec, addr] at he ⊢
    split at he
    · rename_i ha
      simp only [Option.bind_some, ha, and_self, ite_true] at he ⊢
      rw [load_congr (off := off) (n := sz.bytes) h (fun o h1 h2 => by simp [testBit_range]; omega)] at he
      cases e : t.load (t.gpr .x3 + BitVec.ofNat 64 off) sz.bytes with
      | none => rw [e] at he; cases he
      | some x =>
        rw [e] at he
        simp only [Option.map_some, Option.some.injEq] at he
        subst he
        exact ⟨_, rfl, Writes.write (t := t) _ _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    · cases he
  · cases hf

theorem det_ldrq {r : VReg} {n : Reg} {off : Nat} {F : Fp} (hf : fp (.ldrq r n off) = some F) :
    Det (.ldrq r n off) F := by
  intro s t h s' he
  simp only [fp] at hf
  split at hf
  · rename_i hn; subst hn
    simp only [Option.some.injEq] at hf
    subst hf
    simp only [exec, addr] at he ⊢
    split at he
    · rename_i ha
      simp only [Option.bind_some, ha, and_self, ite_true] at he ⊢
      rw [load_congr (off := off) (n := 16) h (fun o h1 h2 => by simp [testBit_range]; omega)] at he
      cases e : t.load (t.gpr .x3 + BitVec.ofNat 64 off) 16 with
      | none => rw [e] at he; cases he
      | some x =>
        rw [e] at he
        simp only [Option.map_some, Option.some.injEq] at he
        subst he
        exact ⟨_, rfl, Writes.setV (t := t) _ _ (fun r hr => only_vbit hr) rfl rfl rfl⟩
    · cases he
  · cases hf

theorem det_vop {op : VOp} {F : Fp} (hf : fp (.vop op) = some F) : Det (.vop op) F := by
  intro s t h s' he
  simp only [fp] at hf
  simp only [exec] at he ⊢
  rw [← VOp.det hf h]
  cases e : VOp.eval s op with
  | none => rw [e] at he; cases he
  | some p =>
    rw [e] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨h1, h2, h3⟩ := VOp.fp_shape hf
    exact ⟨_, rfl, Writes.setV (t := t) _ _ (VOp.dst_eq hf e) h1 h2 h3⟩

theorem det {i : Instr} {F : Fp} (hf : fp i = some F) : Det i F := by
  cases i
  case add => exact det_add hf
  case sub => exact det_sub hf
  case mul => exact det_mul hf
  case umulh => exact det_umulh hf
  case madd => exact det_madd hf
  case logic => exact det_logic hf
  case adc => exact det_adc hf
  case sbc => exact det_sbc hf
  case adds => exact det_adds hf
  case subs => exact det_subs hf
  case adcs => exact det_adcs hf
  case sbcs => exact det_sbcs hf
  case addImm => exact det_addImm hf
  case subImm => exact det_subImm hf
  case lsr => exact det_lsr hf
  case lsl => exact det_lsl hf
  case extr => exact det_extr hf
  case movz => exact det_movz hf
  case movk => exact det_movk hf
  case str => exact det_str hf
  case strq => exact det_strq hf
  case ldr => exact det_ldr hf
  case ldrq => exact det_ldrq hf
  case vop => exact det_vop hf
  all_goals simp only [fp, reduceCtorEq] at hf

/-! ## Interleavings -/

/-- `c` interleaves `a` and `b`. -/
inductive Merge : List Instr → List Instr → List Instr → Prop
  | nil : Merge [] [] []
  | left {x : Instr} {c a b : List Instr} : Merge c a b → Merge (x :: c) (x :: a) b
  | right {y : Instr} {c a b : List Instr} : Merge c a b → Merge (y :: c) a (y :: b)

theorem Merge.append (a b : List Instr) : Merge (a ++ b) a b := by
  induction a with
  | nil =>
    induction b with
    | nil => exact .nil
    | cons y b ih => exact .right ih
  | cons x a ih => exact .left ih


/-! ## Independent instructions commute -/

theorem and_zero {a b i : Nat} (h : a &&& b = 0) (ha : a.testBit i = true) : b.testBit i = false := by
  have := congrArg (·.testBit i) h
  simp only [Nat.testBit_and, ha, Bool.true_and, Nat.zero_testBit] at this
  exact this

theorem lt_pow {m o : Nat} (hm : m >>> 65536 = 0) (h : m.testBit o = true) : o < 2 ^ 64 := by
  have : o < 65536 := by
    by_contra hc
    have := Nat.testBit_shiftRight m (i := 65536) (j := o - 65536)
    rw [hm, Nat.zero_testBit, show 65536 + (o - 65536) = o by omega, h] at this
    exact Bool.noConfusion this
  omega

/-- What independence says, one location at a time. -/
structure Indep (F G : Fp) : Prop where
  gw_gr : ∀ i, F.gw.testBit i = true → G.gr.testBit i = false
  gw_gw : ∀ i, F.gw.testBit i = true → G.gw.testBit i = false
  gw_gr' : ∀ i, G.gw.testBit i = true → F.gr.testBit i = false
  vw_vr : ∀ i, F.vw.testBit i = true → G.vr.testBit i = false
  vw_vw : ∀ i, F.vw.testBit i = true → G.vw.testBit i = false
  vw_vr' : ∀ i, G.vw.testBit i = true → F.vr.testBit i = false
  cw : F.cw = true → G.cr = false ∧ G.cw = false
  cw' : G.cw = true → F.cr = false
  mw_mr : ∀ o, F.mw.testBit o = true → G.mr.testBit o = false
  mw_mw : ∀ o, F.mw.testBit o = true → G.mw.testBit o = false
  mw_mr' : ∀ o, G.mw.testBit o = true → F.mr.testBit o = false
  x3 : F.gw.testBit Reg.x3.ctorIdx = false
  x3' : G.gw.testBit Reg.x3.ctorIdx = false
  fmr : ∀ o, F.mr.testBit o = true → o < 2 ^ 64
  fmw : ∀ o, F.mw.testBit o = true → o < 2 ^ 64
  gmr : ∀ o, G.mr.testBit o = true → o < 2 ^ 64
  gmw : ∀ o, G.mw.testBit o = true → o < 2 ^ 64

theorem Indep.of {F G : Fp} (h : F.indep G = true) : Indep F G := by
  simp only [Fp.indep, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => and_zero h2 hi, fun i hi => ?_, fun i hi => ?_,
    fun i hi => and_zero h4 hi, fun hc => ?_, fun hc => ?_, fun o ho => ?_, fun o ho => ?_,
    fun o ho => and_zero h8 ho, h9, h10, fun o ho => lt_pow h11 ho, fun o ho => lt_pow h12 ho,
    fun o ho => lt_pow h13 ho, fun o ho => lt_pow h14 ho⟩
  · have := and_zero h1 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h1 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2
  · have := and_zero h3 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h3 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2
  · simp only [hc, Bool.true_and, Bool.or_eq_false_iff] at h5; exact h5
  · simp only [hc, Bool.true_and] at h6; exact h6
  · have := and_zero h7 ho; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h7 ho; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2

theorem addr_ne {b : Addr} {o o' : Nat} (h : o ≠ o') (ho : o < 2 ^ 64) (ho' : o' < 2 ^ 64) :
    b + BitVec.ofNat 64 o ≠ b + BitVec.ofNat 64 o' := by
  intro e
  have e' : BitVec.ofNat 64 o = BitVec.ofNat 64 o' := by
    have := congrArg (fun x => x - b) e
    simpa only [BitVec.add_comm b, BitVec.add_sub_cancel] using this
  have := congrArg BitVec.toNat e'
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt ho'] at this
  exact h this

/-- Running an instruction keeps what an independent footprint reads. -/
theorem reads_of_frame {F G : Fp} (hI : Indep F G) {s s' : State} (hfr : Frame F s s') : Reads G s s' where
  gpr r hr := (hfr.gpr r (by
    cases e : F.gw.testBit r.ctorIdx
    · rfl
    · rw [hI.gw_gr _ e] at hr; exact Bool.noConfusion hr)).symm
  v r hr := (hfr.v r (by
    cases e : F.vw.testBit r.ctorIdx
    · rfl
    · rw [hI.vw_vr _ e] at hr; exact Bool.noConfusion hr)).symm
  c hc := (hfr.c (by
    cases e : F.cw
    · rfl
    · rw [(hI.cw e).1] at hc; exact Bool.noConfusion hc)).symm
  x3 := (hfr.gpr _ hI.x3).symm
  mem o ho := (hfr.mem _ fun o' ho' e => by
    have hne : o ≠ o' := fun h => by rw [h, hI.mw_mr _ ho'] at ho; exact Bool.noConfusion ho
    exact addr_ne hne (hI.gmr _ ho) (hI.fmw _ ho') e).symm
  rd := hfr.rd.symm
  wr := hfr.wr.symm

theorem Indep.symm {F G : Fp} (h : Indep F G) : Indep G F where
  gw_gr := h.gw_gr'
  gw_gw i hi := by
    cases e : F.gw.testBit i
    · rfl
    · rw [h.gw_gw _ e] at hi; exact Bool.noConfusion hi
  gw_gr' := h.gw_gr
  vw_vr := h.vw_vr'
  vw_vw i hi := by
    cases e : F.vw.testBit i
    · rfl
    · rw [h.vw_vw _ e] at hi; exact Bool.noConfusion hi
  vw_vr' := h.vw_vr
  cw hc := ⟨h.cw' hc, by
    cases e : F.cw
    · rfl
    · rw [(h.cw e).2] at hc; exact Bool.noConfusion hc⟩
  cw' hc := (h.cw hc).1
  mw_mr := h.mw_mr'
  mw_mw o ho := by
    cases e : F.mw.testBit o
    · rfl
    · rw [h.mw_mw _ e] at ho; exact Bool.noConfusion ho
  mw_mr' := h.mw_mr
  x3 := h.x3'
  x3' := h.x3
  fmr := h.gmr
  fmw := h.gmw
  gmr := h.fmr
  gmw := h.fmw


theorem exec_comm {i j : Instr} {F G : Fp} (hi : fp i = some F) (hj : fp j = some G) (hI : Indep F G)
    (s : State) : (exec i s).bind (exec j) = (exec j s).bind (exec i) := by
  cases ei : exec i s with
  | none =>
    cases ej : exec j s with
    | none => rfl
    | some t1 =>
      simp only [Option.bind_none, Option.bind_some]
      cases e2 : exec i t1 with
      | none => rfl
      | some t2 =>
        obtain ⟨_, h, _⟩ := det hi t1 s (reads_of_frame hI.symm (frame hj ej)).symm t2 e2
        rw [ei] at h; cases h
  | some s1 =>
    cases ej : exec j s with
    | none =>
      simp only [Option.bind_none, Option.bind_some]
      cases e2 : exec j s1 with
      | none => rfl
      | some s2 =>
        obtain ⟨_, h, _⟩ := det hj s1 s (reads_of_frame hI (frame hi ei)).symm s2 e2
        rw [ej] at h; cases h
    | some t1 =>
      simp only [Option.bind_some]
      obtain ⟨s2, hs2, wG⟩ := det hj s s1 (reads_of_frame hI (frame hi ei)) t1 ej
      obtain ⟨t2, ht2, wF⟩ := det hi s t1 (reads_of_frame hI.symm (frame hj ej)) s1 ei
      rw [hs2, ht2]
      congr 1
      have f1 := frame hi ei
      have f2 := frame hj hs2
      have g1 := frame hj ej
      have g2 := frame hi ht2
      have x1 : s1.gpr .x3 = s.gpr .x3 := f1.gpr _ hI.x3
      have y1 : t1.gpr .x3 = s.gpr .x3 := g1.gpr _ hI.x3'
      apply state_ext
      · funext r
        cases hF : F.gw.testBit r.ctorIdx
        · cases hG : G.gw.testBit r.ctorIdx
          · rw [f2.gpr r hG, f1.gpr r hF, g2.gpr r hF, g1.gpr r hG]
          · rw [← wG.gpr r hG, g2.gpr r hF]
        · rw [f2.gpr r (hI.gw_gw _ hF), wF.gpr r hF]
      · rw [f2.sp, f1.sp, g2.sp, g1.sp]
      · cases hF : F.cw
        · cases hG : G.cw
          · rw [f2.c hG, f1.c hF, g2.c hF, g1.c hG]
          · rw [← wG.c hG, g2.c hF]
        · rw [f2.c (hI.cw hF).2, wF.c hF]
      · funext r
        cases hF : F.vw.testBit r.ctorIdx
        · cases hG : G.vw.testBit r.ctorIdx
          · rw [f2.v r hG, f1.v r hF, g2.v r hF, g1.v r hG]
          · rw [← wG.v r hG, g2.v r hF]
        · rw [f2.v r (hI.vw_vw _ hF), wF.v r hF]
      · funext x
        by_cases hx : ∃ o, F.mw.testBit o = true ∧ x = s.gpr .x3 + BitVec.ofNat 64 o
        · obtain ⟨o, ho, rfl⟩ := hx
          have hFG : ∀ o', G.mw.testBit o' = true → o ≠ o' := fun o' ho' h => by
            subst h; rw [hI.mw_mw _ ho] at ho'; exact Bool.noConfusion ho'
          rw [f2.mem _ fun o' ho' e => addr_ne (hFG o' ho') (hI.fmw _ ho) (hI.gmw _ ho') (by rw [e, x1]),
            ← x1, wF.mem o ho]
        · by_cases hy : ∃ o, G.mw.testBit o = true ∧ x = s.gpr .x3 + BitVec.ofNat 64 o
          · obtain ⟨o, ho, rfl⟩ := hy
            have hGF : ∀ o', F.mw.testBit o' = true → o ≠ o' := fun o' ho' h => by
              subst h; rw [hI.symm.mw_mw _ ho] at ho'; exact Bool.noConfusion ho'
            rw [g2.mem _ fun o' ho' e => addr_ne (hGF o' ho') (hI.gmw _ ho) (hI.fmw _ ho') (by rw [e, y1])]
            have w := wG.mem o ho
            rw [y1] at w
            exact w.symm
          · have nF : ∀ o, F.mw.testBit o = true → x ≠ s.gpr .x3 + BitVec.ofNat 64 o :=
              fun o ho e => hx ⟨o, ho, e⟩
            have nG : ∀ o, G.mw.testBit o = true → x ≠ s.gpr .x3 + BitVec.ofNat 64 o :=
              fun o ho e => hy ⟨o, ho, e⟩
            rw [f2.mem x (by rw [x1]; exact nG), f1.mem x nF, g2.mem x (by rw [y1]; exact nF), g1.mem x nG]
      · rw [f2.rd, f1.rd, g2.rd, g1.rd]
      · rw [f2.wr, f1.wr, g2.wr, g1.wr]
      · rw [f2.unknowns, f1.unknowns, g2.unknowns, g1.unknowns]


/-! ## Blocks -/

/-- Every instruction of `a` is independent of every instruction of `b`. -/
def Indeps (a b : List Instr) : Prop :=
  ∀ x ∈ a, ∀ y ∈ b, ∃ F G, fp x = some F ∧ fp y = some G ∧ Indep F G

theorem comm_block {y : Instr} {a : List Instr}
    (ha : ∀ x ∈ a, ∃ F G, fp x = some F ∧ fp y = some G ∧ Indep F G) (s : State) :
    (exec y s).bind (runBlock isa a) = (runBlock isa a s).bind (exec y) := by
  induction a generalizing s with
  | nil =>
    show (exec y s).bind some = exec y s
    cases exec y s <;> rfl
  | cons x a ih =>
    obtain ⟨F, G, hx, hy, hI⟩ := ha x List.mem_cons_self
    show (exec y s).bind (fun u => (exec x u).bind (runBlock isa a)) =
      ((exec x s).bind (runBlock isa a)).bind (exec y)
    rw [← Option.bind_assoc, exec_comm hy hx hI.symm, Option.bind_assoc, Option.bind_assoc]
    congr 1
    funext u
    exact ih (fun x' hx' => ha x' (List.mem_cons_of_mem _ hx')) u

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

theorem run_merge {c a b : List Instr} (hm : Merge c a b) (hind : Indeps a b) (s : State) :
    runBlock isa c s = runBlock isa (a ++ b) s := by
  induction hm generalizing s with
  | nil => rfl
  | @left x c a b _ ih =>
    show (exec x s).bind (runBlock isa c) = (exec x s).bind (runBlock isa (a ++ b))
    congr 1
    funext u
    exact ih (fun x' hx' y hy => hind x' (List.mem_cons_of_mem _ hx') y hy) u
  | @right y c a b _ ih =>
    show (exec y s).bind (runBlock isa c) = runBlock isa (a ++ y :: b) s
    have ih' : runBlock isa c = runBlock isa (a ++ b) :=
      funext (ih (fun x hx y' hy' => hind x hx y' (List.mem_cons_of_mem _ hy')))
    have ap : runBlock isa (a ++ b) = fun u => (runBlock isa a u).bind (runBlock isa b) :=
      funext (runBlock_append a b)
    rw [ih', ap, runBlock_append, ← Option.bind_assoc,
      comm_block (fun x hx => hind x hx y List.mem_cons_self) s, Option.bind_assoc]
    rfl

/-! ## Checking independence on unions -/

/-- Everything `F` touches, `A` touches. -/
structure Sub (F A : Fp) : Prop where
  gr : ∀ i, F.gr.testBit i = true → A.gr.testBit i = true
  gw : ∀ i, F.gw.testBit i = true → A.gw.testBit i = true
  vr : ∀ i, F.vr.testBit i = true → A.vr.testBit i = true
  vw : ∀ i, F.vw.testBit i = true → A.vw.testBit i = true
  cr : F.cr = true → A.cr = true
  cw : F.cw = true → A.cw = true
  mr : ∀ i, F.mr.testBit i = true → A.mr.testBit i = true
  mw : ∀ i, F.mw.testBit i = true → A.mw.testBit i = true

theorem Sub.left (F B : Fp) : Sub F (F.union B) := by
  constructor <;> intros <;> simp_all [Fp.union, Nat.testBit_or]

theorem Sub.right (F B : Fp) : Sub B (F.union B) := by
  constructor <;> intros <;> simp_all [Fp.union, Nat.testBit_or]

theorem Sub.trans {F A B : Fp} (h₁ : Sub F A) (h₂ : Sub A B) : Sub F B :=
  ⟨fun i h => h₂.gr i (h₁.gr i h), fun i h => h₂.gw i (h₁.gw i h), fun i h => h₂.vr i (h₁.vr i h),
    fun i h => h₂.vw i (h₁.vw i h), fun h => h₂.cr (h₁.cr h), fun h => h₂.cw (h₁.cw h),
    fun i h => h₂.mr i (h₁.mr i h), fun i h => h₂.mw i (h₁.mw i h)⟩

theorem false_of_sub {a b : Bool} (h : a = true → b = true) (hb : b = false) : a = false := by
  cases a <;> simp_all

theorem Indep.mono {A B F G : Fp} (h : Indep A B) (hF : Sub F A) (hG : Sub G B) : Indep F G where
  gw_gr i hi := false_of_sub (hG.gr i) (h.gw_gr i (hF.gw i hi))
  gw_gw i hi := false_of_sub (hG.gw i) (h.gw_gw i (hF.gw i hi))
  gw_gr' i hi := false_of_sub (hF.gr i) (h.gw_gr' i (hG.gw i hi))
  vw_vr i hi := false_of_sub (hG.vr i) (h.vw_vr i (hF.vw i hi))
  vw_vw i hi := false_of_sub (hG.vw i) (h.vw_vw i (hF.vw i hi))
  vw_vr' i hi := false_of_sub (hF.vr i) (h.vw_vr' i (hG.vw i hi))
  cw hc := ⟨false_of_sub hG.cr (h.cw (hF.cw hc)).1, false_of_sub hG.cw (h.cw (hF.cw hc)).2⟩
  cw' hc := false_of_sub hF.cr (h.cw' (hG.cw hc))
  mw_mr o ho := false_of_sub (hG.mr o) (h.mw_mr o (hF.mw o ho))
  mw_mw o ho := false_of_sub (hG.mw o) (h.mw_mw o (hF.mw o ho))
  mw_mr' o ho := false_of_sub (hF.mr o) (h.mw_mr' o (hG.mw o ho))
  x3 := false_of_sub (hF.gw _) h.x3
  x3' := false_of_sub (hG.gw _) h.x3'
  fmr o ho := h.fmr o (hF.mr o ho)
  fmw o ho := h.fmw o (hF.mw o ho)
  gmr o ho := h.gmr o (hG.mr o ho)
  gmw o ho := h.gmw o (hG.mw o ho)

theorem blockFp_sub {a : List Instr} {A : Fp} (ha : blockFp a = some A) :
    ∀ x ∈ a, ∃ F, fp x = some F ∧ Sub F A := by
  induction a generalizing A with
  | nil => intro x hx; cases hx
  | cons y a ih =>
    simp only [blockFp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨F, hy, B, hb, rfl⟩ := ha
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨F, hy, Sub.left F B⟩
    · obtain ⟨F', hx', hs⟩ := ih hb x hx
      exact ⟨F', hx', hs.trans (Sub.right F B)⟩

theorem indeps_of {a b : List Instr} {A B : Fp} (ha : blockFp a = some A) (hb : blockFp b = some B)
    (h : A.indep B = true) : Indeps a b := by
  intro x hx y hy
  obtain ⟨F, hx', hF⟩ := blockFp_sub ha x hx
  obtain ⟨G, hy', hG⟩ := blockFp_sub hb y hy
  exact ⟨F, G, hx', hy', (Indep.of h).mono hF hG⟩

/-- Independence by evaluating both blocks' footprints. -/
theorem indeps_of_check {a b : List Instr}
    (h : ((blockFp a).bind fun A => (blockFp b).map fun B => A.indep B) = some true) : Indeps a b := by
  cases ha : blockFp a with
  | none => rw [ha] at h; cases h
  | some A =>
    cases hb : blockFp b with
    | none => rw [ha, hb] at h; cases h
    | some B =>
      rw [ha, hb] at h
      exact indeps_of ha hb (Option.some.inj h)

theorem Merge.nil_left : ∀ b : List Instr, Merge b [] b
  | [] => .nil
  | _ :: b => .right (Merge.nil_left b)

theorem Merge.nil_right : ∀ a : List Instr, Merge a a []
  | [] => .nil
  | _ :: a => .left (Merge.nil_right a)

theorem runBlock_of_WP {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q) :
    ∃ s', runBlock isa is s = some s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact ⟨s, rfl, WP.block_nil_iff.mp h⟩
  | cons i is ih =>
    obtain ⟨s₁, h₁, h₂⟩ := WP.block_cons_iff.mp h
    obtain ⟨s', h', hq⟩ := ih h₂
    have h₁' : exec i s = some s₁ := h₁
    exact ⟨s', by show (exec i s).bind (runBlock isa is) = _; rw [h₁']; exact h', hq⟩

/-- An interleaving of independent blocks runs as the first block and then the second. -/
theorem WP.merge {c a b : List Instr} (hm : Merge c a b) (hind : Indeps a b) {s : State}
    {Q : State → Prop} (h : WP isa (.block (a ++ b)) s Q) : WP isa (.block c) s Q := by
  obtain ⟨s', h', hq⟩ := runBlock_of_WP h
  exact WP.of_runBlock ⟨s', by rw [run_merge hm hind]; exact h', hq⟩

end VG.AArch64.Interleave
