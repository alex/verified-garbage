import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Ed25519.AArch64.Mul
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.Sub
import VerifiedGarbage.Spec.Ed25519
import Mathlib.Logic.Function.Basic

/-! Merged from `Proof.Ed25519.AArch64.Sqr`. -/
section
/-! Four-word field squaring. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem sq_expand_radix (R A0 A1 A2 A3 : Nat) :
    (A0 + R * A1 + R * R * A2 + R * R * R * A3) * (A0 + R * A1 + R * R * A2 + R * R * R * A3) =
      R * (2 * (A0 * A1 + R * (A0 * A2) + R * R * (A0 * A3 + A1 * A2) + R * R * R * (A1 * A3) +
        R * R * R * R * (A2 * A3))) +
        (A0 * A0 + R * R * (A1 * A1) + R * R * R * R * (A2 * A2 + R * R * (A3 * A3))) := by
  grind

/-- The square of four words: twice the products of distinct words, and the squares. -/
theorem sq_expand (A0 A1 A2 A3 : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) *
        (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) =
      2 ^ 64 * (2 * cross A0 A1 A2 A3) + diag A0 A1 A2 A3 := by
  have h := sq_expand_radix (2 ^ 64) A0 A1 A2 A3
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from rfl,
    show (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 from rfl,
    show (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 from rfl] at h
  exact h

theorem sqrWide_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat}
    (ha : FieldRange a large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (sqrWide a)) s fun t =>
      wide t = fe s.mem base a * fe s.mem base a ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x21, .x22, .x23, .x24] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [sqrWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ha (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sqrCross_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrDouble_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (sqrDiag_ok s₃) fun s₄ ⟨c, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have A : ∀ (r : Reg), r ∈ [.x12, .x13, .x14, .x15] → s₃.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  rw [A .x12 (by decide), A .x13 (by decide), A .x14 (by decide), A .x15 (by decide),
    e3, e2, a0, a1, a2, a3] at e4
  have hlt : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  have hx := sq_expand (word s.mem base a).toNat (word s.mem base (a + 8)).toNat
    (word s.mem base (a + 16)).toNat (word s.mem base (a + 24)).toNat
  dsimp only [wide]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx] at hlt
  omega_using [e4, hlt]

/-- Squaring modulo p, allowing the output to alias the input. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base large) {o a : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) :
    WP isa (.block (fieldSqr o a)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldSqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrWide_ok hs₀ ha hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.Add`. -/
section
/-! Four-word field addition. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldAddWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * c.toNat =
          fe s.mem base a + fe s.mem base b ∧
        (t.gpr .x8).toNat = 38 * c.toNat ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ workSize large → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) hd⟩
  have enc : ∀ d, d + 8 ≤ workSize large → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldAddWords, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, ld, exec, addr, State.load, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.mem_addWithCarry,
    BitVec.setWidth_eq, hs.x0, hz, h38, Size.bytes,
    Nat.add_mod, ha, hb, Nat.reduceMod, Nat.zero_add,
    enc a (by omega), enc b (by omega), enc (a + 8) (by omega), enc (b + 8) (by omega),
    enc (a + 16) (by omega), enc (b + 16) (by omega), enc (a + 24) (by omega), enc (b + 24) (by omega),
    w a (by omega), w b (by omega), w (a + 8) (by omega), w (b + 8) (by omega),
    w (a + 16) (by omega), w (b + 16) (by omega), w (a + 24) (by omega), w (b + 24) (by omega),
    and_self, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (word s.mem base (a + 24)) (word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (word s.mem base (b + 8))
        (carryOut (word s.mem base a) (word s.mem base b) false))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := add4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact carry38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- Addition modulo p, with memory and ABI frames. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldAdd o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldAdd, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by
    rw [x1]
    have := Bool.toNat_le c
    omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ heq => ?_
  subst s₃
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans k2')) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega), e2, x1]
  rw [k0.mem] at e1
  have hm : toFe (val4 (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7) + 38 * c.toNat) =
      toFe (fe s.mem base a + fe s.mem base b) := by
    apply toFe_congr
    rw [← e1]
    exact (fold256 _ _).symm
  exact hm.trans (toFe_add rfl)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.FieldMemory`. -/
section
/-! Constants and copies in the field workspace. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem slot_rangeWith (o : Slot) : FieldRange (offset o) large := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  constructor <;> simp only [offset] <;> omega

theorem slot_range (o : Slot) : FieldRange (offset o) := slot_rangeWith (large := true) o

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = v.val ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  rw [constWords, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps [.x4, .x5, .x6, .x7] s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [k4.gpr .x4 (by decide), k3.gpr .x4 (by decide), k2.gpr .x4 (by decide), e1,
    k4.gpr .x5 (by decide), k3.gpr .x5 (by decide), e2, k4.gpr .x6 (by decide), e3, e4]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem constField_op {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [constField, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (slot_rangeWith (large := large) o).2; omega), hv, toFe_self]

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base large) (a : Slot) :
    WP isa (.block (loads (offset a) .x4 .x5 .x6 .x7)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (offset a) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (loads_ok hs (slot_rangeWith (large := large) a) (by decide)) fun t ⟨e1, e2, e3, e4, k⟩ => ?_
  exact ⟨by rw [e1, e2, e3, e4], k⟩

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [copyField, WP.block_append_iff]
  refine WP.mono (loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (slot_rangeWith (large := large) o).2; omega), hv]

theorem Outside_F {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 32 < 2 ^ 64)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : F m' base d = F m base d :=
  congrArg toFe (h.fe hsep hd)

end VG.Proof.Ed25519.AArch64
end

/-!
# Ed25519 field programs: correctness of the lowering

Each arithmetic operation uses the A64 field arithmetic proof. An induction
composes these into a proof for any list of field operations.
-/

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}


open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : Addr) : Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .sqr o a => Function.update e o (e a * e a)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : Env) (o a b i : Slot) :
    evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_add_apply (e : Env) (o a b i : Slot) :
    evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : Env) (o a b i : Slot) :
    evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 64 704 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (k : Keep base t u) :
    Keep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem env_update {base : Addr} {m m' : Mem} (o : Slot)
    (h : Outside base (offset o) 32 m m') :
    env m' base = Function.update (env m base) o (F m' base (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [env]
  · rw [Function.update_of_ne hi]
    simp only [env, F]
    have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem op_keep {base : Addr} {o : Slot} {s t : State} (h : Op base (offset o) s t) :
    Keep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega)
    (by simp only [offset]; omega)⟩

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base large) (op : FieldOp) :
    WP isa (.block op.code) s fun t => Keep base s t ∧ env t.mem base = evalOp op (env s.mem base) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | const o v =>
    refine WP.mono (constField_op hs o v) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | mul o a b =>
    refine WP.mono (mul_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | sqr o a =>
    refine WP.mono (sqr_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | add o a b =>
    refine WP.mono (add_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | sub o a b =>
    refine WP.mono (sub_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩

theorem fieldCode_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block (fieldCode ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOp_ok hs op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.scr hs)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

theorem constField_ok {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o v := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (constField_op hs o v) fun t ⟨hk, hv⟩ => ?_
  exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]⟩

theorem copyField_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o (env s.mem base a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (copyField_op hs o a) fun t ⟨hk, hv⟩ => ?_
  exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) :
    point (evalOps pointAddOps e) 0 1 2 3 = addResult e 4 (by decide) := by
  rfl

/-- What `pointDoubleOps` computes: the addition formula with `p = q`, its
products of equal factors as squares. -/
def doubleResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 1 - e 0)
  let b := (e 1 + e 0) * (e 1 + e 0)
  let c := e 3 * e 3 * e 16 + e 3 * e 3 * e 16
  let dd := e 2 * e 2 + e 2 * e 2
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointDouble_formula (e : Env) :
    point (evalOps pointDoubleOps e) 0 1 2 3 = doubleResult e := by
  rfl

theorem doubleResult_eq (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    doubleResult e = Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) := by
  simp only [doubleResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem addResult_eq (e : Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    addResult e q hq = Spec.Ed25519.pointAdd (point e 0 1 2 3)
      (point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) :=
  (pointAdd_formula e).trans (addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) :=
  (pointDouble_formula e).trans (doubleResult_eq e hd)

end VG.Proof.Ed25519.AArch64
