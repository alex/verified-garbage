import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Arm.Limbs

/-!
# X25519 on 32-bit ARM: one instruction at a time

Untrusted: everything here is checked by Lean. WP rules for the instructions
the code uses, which expose only what changes (`Upd`: one register, `Mupd`:
the memory), what a piece of code leaves unchanged (`Rest`), words of memory
at offsets from a base (`wd`), and 32-bit arithmetic without overflow.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws`, the flags and the memory. -/
structure Rest (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rest.refl (ws : List Reg) (s : State) : Rest ws s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Rest.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : Rest ws s₁ s₂) (h₂ : Rest ws s₂ s₃) :
    Rest ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Rest.mono {ws ws' : List Reg} {s s' : State} (h : Rest ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Rest ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, h, ↓reduceIte],
    rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) :
    Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte],
    fun r h => by simp only [State.setReg, subFlags, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.rest {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Rest ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Mupd.rest {s s' : State} {m : Mem} (h : Mupd s s' m) (ws : List Reg) : Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Fupd.rest {s s' : State} (h : Fupd s s') (ws : List Reg) : Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp only [Op2.eval, h, ↓reduceIte]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

/-- The value of a data-processing instruction. -/
def dpVal (op : DpOp) (x y : BitVec 32) : BitVec 32 :=
  match op with
  | .add => x + y | .sub => x - y | .and => x &&& y | .orr => x ||| y | .eor => x ^^^ y

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_dp {op : DpOp} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (dpVal op (s.gpr n) y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp op d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (dpVal op (s.gpr n) y))
    (by cases op <;> simp only [exec, ho, Option.map_some, dpVal]) (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp only [exec, ho, Option.map_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32))
    (by simp only [exec, ho, ↓reduceIte, State.load8, hin, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp only [exec, ho, ↓reduceIte, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-! ## 32-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)]

theorem toNat_mul_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 32) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The mask of a limb, as `movw` builds it. -/
abbrev mask16 : BitVec 32 := (0xffff : BitVec 16).setWidth 32

theorem toNat_and_mask16 (x : BitVec 32) : (x &&& mask16).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, show mask16.toNat = 2 ^ 16 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_imm {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-! ## Words at offsets from a base -/

/-- The word at `P + d`, as a number. -/
def wd (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 32).toNat

theorem wd_lt (m : Mem) (P : Addr) (d : Nat) : wd m P d < 2 ^ 32 := (m.readW _ 32).isLt

theorem wd_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 32) :
    wd (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [wd, Mem.readW_writeW_self32]

theorem wd_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) :
    wd (m.writeW (P + BitVec.ofNat 64 e) v) P d = wd m P d := by
  rw [wd, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), wd]

theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {d : Nat}
    (hd : ∀ r ∈ rs, (⟨P + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r) : wd m' P d = wd m P d := by
  rw [wd, wd, hf.readW (Region.contains_self _ _) hd (by decide)]

/-- An address `pb + off` of a base register, as a 64-bit address, if it does not wrap. -/
theorem ea {pb : BitVec 32} {off : Nat} (h : pb.toNat + off < 2 ^ 32) :
    State.addr (pb + BitVec.ofNat 32 off) = State.addr pb + BitVec.ofNat 64 off := addr_add h

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- An access at an offset of a region at an offset of `P`. -/
theorem in_off {rs : List Region} {P : Addr} {a len d n : Nat} (hr : (⟨P + BitVec.ofNat 64 a, len⟩ : Region) ∈ rs)
    (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 64) :
    InRegions rs (P + BitVec.ofNat 64 d) n := ⟨_, hr, Offset.contains P h1 h2 h3⟩

theorem in_base {rs : List Region} {P : Addr} {len d n : Nat} (hr : (⟨P, len⟩ : Region) ∈ rs)
    (h : d + n ≤ len) (h3 : d < 2 ^ 64) : InRegions rs (P + BitVec.ofNat 64 d) n :=
  ⟨_, hr, Offset.contains_base P h h3⟩

end VG.Proof.X25519.Arm
