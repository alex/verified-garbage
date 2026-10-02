import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# x86 (32-bit): weakest-precondition rules for single instructions

Continuation-passing rules for one instruction at the head of a block, which
expose only what changes: the rule for `i` proves `WP (i :: rest)` from a
proof of `WP rest` for every state `i` can end in (`Upd`: one register
written, `Mupd`: memory written, `Fupd`: only the flags).
-/

namespace VG.X86.Wp

open VG VG.X86

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (v : BitVec 32) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, arithFlags, State.setFlags, h], rfl, rfl,
    rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (v : BitVec 32) :
    Upd s ((s.setFlags c o z n).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  zf : s'.zf = s.zf
  cf : s'.cf = s.cf

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- The address `[b + d]`, as `readSrc` loads it. -/
theorem readSrc_mem {s : State} {b : Reg} {d : Nat} {B : BitVec 32} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 4) :
    readSrc s (.mem ⟨b, d⟩) = some (s.mem.readW (addr B d) 32) := by
  show s.load32 (s.ea ⟨b, d⟩) = _
  rw [ea_mk, hb]; simp only [State.load32, hin, ↓reduceIte]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _))

/-- `mov d, [b + o]` -/
theorem wp_ldm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, readSrc_mem hb hin]) (k _ (Upd.setReg _ _ _))

/-- `mov [b + o], r` -/
theorem wp_stm {b r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ea_mk, hb, hout]

/-- `xor d, [b + o]` -/
theorem wp_xorm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

/-- `add d, [b + o]` -/
theorem wp_addm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d + s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `add d, r`, and the carry. -/
theorem wp_add {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sub d, v`, and the flags. -/
theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v) → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem sbb_self (x : BitVec 32) (c : Bool) :
    x - x - (BitVec.ofBool c).setWidth 32 = if c then BitVec.allOnes 32 else 0 := by
  cases c <;> simp

/-- `sbb d, d`: all ones if CF is set, and zero otherwise. -/
theorem wp_sbb_self {d : Reg} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (if c then BitVec.allOnes 32 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sbb d (.reg d) :: is)) s Q := by
  have := k _ (Upd.flags s d (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32)
    (decide ((s.gpr d).toNat < (s.gpr d).toNat + c.toNat))
    (subOverflow (s.gpr d) (s.gpr d) (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32))
    (if c then BitVec.allOnes 32 else 0))
  refine cons ?_ this
  simp only [exec, execAlu, readSrc, Option.bind_some, hc, Option.map_some, sbb_self]

theorem wp_andi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_and {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xor {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.cf = some ((s.gpr d).getLsbD (n - 1)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

theorem wp_ror {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_bswap {d : Reg} (k : ∀ s', Upd s s' d (bswap (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Arithmetic -/

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) :=
  sub_ofNat (b := 1) h

end VG.X86.Wp
