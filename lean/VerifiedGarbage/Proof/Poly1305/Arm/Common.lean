import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Poly1305.Arm.Arith

/-!
# Poly1305 on 32-bit ARM: common lemmas

Untrusted: everything here is checked by Lean. Facts about the registers the
code uses, which registers a piece of code may change (`Keeps`), and WP
rules for one instruction at a time that expose only what changes.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-! ## Registers -/

theorem yr_ne : ∀ k < 9, yr k ≠ .r0 ∧ yr k ≠ .r1 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide
theorem yr9 : yr 9 = .r1 := rfl
theorem yr_ne' : ∀ k < 10, yr k ≠ .r0 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide
theorem yr_inj : ∀ j < 10, ∀ k < 10, yr j = yr k → j = k := by decide
theorem xr_ne : ∀ k < 10, xr k ≠ .r0 ∧ xr k ≠ .r1 ∧ xr k ≠ .r2 := by decide
theorem xr_inj : ∀ j < 10, ∀ k < 10, xr j = xr k → j = k := by decide
theorem yr_eq_xr : ∀ k < 9, yr k = xr k := by decide
theorem xr9 : xr 9 = .r12 := rfl

/-- The registers `r1`–`r12`: every register the code changes but `r0` and `lr`. -/
def work : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem yr_work : ∀ k < 10, yr k ∈ work := by decide
theorem xr_work : ∀ k < 10, xr k ∈ work := by decide

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws` and the flags. -/
structure Keeps (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (ws : List Reg) (s : State) : Keeps ws s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps ws s₁ s₂) (h₂ : Keeps ws s₂ s₃) :
    Keeps ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.mono {ws ws' : List Reg} {s s' : State} (h : Keeps ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Keeps ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, subFlags, h], rfl, rfl, rfl, rfl⟩

theorem Upd.keeps {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Keeps ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.mem, h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp [Op2.eval, h]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp [Op2.eval, h]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp [Op2.eval, h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp [exec, ho]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

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
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp [exec, ho, State.load8, hin])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp [exec, ho, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

/-! ## 32-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 32) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem toNat_and_mask (x : BitVec 32) : (x &&& (0x1fff#16).setWidth 32).toNat = x.toNat % 2 ^ 13 := by
  rw [BitVec.toNat_and, show ((0x1fff#16).setWidth 32).toNat = 2 ^ 13 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## Addresses -/

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k := by
  intro x hx hy
  bv_omega

/-- Reading a word after writing one elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show p + BitVec.ofNat 64 d - (p + BitVec.ofNat 64 a) = BitVec.ofNat 64 (d - a) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem sub_sub (p : Addr) {a len b len' : Nat} (h1 : b ≤ a) (h2 : a + len ≤ b + len')
    (h3 : b + len' < 2 ^ 32) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p + BitVec.ofNat 64 b, len'⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  rw [show x - (p + BitVec.ofNat 64 b) = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 (a - b) by
    rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 b + BitVec.ofNat 64 (a - b) by
      rw [← BitVec.ofNat_add]; congr 1; omega]
    bv_omega]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a - b) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The state -/

/-- The state's region. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 128⟩

theorem ea {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {off : Nat} (h : off < 128) :
    State.addr (st + BitVec.ofNat 32 off) = State.addr st + BitVec.ofNat 64 off :=
  addr_add (by omega)

theorem inSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem outSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions s.wr (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, hw, contains_off h (by omega)⟩

end VG.Proof.Poly1305.Arm
