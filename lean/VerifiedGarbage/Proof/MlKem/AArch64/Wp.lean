import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM on AArch64: one instruction at a time

Untrusted: everything here is checked by Lean. Weakest-precondition rules
for the instruction forms the ML-KEM code uses, in continuation style: each
rule runs one instruction in front of the rest of a block, and hands the
rest the state it leaves, with what changed (`Only`: only the registers
listed may differ; `MemTo`: only the memory differs). Values are stated as
natural numbers (`toNat`), which `omega` reasons about; the `_n` lemmas
turn the machine's operations into operations on them when nothing wraps.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64

/-! ## What an instruction changes -/

/-- `s'` is `s` but for the registers `rs`. -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Only

theorem refl (rs : List Reg) (s : State) : Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only rs s₁ s₂) (h₂ : Only rs' s₂ s₃) :
    Only (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Only rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-- A register not in `rs` is kept. -/
theorem get {rs : List Reg} {s s' : State} (h : Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Only

/-- `s'` is `s` with memory `m`. -/
structure MemTo (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` but for the registers `rs` and the memory. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Keep

theorem refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem get {rs : List Reg} {s s' : State} (h : Keep rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Keep

theorem Only.keep {rs : List Reg} {s s' : State} (h : Only rs s s') : Keep rs s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp⟩

theorem MemTo.keep {s s' : State} {m : Mem} (h : MemTo s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem write_x_gpr (s : State) (d : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr d = v := by simp [State.write]

theorem only_write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Only [d] s (s.write sz d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-! ## The instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_x {i : Instr} {d : Reg} {v : BitVec 64} (he : exec i s = some (s.write .x d v))
    (k : ∀ s', Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons he (k _ (only_write _ _ _ _) (write_x_gpr _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  wp_x (by simp [exec, h, State.read]) k

theorem wp_mov {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' h e => k s' h (by rw [e]; exact BitVec.add_zero _)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  wp_x (by simp [exec, h, State.read]) k

theorem wp_and {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_orr {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n >>> sh → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  wp_x (by simp [exec, h, State.read]) k

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n <<< sh → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  wp_x (by simp [exec, h, State.read]) k

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n * s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.mul .x d n m :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_madd {d n m a : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr a + s.gpr n * s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.madd .x d n m a :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Only [d] s s' → s'.gpr d = imm.setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  wp_x (by simp [exec]) k

theorem wp_movk1 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Only [d] s s' →
      s'.gpr d = (s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< 16) ||| imm.setWidth 64 <<< 16) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.movk .x d imm 1 :: is)) s Q :=
  wp_x (by simp only [exec, State.read, Size.bits, BitVec.setWidth_eq]; rfl) k

theorem wp_ldrw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Only [t] s s' → s'.gpr t = (s.mem.readW a 32).setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_
    (k _ (only_write _ _ _ _) (by simp [State.write]))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_strw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldrx {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Only [t] s s' → s'.gpr t = s.mem.readW a 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_
    (k _ (only_write _ _ _ _) (write_x_gpr _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_strx {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', MemTo s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Only [t] s s' → s'.gpr t = (s.mem a).setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  have e : ((s.mem a).setWidth 32 : BitVec 32).setWidth 64 = (s.mem a).setWidth 64 := by
    ext i hi; simp
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ (only_write _ _ _ _) ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · simp only [State.write, ite_true]
    exact e

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

end

/-! ## Constants -/

/-- `movImm d v`: `d ← v`. -/
theorem wp_movImm {d : Reg} {v : BitVec 64} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.movImm d v ++ is)) s Q := by
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (k _ ?_ ?_))))
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp [State.write, hr]
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v

/-! ## Branch conditions -/

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

theorem ne_zero_iff (x : BitVec 64) : (x != 0) = decide (x.toNat ≠ 0) := by
  have e : x = 0 ↔ x.toNat = 0 :=
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  by_cases h : x.toNat = 0
  · have : x = 0 := e.mpr h
    subst this; rfl
  · have : x ≠ 0 := fun h' => h (e.mp h')
    simpa [h] using this

theorem eq_zero_iff (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  rw [← Bool.not_not (x == 0), show (!(x == 0)) = (x != 0) from rfl, ne_zero_iff]
  simp

/-- A do-while loop on `cbnz cr` that runs its body `n > 0` times: the
register is not zero exactly until the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ ((s'.gpr cr).toNat ≠ 0 ↔ k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by
    rw [eval_nonzero, ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr hc)
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## Numbers -/

theorem toNat_add_n {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_n {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have := a.isLt
  omega

theorem toNat_mul_n {a b : BitVec 64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_madd_n {a b c : BitVec 64} (h : a.toNat + b.toNat * c.toNat < 2 ^ 64) :
    (a + b * c).toNat = a.toNat + b.toNat * c.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem toNat_lsr (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_lsl_n {a : BitVec 64} {n : Nat} (h : a.toNat * 2 ^ n < 2 ^ 64) :
    (a <<< n).toNat = a.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_and_mask (a b : BitVec 64) {k : Nat} (h : b.toNat = 2 ^ k - 1) :
    (a &&& b).toNat = a.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, h, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_imm (imm : BitVec 16) : (imm.setWidth 64).toNat = imm.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := imm.isLt; omega)]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_readW32 (m : Mem) (a : Addr) : ((m.readW a 32).setWidth 64).toNat = (m.readW a 32).toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.readW a 32).isLt; omega)]

theorem toNat_byte (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The low 32 bits of a register holding a number less than `2³²`. -/
theorem setWidth32_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

/-- The low byte of a register. -/
theorem setWidth8_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

/-! ## Addresses -/

theorem ptr_next (p : Addr) (k c : Nat) :
    p + BitVec.ofNat 64 (c * k) + BitVec.ofNat 64 c = p + BitVec.ofNat 64 (c * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

theorem ptr_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- `[p + off, p + off + n)` is within the region `⟨p, len⟩` if `off + n ≤ len < 2⁶⁴`. -/
theorem contains_off {p : Addr} {off n len : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show p + BitVec.ofNat 64 off - p = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_regions {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

theorem in_rd_wr {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, List.mem_append_right _ hR, hc⟩

theorem in_rd {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions rd a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, List.mem_append_left _ hR, hc⟩

/-- Bytes `[a, a + n)` and `[b, b + k)` at offsets of one base, apart. -/
theorem sep_off (p : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n < 2 ^ 64)
    (hb : b + k < 2 ^ 64) : Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 b) k := by
  intro x h₁ h₂
  have e : ∀ c, c < 2 ^ 64 → (x - (p + BitVec.ofNat 64 c)).toNat = ((x - p).toNat + 2 ^ 64 - c) % 2 ^ 64 := by
    intro c hc
    rw [show x - (p + BitVec.ofNat 64 c) = (x - p) - BitVec.ofNat 64 c by bv_omega, BitVec.toNat_sub,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    omega
  rw [e a (by omega)] at h₁
  rw [e b (by omega)] at h₂
  have := (x - p).isLt
  omega

end VG.Proof.MlKem.AArch64
