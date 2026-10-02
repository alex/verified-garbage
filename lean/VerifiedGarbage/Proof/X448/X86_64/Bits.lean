import VerifiedGarbage.Proof.X448.X86_64.Iter
import VerifiedGarbage.Proof.X448.Bytes

/-!
# X448 on x86-64: the bits of the scalar

`bits` stores bit `j` of byte `i` of the scalar at byte `8i + j` of `BITS`,
then the clamped bits; so byte `t` of `BITS` is bit `t` of the decoded scalar
(`scalar_bit`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

/-- The body of `bits`' loop. -/
def bitsBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 56)]

theorem bitsBody_eq : bitsBody =
    [.movzx8 .rax { base := .rsi, index := some .rbx },
    .mov .rdx (.reg .rax),
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 0) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 1,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 1) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 2,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 2) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 3,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 3) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 4,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 4) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 5,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 5) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 6,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 6) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 7,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 7) .rdx,
    .alu .add .rbx (.imm 1),
    .alu .cmp .rbx (.imm 56)] := rfl

theorem bits_eq : bits = .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block bitsBody) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .mov32 .rax (.imm 1), .store8 (sc (BITS + 447)) .rax])) := rfl

theorem ea_scalar (s : State) {k : Addr} (hk : s.gpr .rsi = k) {i : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    s.ea { base := .rsi, index := some .rbx } = k + BitVec.ofNat 64 i := by
  simp only [State.ea, hk, hb]
  rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]

theorem ea_bitAt (s : State) (j : Nat) :
    s.ea (bitAt j) = s.gpr .rdi + s.gpr .rbx * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) := by
  simp only [State.ea, bitAt, BitVec.ofInt_natCast]

theorem addr_bit (base : Addr) (i j : Nat) :
    base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) =
      off base (BITS + (8 * i + j)) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    off base d = off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => ofs base x) h
    simp only [ofs_off' base hd, ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& BitVec.signExtend 64 (1 : BitVec 32)).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

/-- Bit `j` of `rax` (a byte) into `BITS[8 rbx + j]`. -/
def bitJ (j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1), .store8 (bitAt j) .rdx]

theorem bitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 56)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ j)) s fun s' =>
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base (BITS + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have w : InRegions s.wr (off base (BITS + (8 * i + j))) 1 :=
    ⟨_, hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have e := bit_byte b j hj
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.store8, ea_bitAt, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, hs.rdi, hb, ha, addr_bit, w, ite_false, reduceCtorEq, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; rfl
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, State.store8,
    ea_bitAt, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, ha, addr_bit, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩,
    ite_true, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_self]
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) : (m.writeW (off base d) v) x = m x := by
  rw [writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (ofs_off' base hd) hx

theorem bitsBody_eq' : bitsBody = ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (bitJ 0 ++ (bitJ 1 ++ (bitJ 2 ++ (bitJ 3 ++ (bitJ 4 ++ (bitJ 5 ++ (bitJ 6 ++ (bitJ 7 ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 56)] : List Instr))))))))) := by
  rw [bitsBody_eq]; rfl

theorem inc_eq (i : Nat) :
    BitVec.ofNat 64 i + BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (i + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add]

theorem cmp56 : ∀ i < 56,
    (BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (56 : BitVec 32) == 0) = decide (i + 1 = 56) := by
  decide +kernel

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    {i : Nat} (hi : i < 56) (hb : s.gpr .rbx = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 i) 1) :
    WP isa (.block bitsBody) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = 56)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ j < 8, s'.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem s'.mem := by
  rw [bitsBody_eq', WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun s' => s'.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_scalar s hk hb, State.load8, hkr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s₀ ⟨a0, g0, m0, rd0, wr0⟩ => ?_
  have hs₀ : Scr s₀ base := ⟨(g0 _ (by decide)).trans hs.rdi, wr0 ▸ hs.wr, hs.nowrap⟩
  have hb₀ : s₀.gpr .rbx = BitVec.ofNat 64 i := (g0 _ (by decide)).trans hb
  -- The eight bits, each kept by the ones after it.
  have keep : ∀ {x y : State}, (∀ r, r ≠ .rdx → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr →
      Scr x base → x.gpr .rbx = BitVec.ofNat 64 i → x.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 →
      Scr y base ∧ y.gpr .rbx = BitVec.ofNat 64 i ∧ y.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 :=
    fun g _ wr hx hbx hax => ⟨⟨(g _ (by decide)).trans hx.rdi, wr ▸ hx.wr, hx.nowrap⟩,
      (g _ (by decide)).trans hbx, (g _ (by decide)).trans hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₀ hi hb₀ a0 (j := 0) (by omega)) fun s₁ ⟨g1, rd1, wr1, m1⟩ => ?_
  obtain ⟨hs₁, hb₁, ha₁⟩ := keep g1 rd1 wr1 hs₀ hb₀ a0
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₁ hi hb₁ ha₁ (j := 1) (by omega)) fun s₂ ⟨g2, rd2, wr2, m2⟩ => ?_
  obtain ⟨hs₂, hb₂, ha₂⟩ := keep g2 rd2 wr2 hs₁ hb₁ ha₁
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₂ hi hb₂ ha₂ (j := 2) (by omega)) fun s₃ ⟨g3, rd3, wr3, m3⟩ => ?_
  obtain ⟨hs₃, hb₃, ha₃⟩ := keep g3 rd3 wr3 hs₂ hb₂ ha₂
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₃ hi hb₃ ha₃ (j := 3) (by omega)) fun s₄ ⟨g4, rd4, wr4, m4⟩ => ?_
  obtain ⟨hs₄, hb₄, ha₄⟩ := keep g4 rd4 wr4 hs₃ hb₃ ha₃
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₄ hi hb₄ ha₄ (j := 4) (by omega)) fun s₅ ⟨g5, rd5, wr5, m5⟩ => ?_
  obtain ⟨hs₅, hb₅, ha₅⟩ := keep g5 rd5 wr5 hs₄ hb₄ ha₄
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₅ hi hb₅ ha₅ (j := 5) (by omega)) fun s₆ ⟨g6, rd6, wr6, m6⟩ => ?_
  obtain ⟨hs₆, hb₆, ha₆⟩ := keep g6 rd6 wr6 hs₅ hb₅ ha₅
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₆ hi hb₆ ha₆ (j := 6) (by omega)) fun s₇ ⟨g7, rd7, wr7, m7⟩ => ?_
  obtain ⟨hs₇, hb₇, ha₇⟩ := keep g7 rd7 wr7 hs₆ hb₆ ha₆
  rw [WP.block_append_iff]
  refine WP.mono (bitJ_ok hs₇ hi hb₇ ha₇ (j := 7) (by omega)) fun s₈ ⟨g8, rd8, wr8, m8⟩ => ?_
  obtain ⟨hs₈, hb₈, ha₈⟩ := keep g8 rd8 wr8 hs₇ hb₇ ha₇
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₈, inc_eq,
    ite_true, RegUpd.zf_arithFlags, RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, cmp56 i hi]
  have hm : s₀.mem = s.mem := m0
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ite_eq_right hr.2.2, g8 r hr.2.1, g7 r hr.2.1, g6 r hr.2.1, g5 r hr.2.1, g4 r hr.2.1, g3 r hr.2.1,
      g2 r hr.2.1, g1 r hr.2.1, g0 r hr.1]
  · rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0]
  · rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
    have ne : ∀ a b, a < 8 → b < 8 → a ≠ b →
        off base (BITS + (8 * i + a)) ≠ off base (BITS + (8 * i + b)) := by
      intro a b ha hb hab h
      rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)] at h
      omega
    have ne' : ∀ a b, a < 8 → b < 8 → a ≠ b →
        (off base (BITS + (8 * i + a)) = off base (BITS + (8 * i + b))) = False :=
      fun a b ha hb hab => eq_false (ne a b ha hb hab)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [writeW8_apply, ite_true, ne', ite_false]
  · intro x hx
    have hd : ∀ j < 8, ofs base x ≠ BITS + (8 * i + j) := fun j hj h => by omega
    have hb : ∀ j < 8, BITS + (8 * i + j) < 2 ^ 64 := fun j hj => by simp only [BITS]; omega
    rw [m8, m7, m6, m5, m4, m3, m2, m1, writeW8_outside _ _ _ (hb 7 (by omega)) (hd 7 (by omega)),
      writeW8_outside _ _ _ (hb 6 (by omega)) (hd 6 (by omega)),
      writeW8_outside _ _ _ (hb 5 (by omega)) (hd 5 (by omega)),
      writeW8_outside _ _ _ (hb 4 (by omega)) (hd 4 (by omega)),
      writeW8_outside _ _ _ (hb 3 (by omega)) (hd 3 (by omega)),
      writeW8_outside _ _ _ (hb 2 (by omega)) (hd 2 (by omega)),
      writeW8_outside _ _ _ (hb 1 (by omega)) (hd 1 (by omega)),
      writeW8_outside _ _ _ (hb 0 (by omega)) (hd 0 (by omega)), hm]

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  rsi : s.gpr .rsi = k
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) .ne) s fun s' => BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .ne)
    (Q := fun s' => BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.rsi hi hb.rbx (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', g', rd', wr', bits', o'⟩ => ?_
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.rdi, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.rsi, b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
  rcases Nat.lt_or_ge (i + 1) 56 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 56), Bool.not_false],
      56 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 55 := by omega
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 448`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits_eq]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, hk, rfl, fun r hr => ?_, rfl, rfl, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  have hs₂ := h₂.scr
  have w : ∀ d, d + 1 ≤ 8192 → InRegions s₂.wr (off base d) 1 :=
    fun d hd => ⟨_, hs₂.wr, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, State.store8, ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hs₂.rdi, w BITS (by simp only [BITS]; omega), w (BITS + 1) (by simp only [BITS]; omega),
    w (BITS + 447) (by simp only [BITS]; omega),
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, by rw [RegUpd.rd_setReg]; exact h₂.rd, h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [hr'.1, ite_false]
    exact h₂.gpr r hr
  · have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [writeW8_apply, off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [h₂.bits t (by omega), getD_bytesAt _ _ (by omega)]

end VG.Proof.X448.X86_64
