import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy

/-!
# Short Weierstrass curves on x86-64: tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, each giving
eight bytes of the table (`bitsBody_ok`). `bitMask d` makes the mask `rcx`
of the byte `rbx` of the table at `d` (`bitMask_ok`): all ones for a 1, zero
for a 0 (`bitMask_bool_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

/-! ## Bytes -/

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem writeW8_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero,
    Nat.mul_zero, BitVec.setWidth_eq]
  exact BitVec.extractLsb'_eq_self

/-! ## Masks -/

/-- `rbx` as an index into a table at `d`. -/
theorem ea_tbl {s : State} {base : Addr} (hb : s.gpr .rdi = base) {t : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 t) (d : Nat) : s.ea (tbl d) = off base (d + t) := by
  simp only [State.ea, tbl, hb, ht, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, Offset.add_add, Nat.add_comm]

/-- `rcx = -[rdi + rbx + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 t) (hd : d + t + 1 ≤ size) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .rcx = 0 - (s.mem (off base (d + t))).setWidth 64 ∧ Keeps [.rax, .rcx] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (off base (d + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := d + t) (n := 1) hd (by decide)⟩
  apply WP.of_runBlock
  simp only [bitMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    Option.map_some, Option.bind_some, State.load8, State.setReg32, ea_tbl hs.rdi ht, hr,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 64 = (if c then BitVec.allOnes 64 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 t) (hd : d + t + 1 ≤ size) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .rcx = (if c then BitVec.allOnes 64 else 0) ∧ Keeps [.rax, .rcx] s s' :=
  WP.mono (bitMask_ok hs ht hd) fun _ ⟨e, k⟩ => ⟨by rw [e, hc, neg_bit], k⟩

/-! ## The table of bits -/

/-- Bit `j` of `rax` (a byte) to byte `j` of the eight at `rdi + 8 rbx + dst`. -/
def bitJ (dst j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1), .store8 (bitAt dst j) .rdx]

/-- The body of `bits`' loop. -/
def bitsBody (src dst nbytes : Nat) : List Instr :=
  [.movzx8 .rax (tbl src)] ++ (List.range 8).flatMap (bitJ dst) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 nbytes))]

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block (bitsBody src dst nbytes)) .ne) :=
  rfl

theorem ea_bitAt (s : State) (dst j : Nat) :
    s.ea (bitAt dst j) = s.gpr .rdi + s.gpr .rbx * BitVec.ofNat 64 8 + BitVec.ofNat 64 (dst + j) := by
  simp only [State.ea, bitAt]
  rw [← Int.natCast_add, BitVec.ofInt_natCast]

theorem addr_bit (base : Addr) (i dst j : Nat) :
    base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofNat 64 (dst + j) =
      off base (dst + (8 * i + j)) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact congrArg (fun k => base + BitVec.ofNat 64 k) (by omega)

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& BitVec.signExtend 64 (1 : BitVec 32)).setWidth 8 : BitVec 8) =
      if b.getLsbD j then 1 else 0 := by decide +kernel

theorem bit_byte0 : ∀ b : BitVec 8,
    ((b.setWidth 64 &&& BitVec.signExtend 64 (1 : BitVec 32)).setWidth 8 : BitVec 8) =
      if b.getLsbD 0 then 1 else 0 := by decide +kernel

theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {dst j : Nat} (hj : j < 8) (hd : dst + (8 * i + j) + 1 ≤ size) :
    WP isa (.block (bitJ dst j)) s fun s' => KeepRegs [.rdx] s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have w : InRegions s.wr (off base (dst + (8 * i + j))) 1 :=
    ⟨_, hs.wr, hs.contains (n := 1) hd (by decide)⟩
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.store8, ea_bitAt, hs.rdi, ht, addr_bit, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
      RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, w, ite_false, reduceCtorEq,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ha, bit_byte0]
    refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, State.store8,
      ea_bitAt, hs.rdi, ht, addr_bit, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
      RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
      RegUpd.mem_arithFlags, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩, ite_true, reduceCtorEq,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ha, bit_byte b j hj, and_self]
    refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The first `k` bits of `rax` (a byte). -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {dst : Nat} (hd : dst + 8 * i + 8 ≤ size) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => KeepRegs [.rdx] s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (bitJs_ok hs ht ha hd k (by omega)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_
    refine WP.mono (bitJ_ok (hs.of_keepRegs k₁ (by decide)) (i := i) (by rw [k₁.gpr _ (by decide), ht])
      (b := b) (by rw [k₁.gpr _ (by decide), ha]) (dst := dst) (j := k) (by omega) (by omega))
      fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega)]; omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, writeW8_self]

theorem cmp_eq {i N : Nat} (hi : i + 1 ≤ N) (hN : N < 2 ^ 31) :
    (BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (BitVec.ofNat 32 N) == 0) = decide (i + 1 = N) := by
  have hse : BitVec.signExtend 64 (BitVec.ofNat 32 N) = BitVec.ofNat 64 N := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
        rw [BitVec.toNat_ofNat]; omega)),
      BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]
  rw [hse]
  by_cases h : i + 1 = N
  · rw [h, BitVec.sub_self, decide_eq_true rfl]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    omega

theorem inc_eq (i : Nat) :
    BitVec.ofNat 64 i + BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (i + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add]

/-- One byte of the number at `src`: its bits to the table at `dst`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src dst N i : Nat}
    (ht : s.gpr .rbx = BitVec.ofNat 64 i) (hi : i < N) (hN : N < 2 ^ 31) (hsrc : src + i + 1 ≤ size)
    (hd : dst + 8 * i + 8 ≤ size) :
    WP isa (.block (bitsBody src dst N)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = N)) ∧
      KeepRegs [.rax, .rdx, .rbx] s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  have hr : InRegions (s.rd ++ s.wr) (off base (src + i)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains (n := 1) hsrc (by decide)⟩
  rw [bitsBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax (tbl src)]) s (fun s₁ =>
      s₁.gpr .rax = (s.mem (off base (src + i))).setWidth 64 ∧ Keeps [.rax] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_tbl hs.rdi ht, State.load8, hr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (bitJs_ok hs₁ (by rw [k₁.1 _ (by decide), ht]) a₁ hd 8 (Nat.le_refl _))
    fun s₂ ⟨k₂, e₂, O₂⟩ => ?_
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 i := by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), ht]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₂, inc_eq,
    ite_true, RegUpd.zf_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.mem_setReg, cmp_eq hi hN]
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, ?_, ?_⟩, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_eq_right hr.2.2, k₂.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr.2.1),
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr.1)]
  · rw [RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, k₂.rd, k₁.2.2.1]
  · rw [RegUpd.wr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, k₂.wr, k₁.2.2.2]
  · exact e₂ j hj
  · rw [← k₁.2.1]; exact O₂

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base size
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  keep : KeepRegs [.rax, .rdx, .rbx] s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

theorem bitsLoop_ok {s₀ : State} {base : Addr} {size src dst n : Nat} (hn : n < 2 ^ 28)
    (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    ∀ i, ∀ s, i < 8 * n → BInv base size src dst n s₀ s i →
      WP isa (.loop (.block (bitsBody src dst (8 * n))) .ne) s fun s' =>
        BInv base size src dst n s₀ s' (8 * n) := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block (bitsBody src dst (8 * n))) (c := .ne)
    (Q := fun s' => BInv base size src dst n s₀ s' (8 * n))
    (fun m (s : State) => ∃ i, m = 8 * n - i ∧ i < 8 * n ∧ BInv base size src dst n s₀ s i) ?_
    (8 * n - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  have hnw := hb.scr.nowrap
  refine WP.mono (bitsBody_ok hb.scr hb.rbx hi (by omega) (by omega) (by omega))
    fun s' ⟨b', z', k', bits', O'⟩ => ?_
  have hbyte : s.mem (off base (src + i)) = s₀.mem (off base (src + i)) :=
    hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega)]; omega)
  have inv : BInv base size src dst n s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keepRegs k' (by decide), b', hb.keep.trans k',
      hb.mem.trans (O'.mono (by omega) (by omega)), fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
  rcases Nat.lt_or_ge (i + 1) (8 * n) with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 8 * n), Bool.not_false],
      8 * n - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · have h' : i + 1 = 8 * n := by omega
    exact .inl ⟨by simp only [h', decide_true, Bool.not_true], h' ▸ inv⟩

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst : Nat}
    (hn0 : 0 < n) (hn : n < 2 ^ 28) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      KeepRegs [.rax, .rdx, .rbx] s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  rw [bits_eq]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      BInv base size src dst n s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, rfl, ⟨fun r hr => ?_, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.mono (bitsLoop_ok hn hsrc hdst hsep 0 s₁ (by omega) h₁) fun s₂ h₂ => ⟨fun t ht => ?_, h₂.keep, h₂.mem⟩
  rw [h₂.bits t (by omega), show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
    testBit_byte s.mem base (a := src) (n := n) (by omega) (Nat.mod_lt _ (by decide))]
  simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega]

end VG.Proof.Weierstrass.X86_64
