import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Calls

/-!
# Streaming ChaCha20 on ARMv7: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/Arm/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function. The pieces are those that the proof
of constant time (`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_cmp
  wp_ldr wp_str eval_eq ofNat_beq_zero sub_ofNat)
open VG.Proof.ChaCha20.Arm.Xor (imm0 imm1 imm64 sub_zero')
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The check -/

/-- After the check: Z is whether fewer than `len` bytes are left. -/
structure Q0 (s₀ s : State) : Prop where
  z : s.z = decide (N s₀ < L s₀)
  keep : ∀ r, r ≠ .r3 → r ≠ .r12 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem N_eq (s₀ : State) : N s₀ = (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat +
    2 ^ 32 * (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32).toNat := by
  simp only [N, leftAt]
  rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat, Offset.add_add]

/-- The flag the check leaves: whether `a + 2³² b < l`, from the carries of
`a - l` and `b - 1`. -/
theorem check_z (a b l : BitVec 32) :
    (((0 + 0 + if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0) + 0 +
      if decide (BitVec.toNat (1 : BitVec 32) ≤ b.toNat) = true then 1 else 0) - 0 == 0) =
      decide (a.toNat + 2 ^ 32 * b.toNat < l.toNat) := by
  have := l.isLt
  have e : (1 : BitVec 32).toNat = 1 := rfl
  by_cases h₁ : l.toNat ≤ a.toNat <;> by_cases h₂ : BitVec.toNat (1 : BitVec 32) ≤ b.toNat <;>
    simp only [h₁, h₂, decide_true, decide_false, ite_true] <;>
    first | (rw [decide_eq_false (by omega)]; decide) | (rw [decide_eq_true (by omega)]; decide)

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have e₁ := hp.eaS (d := 128) (by decide); have e₂ := hp.eaS (d := 132) (by decide)
  have j₁ := hp.r_st (d := 128) (n := 4) (by decide); have j₂ := hp.r_st (d := 132) (n := 4) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.setReg, subFlags, e₁, e₂, j₁, j₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h₁ h₂ => by simp [h₁, h₂], rfl, rfl, rfl, rfl⟩
  refine (check_z (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32) (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32)
    (s₀.gpr .r2)).trans ?_
  rw [N_eq]

/-- What `apply` guarantees (`applyArm`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.ChaCha20.applyArm.post s₀ s

theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.mov .r0 (.imm 0)]) s (Final s₀) := by
  refine wp_mov (op2_imm imm0) fun s' u => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u.sp, h.sp]⟩, ?_⟩
  · rw [u.other r (preserved_ne hr).1, h.keep r (preserved_ne hr).2.2.2.1 (preserved_ne hr).2.2.2.2]
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega), u.mem, h.mem]
    exact ⟨rfl, u.gpr, rfl, rfl⟩

/-! ## The bytes left in the buffered block -/

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 32) : x &&& (63 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 64) := by
  have : (63 : BitVec 32) = BitVec.ofNat 32 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Our caller's `r4`–`r7`, our return address, and the bytes left after
`apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  r4 : m.readW (st s₀ + BitVec.ofNat 64 576) 32 = s₀.gpr .r4
  r5 : m.readW (st s₀ + BitVec.ofNat 64 580) 32 = s₀.gpr .r5
  r6 : m.readW (st s₀ + BitVec.ofNat 64 584) 32 = s₀.gpr .r6
  r7 : m.readW (st s₀ + BitVec.ofNat 64 588) 32 = s₀.gpr .r7
  lr : m.readW (st s₀ + BitVec.ofNat 64 592) 32 = s₀.gpr .lr
  lo : m.readW (st s₀ + BitVec.ofNat 64 600) 32 = BitVec.ofNat 32 (N s₀ - L s₀)
  hi : m.readW (st s₀ + BitVec.ofNat 64 604) 32 = BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 576, 32⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 4 ≤ 608 → (savR s₀).Contains (st s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.r4],
    by rw [hf.readW (c 580 (by decide) (by decide)) hd (by decide), h.r5],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.r6],
    by rw [hf.readW (c 588 (by decide) (by decide)) hd (by decide), h.r7],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.lr],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.lo],
    by rw [hf.readW (c 604 (by decide) (by decide)) hd (by decide), h.hi]⟩

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- The memory after `start`'s stores. -/
def startMem (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) : Mem :=
  ((((((m.writeW (st + BitVec.ofNat 64 576) a).writeW (st + BitVec.ofNat 64 580) b).writeW
    (st + BitVec.ofNat 64 584) c).writeW (st + BitVec.ofNat 64 588) d).writeW (st + BitVec.ofNat 64 592) e).writeW
    (st + BitVec.ofNat 64 600) lo).writeW (st + BitVec.ofNat 64 604) hi

theorem startMem_frame (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) :
    Frame [⟨st, 768⟩] m (startMem m st a b c d e lo hi) := by
  have c : ∀ d, d + 4 ≤ 768 → (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 580 (by decide))).writeW (List.mem_singleton_self _) _
    (c 584 (by decide))).writeW (List.mem_singleton_self _) _ (c 588 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 592 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 600 (by decide))).writeW (List.mem_singleton_self _) _ (c 604 (by decide))

theorem startMem_byte (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) {i : Nat} (hi' : i < 576) :
    (startMem m st a b c d e lo hi) (st + BitVec.ofNat 64 i) = m (st + BitVec.ofNat 64 i) := by
  simp only [startMem]
  rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]

theorem startMem_read (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) {k : Nat} (hk : k + 4 ≤ 576) :
    (startMem m st a b c d e lo hi).readW (st + BitVec.ofNat 64 k) 32 = m.readW (st + BitVec.ofNat 64 k) 32 := by
  simp only [startMem]
  rw [readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega)]

set_option simprocs false in
theorem startMem_saved (s₀ : State) :
    Saved s₀ (startMem s₀.mem (st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
      (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (config := {decide := true}) only [startMem, Mem.readW_writeW_self32, readW_writeW_ofNat]

/-- The low word of the bytes left after `apply`. -/
theorem left_lo {a b l : BitVec 32} {n : Nat} (hn : n = a.toNat + 2 ^ 32 * b.toNat) (h : l.toNat ≤ n) :
    a - l = BitVec.ofNat 32 (n - l.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := l.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- And its high word, from the borrow of the low word. -/
theorem left_hi {a b l : BitVec 32} {n : Nat} (hn : n = a.toNat + 2 ^ 32 * b.toNat) (h : l.toNat ≤ n) :
    b + ((65535 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (65535 : BitVec 16))) +
      (if decide (l.toNat ≤ a.toNat) = true then 1 else 0) = BitVec.ofNat 32 ((n - l.toNat) / 2 ^ 32) := by
  rw [show ((65535 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (65535 : BitVec 16)) : BitVec 32) =
    BitVec.ofNat 32 (2 ^ 32 - 1) by decide]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := l.isLt
  by_cases hc : l.toNat ≤ a.toNat
  · simp only [hc, decide_true, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · simp only [hc, decide_false, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (if false = true then (1 : BitVec 32) else 0).toNat = 0 from rfl]
    omega

def startA : List Instr :=
  [.str .r4 .r0 576, .str .r5 .r0 580, .str .r6 .r0 584, .str .r7 .r0 588, .str .lr .r0 592,
   .ldr .r3 .r0 128, .ldr .r12 .r0 132, .subs .r3 .r3 (.reg .r2), .movw .r4 0xffff, .movt .r4 0xffff,
   .adc .r12 .r12 (.reg .r4), .str .r3 .r0 600, .str .r12 .r0 604]

def startB : List Instr :=
  [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
   .ldr .r12 .r4 128, .dp .and .r12 .r12 (.imm 63), .cmp .r12 (.reg .r6), .mov .r0 (.imm 0),
   .adc .r0 .r0 (.imm 0), .cmp .r0 (.imm 0), .mov .r2 (.reg .r6)]

theorem start_eq : start = startA ++ startB := rfl

set_option simprocs false in
theorem startA_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block startA) s fun s' =>
      s'.mem = startMem s₀.mem (st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
        (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s'.gpr r = s₀.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : ∀ d, d < 768 → State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.keep .r0 (by decide) (by decide)]; exact hp.eaS hd
  have o : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have i : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e576 := e 576 (by decide); have e580 := e 580 (by decide); have e584 := e 584 (by decide)
  have e588 := e 588 (by decide); have e592 := e 592 (by decide); have e600 := e 600 (by decide)
  have e604 := e 604 (by decide); have e128 := e 128 (by decide); have e132 := e 132 (by decide)
  have o576 := o 576 (by decide); have o580 := o 580 (by decide); have o584 := o 584 (by decide)
  have o588 := o 588 (by decide); have o592 := o 592 (by decide); have o600 := o 600 (by decide)
  have o604 := o 604 (by decide); have i128 := i 128 (by decide); have i132 := i 132 (by decide)
  have k4 := h.keep .r4 (by decide) (by decide); have k5 := h.keep .r5 (by decide) (by decide)
  have k6 := h.keep .r6 (by decide) (by decide); have k7 := h.keep .r7 (by decide) (by decide)
  have kl := h.keep .lr (by decide) (by decide); have k2 := h.keep .r2 (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [startA, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.store32, State.setReg, subFlags, e576, e580, e584, e588, e592, e600, e604, e128, e132,
    o576, o580, o584, o588, o592, o600, o604, i128, i132, k4, k5, k6, k7, kl, k2, h.mem, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left', readW_writeW_ofNat]
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, trivial⟩
  · rw [left_lo (N_eq s₀) hle, left_hi (N_eq s₀) hle]
    rfl
  · simp only [h₁, h₂, h₃, ite_false]
    exact h.keep r h₁ h₃

/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.r8, .r9, .r10, .r11]

theorem kept_ne {r : Reg} (hr : r ∈ kept) {r' : Reg} (h : r' ∉ kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- After `start`, with `x` in `r2`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = ST s₀
  r5 : s.gpr .r5 = DP s₀
  r6 : s.gpr .r6 = BitVec.ofNat 32 (L s₀)
  r2 : s.gpr .r2 = BitVec.ofNat 32 x
  r12 : s.gpr .r12 = BitVec.ofNat 32 (O s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

theorem lo_mod (s₀ : State) : (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat % 64 = O s₀ := by
  simp only [O]
  rw [N_eq]
  omega

/-- The carry of `cmp`, moved into a register by `adc` of zeros, compared
with zero. -/
theorem carry_z (x y : Nat) : ((0 + 0 + if decide (x ≤ y) = true then (1 : BitVec 32) else 0) - 0 == 0) =
    decide (y < x) := by
  by_cases h : x ≤ y
  · simp only [h, decide_true, ite_true]; rw [decide_eq_false (by omega)]; decide
  · simp only [h, decide_false]; rw [decide_eq_true (by omega)]; decide

set_option simprocs false in
theorem startB_ok {s₀ : State} (hp : APre s₀) {s : State} (h0 : s.gpr .r0 = ST s₀) (h1 : s.gpr .r1 = DP s₀)
    (h2 : s.gpr .r2 = s₀.gpr .r2) (hk : ∀ r ∈ kept, s.gpr r = s₀.gpr r)
    (hm : s.mem = startMem s₀.mem (st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
        (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    WP isa (.block startB) s fun s' => R1 s₀ (L s₀) s' ∧ s'.z = decide (O s₀ < L s₀) := by
  have hf := startMem_frame s₀.mem (st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
    (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))
  have e₁ := hp.eaS (d := 128) (by decide)
  have i₁ : InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 128) 4 := by
    rw [hrd, hwr]; exact hp.r_st (by decide)
  have v₁ := startMem_read s₀.mem (st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
    (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)) (k := 128) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [startB, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.setReg, subFlags, h0, h1, h2, e₁, i₁, hm, v₁, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', and_63, lo_mod]
  have hO : O s₀ < 2 ^ 32 := by have := O_lt s₀; omega
  have hL : s₀.gpr .r2 = BitVec.ofNat 32 (L s₀) := by simp [L]
  refine ⟨⟨rfl, rfl, hL, hL, rfl, fun r hr => ?_, hrd, hwr, hsp,
    ⟨fun i hi => startMem_byte _ _ _ _ _ _ _ _ _ (by omega), startMem_saved s₀⟩, fun k hk => ?_, hm ▸ hf⟩, ?_⟩
  · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [ite_false] <;>
      exact hk _ (by simp [kept])
  · dsimp only
    rw [hm, hf.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    simp
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hO, carry_z]

end VG.Proof.ChaCha20.Arm.Stream
