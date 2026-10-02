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
    BitVec.ofNat 32 (2 ^ 32 - 1) by apply BitVec.eq_of_toNat_eq; simp]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt; have hl := l.isLt
  have e1 : (BitVec.ofNat 32 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 := rfl
  have e2 : (BitVec.ofNat 32 ((n - l.toNat) / 2 ^ 32)).toNat = (n - l.toNat) / 2 ^ 32 % 2 ^ 32 :=
    BitVec.toNat_ofNat _ _
  rw [BitVec.toNat_add, BitVec.toNat_add, e1, e2]
  by_cases hc : l.toNat ≤ a.toNat
  · rw [show (if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0).toNat = 1 by simp [hc]]
    omega
  · rw [show (if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0).toNat = 0 by simp [hc]]
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
    rw [hf.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    simp
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hO, carry_z]

theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.z = decide (O s₀ < L s₀) := by
  rw [start_eq, WP.block_append_iff]
  refine WP.mono (startA_ok hp hle h) fun s₁ ⟨m₁, g₁, r₁, w₁, p₁⟩ => startB_ok hp
    (by rw [g₁ _ (by decide) (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (fun r hr => g₁ r (kept_ne hr) (kept_ne hr) (kept_ne hr)) m₁ (by rw [r₁, h.rd]) (by rw [w₁, h.wr])
    (by rw [p₁, h.sp])

theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s) (hz : s.z = decide (O s₀ < L s₀)) :
    WP isa (.ite .eq (.block [.mov .r2 (.reg .r12)]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by have e : isa.eval .eq s = some s.z := eval_eq s; rw [e, hz]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine wp_mov (op2_reg _ _) fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.r4], by rw [u.other _ (by decide), h.r5],
      by rw [u.other _ (by decide), h.r6],
      by rw [u.gpr, h.r12, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.r12],
      fun r hr => by rw [u.other r (kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp], u.mem ▸ h.mid, u.mem ▸ h.done,
      u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.r4, h.r5, h.r6, ?_, h.r12, h.keep, h.rd, h.wr, h.sp, h.mid, h.done,
      h.frame⟩
    rw [h.r2, H, headLen, bufLeft, Nat.min_eq_right hge]

/-- After `part1`: the bytes from the buffered block XORed, and `r2` the
bytes of the whole blocks, Z whether there are none. -/
structure Q1 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = ST s₀
  r5 : s.gpr .r5 = DP s₀ + BitVec.ofNat 32 (H s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (L s₀ - H s₀)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (64 * NB s₀)
  z : s.z = decide (64 * NB s₀ = 0)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 32 x >>> 6) <<< 6 = BitVec.ofNat 32 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem part1_eq : part1 = .seq (.block start)
    (.seq (.ite .eq (.block [.mov .r2 (.reg .r12)]) (.block []))
    (.seq (.block [.dp .add .r3 .r4 (.imm 128), .dp .sub .r3 .r3 (.reg .r12), .dp .sub .r6 .r6 (.reg .r2)])
    (.seq xorBytes (.block [.mov .r2 (.shifted .r6 .lsr 6), .mov .r2 (.shifted .r2 .lsl 6), .cmp .r2 (.imm 0)])))) :=
  rfl

theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  rw [part1_eq]
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ hz₁) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block, and the length left.
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_sub (op2_reg _ _) fun s₄ u₄ =>
    wp_sub (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_)
  have hK : s₅.gpr .r3 = ST s₀ + BitVec.ofNat 32 (128 - O s₀) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .r12 (by decide), h₂.r4, h₂.r12,
      show (128 : BitVec 32) = BitVec.ofNat 32 (128 - O s₀) + BitVec.ofNat 32 (O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - O s₀ + O s₀ = 128 by omega]; rfl,
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have g : ∀ r, r ≠ .r3 → r ≠ .r6 → s₅.gpr r = s₂.gpr r := fun r h₁ h₂ => by
    rw [u₅.other r h₂, u₄.other r h₁, u₃.other r h₁]
  have hm₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have hr6 : s₅.gpr .r6 = BitVec.ofNat 32 (L s₀ - H s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), h₂.r6, u₄.other _ (by decide),
      u₃.other _ (by decide), h₂.r2, sub_ofNat hH]
  have eK : State.addr (ST s₀ + BitVec.ofNat 32 (128 - O s₀)) = st s₀ + BitVec.ofNat 64 (128 - O s₀) :=
    hp.eaS (by omega)
  have hb : BPre s₅ (DP s₀) (ST s₀ + BitVec.ofNat 32 (128 - O s₀)) (H s₀) :=
    ⟨by rw [g _ (by decide) (by decide), h₂.r5], hK, by rw [g _ (by decide) (by decide), h₂.r2],
      by omega, by rw [hp.sNat (by omega)]; omega,
      fun k hk => by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]; exact dR_byte hp (by omega),
      fun k hk => by
        rw [u₅.rd, u₄.rd, u₃.rd, u₅.wr, u₄.wr, u₃.wr, h₂.rd, h₂.wr, eK, Offset.add_add]
        exact hp.r_st (by omega),
      fun j hj k hk => by rw [eK, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₆ h₆ => ?_)
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ =>
    wp_cmp (n := .r2) (op2_imm imm0) fun s₉ f₉ hz => WP.block_nil ?_
  have g' : ∀ r, r ≠ .r2 → s₉.gpr r = s₆.gpr r := fun r hr => by
    rw [f₉.gpr, u₈.other r hr, u₇.other r hr]
  have hm : s₉.mem = s₆.mem := by rw [f₉.mem, u₈.mem, u₇.mem]
  have hnb : 64 * ((L s₀ - H s₀) / 64) = 64 * NB s₀ := by simp only [NB, blocksOf, H]
  have hr2 : s₉.gpr .r2 = BitVec.ofNat 32 (64 * NB s₀) := by
    rw [f₉.gpr, u₈.gpr, u₇.gpr, h₆.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr6,
      round64 (by omega), hnb]
  have kp : ∀ r ∈ kept, s₉.gpr r = s₀.gpr r := fun r hr => by
    rw [g' r (kept_ne hr), h₆.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g r (kept_ne hr) (kept_ne hr)]
    exact h₂.keep r hr
  refine ⟨by rw [g' _ (by decide), h₆.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide), h₂.r4],
    by rw [g' _ (by decide), h₆.r5], by rw [g' _ (by decide), h₆.keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide), hr6], hr2,
    by rw [hz, ← congrFun f₉.gpr .r2, hr2, sub_zero', ofNat_beq_zero (by omega)], kp,
    by rw [f₉.rd, u₈.rd, u₇.rd, h₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd],
    by rw [f₉.wr, u₈.wr, u₇.wr, h₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr],
    by rw [f₉.sp, u₈.sp, u₇.sp, h₆.sp, u₅.sp, u₄.sp, u₃.sp, h₂.sp], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [hm, h₆.frame _ fun r hr hc => ?_, hm₅]
    · exact h₂.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    refine (hm₅ ▸ h₂.mid.saved).frame h₆.frame fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
      simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < H s₀
    · rw [h₆.data k hk', hm₅, h₂.done k hk, eK, Offset.add_add, h₂.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₆.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        hm₅, h₂.done k hk]
      simp [hk']
  · rw [hm]
    exact (hm₅ ▸ h₂.frame.mono (by simp)).trans (h₆.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)

/-! ## The whole blocks -/

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = ST s₀
  r5 : s.gpr .r5 = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (T s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.r4, by rw [h.r5, h0, Nat.add_zero], by rw [h.r6, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr, h.sp,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

/-- The callee-saved registers are kept by the calls, but for `lr`. -/
theorem kept_cs : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∈ preserved ∧ r ≠ .lr := by decide

def ctrInstrs : List Instr :=
  [.ldr .r0 .r4 48, .mov .r1 (.shifted .r2 .lsr 6), .dp .add .r0 .r0 (.reg .r1), .str .r0 .r4 48,
   .mov .r7 (.reg .r2), .dp .add .r0 .r4 (.imm 192), .mov .r1 (.reg .r5), .dp .add .r3 .r4 (.imm 256)]

theorem blocksArgs_eq : blocksArgs = copyWords .r0 .r4 .r4 0 192 16 ++ ctrInstrs := rfl

theorem shr_nb {nb : Nat} (h : 64 * nb < 2 ^ 32) : BitVec.ofNat 32 (64 * nb) >>> 6 = BitVec.ofNat 32 nb := by
  rw [VG.Proof.MdStream.Arm.shr6 h, show 64 * nb / 64 = nb by omega]

theorem blocks_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) (hnb : 0 < NB s₀) :
    WP isa (.seq (.block blocksArgs) (.seq (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor)
      (.block [.dp .add .r5 .r5 (.reg .r7), .dp .sub .r6 .r6 (.reg .r7)]))) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  have hrw : s.rd ++ s.wr = [stR s₀, dR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr, List.nil_append]
  have hc : CPre s .r0 .r4 .r4 (ST s₀) (ST s₀) 0 192 16 :=
    ⟨h.r4, h.r4, by decide, by decide, by omega, by omega, by decide, by decide,
      fun i n' hi => by rw [hrw]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun i n' hi => by rw [h.wr]; exact hp.w_st (by omega),
      Offset.disjoint _ (by omega) (by omega) (by omega)⟩
  rw [blocksArgs_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hc) fun s₁ h₁ => ?_
  have r4₁ : s₁.gpr .r4 = ST s₀ := by rw [h₁.gpr _ (by decide), h.r4]
  have rd₁ : s₁.rd ++ s₁.wr = [stR s₀, dR s₀] := by rw [h₁.rd, h₁.wr, hrw]
  have c48 : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 := Offset.contains_base _ (by omega) (by omega)
  unfold ctrInstrs
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [r4₁]; exact hp.eaS (by decide))
    (by rw [rd₁]; exact ⟨stR s₀, by simp, c48⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_add (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_str (a := st s₀ + BitVec.ofNat 64 48) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; exact hp.eaS (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr, h.wr]; exact hp.w_st (by decide)) fun s₅ g₅ => ?_
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_mov (op2_reg _ _) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  -- What the registers and memory are before the call.
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r7 → s₉.gpr r = s.gpr r := fun r a b c d => by
    rw [u₉.other r c, u₈.other r b, u₇.other r a, u₆.other r d, g₅.gpr, u₄.other r a, u₃.other r b,
      u₂.other r a, h₁.gpr r a]
  have r4₉ : s₉.gpr .r4 = ST s₀ := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r4]
  have r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 (64 * NB s₀) := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), h.r2]
  have hm₉ : s₉.mem = s₁.mem.writeW (st s₀ + BitVec.ofNat 64 48)
      (s₁.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 (NB s₀)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, u₄.gpr, u₃.gpr, u₃.other .r0 (by decide), u₂.gpr,
      u₂.other .r2 (by decide), h₁.gpr .r2 (by decide), h.r2, shr_nb (by omega), u₄.mem, u₃.mem, u₂.mem]
  have x0 : s₉.gpr .r0 = ST s₀ + BitVec.ofNat 32 192 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; rfl
  have x1 : s₉.gpr .r1 = DP s₀ + BitVec.ofNat 32 (H s₀) := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr _ (by decide), h.r5]
  have x3 : s₉.gpr .r3 = ST s₀ + BitVec.ofNat 32 256 := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; rfl
  have x7 : s₉.gpr .r7 = BitVec.ofNat 32 (64 * NB s₀) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr _ (by decide), h.r2]
  have hrd₉ : s₉.rd = [] := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd, h.rd, hp.rd]
  have hwr₉ : s₉.wr = [stR s₀, dR s₀] := by
    rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr, h.wr, hp.wr]
  have hsp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h₁.sp, h.sp]
  have e192 := hp.eaS (d := 192) (by decide)
  have e256 := hp.eaS (d := 256) (by decide)
  have eH := hp.eaD (d := H s₀) (by omega)
  have dSD : (cpR s₀).Disjoint (blR s₀) := (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀)
  have dSB : (cpR s₀).Disjoint (wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dDB : (blR s₀).Disjoint (wkR s₀) := (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀)
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, hHNB⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  refine WP.seq (xor_call (n := 64 * NB s₀) x0 x1 r2₉ x3 (by omega)
    (by rw [e192, eH]; exact dSD) (by rw [e192, e256]; exact dSB) (by rw [eH, e256]; exact dDB)
    (by rw [hp.sNat (by decide)]; omega) (by rw [hp.dNat (by omega)]; omega) (by rw [hp.sNat (by decide)]; omega)
    (by rw [hrd₉, hwr₉, List.nil_append, List.nil_append, e192, eH, e256]; exact Covers.of_sub hcov)
    (by rw [hwr₉, e192, eH, e256]; exact Covers.of_sub hcov) fun s₁₀ k₁₀ x₁₀ => ?_)
  rw [e192, eH, e256] at k₁₀
  rw [e192, eH] at x₁₀
  refine wp_add (op2_reg _ _) fun s₁₁ u₁₁ => wp_sub (op2_reg _ _) fun s₁₂ u₁₂ => WP.block_nil ?_
  have gc : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], s₁₀.gpr r = s₉.gpr r := fun r hr =>
    k₁₀.cs r (kept_cs r hr).1 (kept_cs r hr).2
  have g₁₂ : ∀ r, r ≠ .r5 → r ≠ .r6 → s₁₂.gpr r = s₁₀.gpr r := fun r a b => by
    rw [u₁₂.other r b, u₁₁.other r a]
  have hm : s₁₂.mem = s₁₀.mem := by rw [u₁₂.mem, u₁₁.mem]
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h₁, h₂, h₃]
  have f₁ : Frame [cpR s₀] s.mem s₁.mem := h₁.frame
  have f₉ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₁.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c48s : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have svS := savR_sub s₀
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have st₁ : stateAt s₁.mem (st s₀) = S0 s₀ := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint _ (by omega) (by omega)),
      h.mid.state]
  have e12 : s₁.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (S0 s₀)[12] := by
    rw [← st₁]; simp [stateAt]
  have st₉ : stateAt s₉.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [hm₉, Proof.ChaCha20.Arm.Xor.stateAt_writeW_counter, st₁, e12]; rfl
  have cp₉ : stateAt s₉.mem (st s₀ + BitVec.ofNat 64 192) = S0 s₀ := by
    refine stateAt_congr fun i hi => ?_
    rw [Offset.add_add, hm₉, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
    have := h₁.copied i (by omega)
    rw [Nat.zero_add] at this
    rw [this]
    exact h.mid.keep i (by omega)
  have fc : Frame [cpR s₀, ⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s.mem s₉.mem :=
    (f₁.mono (by simp)).trans (f₉.mono (by simp))
  refine ⟨by rw [g₁₂ _ (by decide) (by decide), gc .r4 (by simp), r4₉], ?_, ?_, fun r hr => ?_,
    by rw [u₁₂.rd, u₁₁.rd, k₁₀.rd, hrd₉, hp.rd], by rw [u₁₂.wr, u₁₁.wr, k₁₀.wr, hwr₉, hp.wr],
    by rw [u₁₂.sp, u₁₁.sp, k₁₀.sp, hsp₉], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, gc .r5 (by simp), gc .r7 (by simp), x7,
      g _ (by decide) (by decide) (by decide) (by decide), h.r5, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), gc .r6 (by simp), u₁₁.other _ (by decide), gc .r7 (by simp), x7,
      g _ (by decide) (by decide) (by decide) (by decide), h.r6, sub_ofNat (by omega), hT, Nat.sub_sub]
  · rw [g₁₂ r (kept_ne hr) (kept_ne hr),
      gc r (by
        simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp),
      g r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr)]
    exact h.keep r hr
  · rw [hm, Proof.ChaCha20.Arm.Xor.stateAt_frame k₁₀.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))), st₉]
  · rw [hm, ← Offset.add_add, k₁₀.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · rw [hm]
    refine (h.mid.saved.frame fc fun r hr => ?_).frame k₁₀.frame (nd _ ?_ (sd _ svS) ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · rw [hm]
    have fcd : s₉.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ds _ _ (fun _ h => h) (cpR_sub s₀)
        · exact ds _ _ (fun _ h => h) c48s) (show L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [k₁₀.frame.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (ds _ _ hpre (cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (wkR_sub s₀)))
          (show H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < H s₀ + 64 * NB s₀
    · have e := xor_getD (length_keystream _ _) x₁₀ (j := k - H s₀) (by omega)
      rw [Offset.add_add, show H s₀ + (k - H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, cp₉,
        keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩ (dR s₀) :=
        Offset.sub_base _ (by omega)
      have := k₁₀.frame.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (ds _ _ hR (cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (wkR_sub s₀))) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · rw [hm]
    refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₁₀.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨stR s₀, by simp, c48s⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨stR s₀, by simp, wkR_sub s₀⟩

theorem part2_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) : WP isa part2 s (Q2 s₀) := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  refine WP.ite (decide (64 * NB s₀ = 0)) (by have e : isa.eval .eq s = some s.z := eval_eq s; rw [e, h.z])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = ST s₀
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0
  saved : Saved s₀ s.mem
  done : Done s₀ (L s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : Q2 s₀ s) (h0 : T s₀ = 0) : Q3 s₀ s := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  refine ⟨h.r4, h.keep, h.rd, h.wr, h.sp, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl,
    h.saved, by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem tailXor_eq : tailXor = .seq (.block [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48,
    .dp .add .r3 .r4 (.imm 64), .mov .r2 (.reg .r6)]) xorBytes := rfl

theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)])
      (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) tailXor)) s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hst := hp.st_fit
  have hd := hp.d_fit
  refine WP.seq (wp_mov (op2_reg _ _) fun s' u => wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have x0₁ : s₁.gpr .r0 = ST s₀ := by rw [u₁.other _ (by decide), u.gpr, h.r4]
  have x1₁ : s₁.gpr .r1 = ST s₀ + BitVec.ofNat 32 64 := by rw [u₁.gpr, u.other _ (by decide), h.r4]; rfl
  have k₁ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r := fun r a b => by rw [u₁.other r b, u.other r a]
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [u₁.wr, u.wr, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [u₁.rd, u.rd, h.rd, hp.rd]
  have e64 := hp.eaS (d := 64) (by decide)
  refine WP.seq (block_call x0₁ x1₁ (by rw [e64]; exact Offset.disjoint_base _ (by omega) (by omega))
    (by omega) (by rw [hp.sNat (by decide)]; omega)
    (by
      rw [hrd₁, hwr₁, e64]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁, e64]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  rw [e64] at k₂ blk₂
  have g : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.cs r (kept_cs r hr).1 (kept_cs r hr).2, k₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have r4₂ : s₂.gpr .r4 = ST s₀ := by rw [g .r4 (by simp), h.r4]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  rw [tailXor_eq]
  refine WP.seq (wp_ldr (a := st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [r4₂]; exact hp.eaS (by decide))
    hr48 fun s₃ u₃ => wp_add (op2_imm imm1) fun s₄ u₄ => ?_)
  refine wp_str (a := st s₀ + BitVec.ofNat 64 48) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r4₂]; exact hp.eaS (by decide))
    (by rw [u₄.wr, u₃.wr]; exact hw48) fun s₅ g₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have g₇ : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s₇.gpr r = s₂.gpr r := fun r a b c => by
    rw [u₇.other r b, u₆.other r c, g₅.gpr, u₄.other r a, u₃.other r a]
  have m₇ : s₇.mem = s₂.mem.writeW (st s₀ + BitVec.ofNat 64 48)
      (s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 + 1) := by
    rw [u₇.mem, u₆.mem, g₅.mem, u₄.gpr, u₃.gpr, u₄.mem, u₃.mem]
  have rd₇ : s₇.rd = s₂.rd := by rw [u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd]
  have wr₇ : s₇.wr = s₂.wr := by rw [u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr]
  have sp₇ : s₇.sp = s₂.sp := by rw [u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp]
  have eD := hp.eaD (d := H s₀ + 64 * NB s₀) (by omega)
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : BPre s₇ (DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)) (ST s₀ + BitVec.ofNat 32 64) (T s₀) :=
    ⟨by rw [g₇ _ (by decide) (by decide) (by decide), g .r5 (by simp), h.r5],
      by rw [u₇.other _ (by decide), u₆.gpr, g₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r4₂]; rfl,
      by rw [u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        g .r6 (by simp), h.r6],
      by rw [hp.dNat (by omega)]; omega, by rw [hp.sNat (by decide)]; omega,
      fun k hk => by
        rw [wr₇, k₂.wr, hwr₁, eD, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₇, wr₇, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, e64, Offset.add_add]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [eD, e64, Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₈ h₈ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₄ := h₈.frame
  rw [eD] at f₄
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have hm₁ : s₁.mem = s.mem := by rw [u₁.mem, u.mem]
  rw [hm₁] at f₂ blk₂
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, h.state]
  have b3 : ∀ i < 64, s₇.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₇]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₈.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₇.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact f₄.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₈.rd, rd₇, k₂.rd, hrd₁, hp.rd], by rw [h₈.wr, wr₇, k₂.wr, hwr₁, hp.wr],
    by rw [h₈.sp, sp₇, k₂.sp, u₁.sp, u.sp, h.sp], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₈.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₇ _ (by decide) (by decide) (by decide), r4₂]
  · rw [h₈.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g₇ r (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g r (by
        simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₇, Proof.ChaCha20.Arm.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame f₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₇.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (bufR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by omega) hk]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [f₄.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₈.data (k - (H s₀ + 64 * NB s₀)) (by omega)
      rw [eD, e64, Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega]
  · refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

theorem part3_eq : part3 = .seq (.block [.cmp .r6 (.imm 0)]) (.ite .eq (.block [])
    (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)])
      (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) tailXor))) := rfl

theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  rw [part3_eq]
  refine WP.seq (wp_cmp (n := .r6) (op2_imm imm0) fun s₁ f₁ hz => WP.block_nil ?_)
  have h₁ : Q2 s₀ s₁ := ⟨by rw [f₁.gpr, h.r4], by rw [f₁.gpr, h.r5], by rw [f₁.gpr, h.r6],
    fun r hr => by rw [f₁.gpr, h.keep r hr], by rw [f₁.rd, h.rd], by rw [f₁.wr, h.wr], by rw [f₁.sp, h.sp],
    by rw [f₁.mem, h.state], fun i hi => by rw [f₁.mem, h.buf i hi], f₁.mem ▸ h.saved, f₁.mem ▸ h.done,
    f₁.mem ▸ h.frame⟩
  refine WP.ite (decide (T s₀ = 0)) (by
      have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
      rw [e, hz, h.r6, sub_zero', ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have e : ∀ d, d < 768 → State.addr (s.gpr .r4 + BitVec.ofNat 32 d) = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.r4]; exact hp.eaS hd
  have w : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e128 := e 128 (by decide); have e132 := e 132 (by decide); have e576 := e 576 (by decide)
  have e580 := e 580 (by decide); have e584 := e 584 (by decide); have e588 := e 588 (by decide)
  have e592 := e 592 (by decide); have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o128 := w 128 (by decide); have o132 := w 132 (by decide)
  have i576 := r 576 (by decide); have i580 := r 580 (by decide); have i584 := r 584 (by decide)
  have i588 := r 588 (by decide); have i592 := r 592 (by decide); have i600 := r 600 (by decide)
  have i604 := r 604 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.store32, State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true,
    ite_false, e128, e132, e576, e580, e584, e588, e592, e600, e604, o128, o132, i576, i580, i584, i588, i592,
    i600, i604, readW_writeW_ofNat, h.saved.lo, h.saved.hi, h.saved.r4, h.saved.r5, h.saved.r6, h.saved.r7,
    h.saved.lr]
  have hfw : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (N s₀ - L s₀))).writeW
        (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (st s₀) (e := 128) (d := 128) (k := 8) (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (st s₀) (e := 128) (d := 132) (k := 8) (by omega) (by omega) (by omega))
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (N s₀ - L s₀))).writeW
      (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) (st s₀) =
      ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨⟨fun r hr => ?_, h.sp⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp (config := {decide := true}) only [ite_true, ite_false]
    all_goals exact h.keep _ (by simp [kept])
  · have hd : ∀ k < L s₀, ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (N s₀ - L s₀))).writeW
        (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)))
        (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by simp (config := {decide := true}), apply_data hle fun k hk => ?_,
      apply_rest hle ?_ hS fun i hi => ?_⟩
    · dsimp only
      rw [hd k hk, h.done k hk, ite_pos hk]
    · dsimp only
      rw [leftAt_halves _ _ (by omega)]
    · dsimp only
      rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
        byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq : apply = .seq (.block check)
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.seq part1 (.seq part2 (.seq part3 (.block finish))))) := rfl

theorem apply_correct {s₀ : State} (hp : APre s₀) : WP isa apply s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by
      have e : isa.eval .eq s = some s.z := eval_eq s
      rw [e, h.z])
    (fun hlt => fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.Arm.Stream
