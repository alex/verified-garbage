import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Calls

/-!
# Streaming ChaCha20 on x86 (32-bit): `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/X86/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function. The pieces are those that the proof
of constant time (`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off)
open VG.Proof.ChaCha20.X86.Xor (toNat_ofNat_lt32 ptr_add)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The check -/

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4))]) s₀ fun s => s = s₀.setReg .eax (ST s₀) := by
  have i₀ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 := hp.in_arg (i := 0) (by decide)
  have v₀ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = ST s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₀, v₀, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- After the check: `edx:ecx` holds the bytes left less `len` (modulo
2⁶⁴), and the borrow whether fewer than `len` are left. -/
structure Q0 (s₀ s : State) : Prop where
  eax : s.gpr .eax = ST s₀
  pair : Pair s ((N s₀ + 2 ^ 64 - L s₀) % 2 ^ 64)
  cf : s.cf = some (decide (N s₀ < L s₀))
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) (s₀.setReg .eax (ST s₀)) (Q0 s₀) := by
  have i₂ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 := hp.in_arg (i := 2) (by decide)
  have v₂ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = LN s₀ := rfl
  have e₁ := hp.eaS (d := 128) (by decide); have e₂ := hp.eaS (d := 132) (by decide)
  have j₁ := hp.r_st (d := 128) (n := 4) (by decide); have j₂ := hp.r_st (d := 132) (n := 4) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, execAlu, arithFlags, State.setReg, State.setFlags, i₂, v₂, e₁, e₂, j₁, j₂,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hN : N s₀ = (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat +
      2 ^ 32 * (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32).toNat := by
    simp only [N, leftAt]
    rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat, Offset.add_add]
  have hL : L s₀ = (LN s₀).toNat := rfl
  refine ⟨by simp (config := {decide := true}), ?_, ?_, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], rfl, rfl, rfl⟩
  all_goals simp (config := {decide := true}) only [Pair, ite_true, ite_false]
  all_goals
    have ha := (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).isLt
    have hb := (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32).isLt
    have hl := (LN s₀).isLt
    rw [hN, hL]
    generalize s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32 = a at *
    generalize s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32 = b at *
    generalize LN s₀ = l at *
  · rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    by_cases hc : a.toNat < l.toNat
    · simp only [hc, decide_true, Bool.toNat_true]; simp; omega
    · simp only [hc, decide_false, Bool.toNat_false]; simp; omega
  · congr 1
    by_cases hc : a.toNat < l.toNat
    · simp only [hc, decide_true, Bool.toNat_true]; simp; omega
    · simp only [hc, decide_false, Bool.toNat_false]; simp; omega

/-- What `apply` guarantees (`applyX86`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.ChaCha20.applyX86.post s₀ s

set_option simprocs false in
theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.mov .eax (.imm 0)]) s (Final s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, h.mem]⟩, ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (calleeSaved_ne hr).1]
    exact h.keep r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.1 (calleeSaved_ne hr).2.2
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega)]
    rw [RegUpd.mem_setReg, h.mem]
    exact ⟨rfl, RegUpd.gpr_setReg_self .., rfl, rfl⟩

/-! ## The bytes left in the buffered block -/

/-- `and` with `0xffffffc0` rounds down to a multiple of 64. -/
theorem and_mask (x : BitVec 32) : x &&& (0xffffffc0 : BitVec 32) = BitVec.ofNat 32 (x.toNat / 64 * 64) := by
  have : (0xffffffc0 : BitVec 32) = BitVec.ofNat 32 ((2 ^ 26 - 1) <<< 6) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 64 * 64 = (n >>> 6) <<< 6 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 6 ≤ i
  · by_cases h2 : i - 6 < 26
    · simp [hi, h2, show 6 + (i - 6) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 6 + (i - 6) = i by omega]
  · simp [hi]

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 32) : x &&& (63 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 64) := by
  have : (63 : BitVec 32) = BitVec.ofNat 32 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Our caller's `ebx, esi, edi, ebp`, and the bytes left after `apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  ebx : m.readW (st s₀ + BitVec.ofNat 64 576) 32 = s₀.gpr .ebx
  esi : m.readW (st s₀ + BitVec.ofNat 64 580) 32 = s₀.gpr .esi
  edi : m.readW (st s₀ + BitVec.ofNat 64 584) 32 = s₀.gpr .edi
  ebp : m.readW (st s₀ + BitVec.ofNat 64 588) 32 = s₀.gpr .ebp
  lo : m.readW (st s₀ + BitVec.ofNat 64 600) 32 = BitVec.ofNat 32 (N s₀ - L s₀)
  hi : m.readW (st s₀ + BitVec.ofNat 64 604) 32 = BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 576, 32⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 4 ≤ 608 → (savR s₀).Contains (st s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.ebx],
    by rw [hf.readW (c 580 (by decide) (by decide)) hd (by decide), h.esi],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.edi],
    by rw [hf.readW (c 588 (by decide) (by decide)) hd (by decide), h.ebp],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.lo],
    by rw [hf.readW (c 604 (by decide) (by decide)) hd (by decide), h.hi]⟩

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- The memory after `start`'s stores. -/
def startMem (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) : Mem :=
  (((((m.writeW (st + BitVec.ofNat 64 576) b).writeW (st + BitVec.ofNat 64 580) si).writeW
    (st + BitVec.ofNat 64 584) di).writeW (st + BitVec.ofNat 64 588) bp).writeW (st + BitVec.ofNat 64 600) lo).writeW
    (st + BitVec.ofNat 64 604) hi

theorem startMem_frame (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) :
    Frame [⟨st, 768⟩] m (startMem m st b si di bp lo hi) := by
  have c : ∀ d, d + 4 ≤ 768 → (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by omega)
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 580 (by decide))).writeW (List.mem_singleton_self _) _
    (c 584 (by decide))).writeW (List.mem_singleton_self _) _ (c 588 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 600 (by decide))).writeW (List.mem_singleton_self _) _ (c 604 (by decide))

set_option simprocs false in
theorem startMem_read (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) {d : Nat} (hd : d + 4 ≤ 576) :
    (startMem m st b si di bp lo hi).readW (st + BitVec.ofNat 64 d) 32 = m.readW (st + BitVec.ofNat 64 d) 32 := by
  simp only [startMem]
  rw [readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega)]

theorem startMem_byte (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) {i : Nat} (hi' : i < 576) :
    (startMem m st b si di bp lo hi) (st + BitVec.ofNat 64 i) = m (st + BitVec.ofNat 64 i) := by
  simp only [startMem]
  rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]

set_option simprocs false in
theorem startMem_saved (s₀ : State) :
    Saved s₀ (startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
      (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (config := {decide := true}) only [startMem, Mem.readW_writeW_self32, readW_ofNat32]

def startStores : List Instr :=
  [.store (at_ .eax 576) .ebx, .store (at_ .eax 580) .esi, .store (at_ .eax 584) .edi,
   .store (at_ .eax 588) .ebp, .store (at_ .eax 600) .ecx, .store (at_ .eax 604) .edx]

def startLoads : List Instr :=
  [.mov .ebx (.reg .eax), .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)),
   .mov .eax (.mem (at_ .ebx 128)), .alu .and .eax (.imm 63), .mov .ecx (.reg .ebp),
   .alu .cmp .eax (.reg .ebp)]

theorem start_eq : start = startStores ++ startLoads := rfl

/-- After `start`, with `x` in `ecx`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀
  ebp : s.gpr .ebp = LN s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 x
  eax : s.gpr .eax = BitVec.ofNat 32 (O s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

set_option simprocs false in
theorem startStores_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block startStores) s fun s' => s'.gpr = s.gpr ∧
      s'.mem = startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
        (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ⟨hecx, hedx⟩ := pair_eq h.pair (by omega)
  rw [show (N s₀ + 2 ^ 64 - L s₀) % 2 ^ 64 = N s₀ - L s₀ by have := N_lt s₀; omega] at hecx hedx
  have e : ∀ d, d < 768 → (s.gpr .eax + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.eax]; exact hp.eaS hd
  have o : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have e576 := e 576 (by decide); have e580 := e 580 (by decide); have e584 := e 584 (by decide)
  have e588 := e 588 (by decide); have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o576 := o 576 (by decide); have o580 := o 580 (by decide); have o584 := o 584 (by decide)
  have o588 := o 588 (by decide); have o600 := o 600 (by decide); have o604 := o 604 (by decide)
  have kb := h.keep .ebx (by decide) (by decide) (by decide)
  have ks := h.keep .esi (by decide) (by decide) (by decide)
  have kd := h.keep .edi (by decide) (by decide) (by decide)
  have kp := h.keep .ebp (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [startStores, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, at_, State.store32, e576, e580, e584, e588, e600, e604, o576, o580, o584, o588, o600, o604,
    kb, ks, kd, kp, hecx, hedx, h.mem, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, trivial⟩

theorem lo_mod (s₀ : State) : (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat % 64 = O s₀ := by
  simp only [O, N, leftAt]
  rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat]
  omega

set_option simprocs false in
theorem startLoads_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q0 s₀ s) {s₁ : State} (g₁ : s₁.gpr = s.gpr)
    (m₁ : s₁.mem = startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
        (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)))
    (r₁ : s₁.rd = s.rd) (w₁ : s₁.wr = s.wr) :
    WP isa (.block startLoads) s₁ fun s' => R1 s₀ (L s₀) s' ∧ s'.cf = some (decide (O s₀ < L s₀)) := by
  have hf := startMem_frame s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
    (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))
  have ha : ∀ i, i < 3 → (startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
      (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))).readW (argAddr s₀ i) 32 =
      arg s₀ i := fun i hi =>
    hf.readW (arg_in s₀ (n := 3) (by have := hp.sp_hi; omega) hi) (by simpa using hp.a_st) (by decide)
  have gesp : s₁.gpr .esp = E s₀ := by rw [g₁, h.keep .esp (by decide) (by decide) (by decide)]
  have geax : s₁.gpr .eax = ST s₀ := by rw [g₁, h.eax]
  have i₁ : InRegions (s₁.rd ++ s₁.wr) ((E s₀ + BitVec.ofNat 32 8).setWidth 64) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.in_arg (i := 1) (by decide)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) ((E s₀ + BitVec.ofNat 32 12).setWidth 64) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.in_arg (i := 2) (by decide)
  have v₁ := ha 1 (by decide)
  have v₂ := ha 2 (by decide)
  have e₃ := hp.eaS (d := 128) (by decide)
  have i₃ : InRegions (s₁.rd ++ s₁.wr) (st s₀ + BitVec.ofNat 64 128) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.r_st (by decide)
  have v₃ := startMem_read s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
    (BitVec.ofNat 32 (N s₀ - L s₀)) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32)) (d := 128) (by decide)
  simp only [argAddr] at v₁ v₂
  apply WP.of_runBlock
  simp (config := {decide := true}) only [startLoads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, execAlu, arithFlags, State.setReg, State.setFlags, gesp, geax, m₁, i₁, i₂, i₃,
    v₁, v₂, e₃, v₃, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_63, lo_mod]
  have hO : O s₀ < 2 ^ 32 := by have := O_lt s₀; omega
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}) [L],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [gesp], by rw [r₁, h.rd],
    by rw [w₁, h.wr], ⟨fun i hi => startMem_byte _ _ _ _ _ _ _ _ (by omega), startMem_saved s₀⟩,
    fun k hk => ?_, hf⟩, ?_⟩
  · dsimp only
    rw [hf.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    simp
  · simp only [Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 hO]

theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.cf = some (decide (O s₀ < L s₀)) := by
  rw [start_eq, WP.block_append_iff]
  exact WP.mono (startStores_ok hp hle h) fun s₁ ⟨g₁, m₁, r₁, w₁⟩ => startLoads_ok hp h g₁ m₁ r₁ w₁

set_option simprocs false in
theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s) (hc : s.cf = some (decide (O s₀ < L s₀))) :
    WP isa (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by show eval .b s = _; simp only [eval, hc]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .ecx → (s.setReg .ecx (s.gpr .eax)).gpr r = s.gpr r := fun r hr =>
      RegUpd.gpr_setReg_of_ne _ _ hr
    exact ⟨by rw [g _ (by decide), h.ebx], by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.ebp],
      by rw [RegUpd.gpr_setReg_self, h.eax, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [g _ (by decide), h.eax], by rw [g _ (by decide), h.esp], h.rd, h.wr, h.mid, h.done, h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.ebx, h.esi, h.ebp, ?_, h.eax, h.esp, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.ecx, H, headLen, bufLeft, Nat.min_eq_right hge]

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- After the pointer to the bytes left in the buffered block is computed. -/
structure R2 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (H s₀)
  edx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 (128 - O s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

set_option simprocs false in
theorem ptr_ok {s₀ : State} {s : State} (h : R1 s₀ (H s₀) s) :
    WP isa (.block (ptr .edx .ebx 128 ++ [.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)])) s (R2 s₀) := by
  have hO := O_lt s₀
  have hH := H_le s₀
  have hL := L_lt s₀
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨by simp (config := {decide := true}) [h.ebx], by simp (config := {decide := true}) [h.esi], ?_,
    by simp (config := {decide := true}) [h.ecx], ?_, by simp (config := {decide := true}) [h.esp], h.rd, h.wr,
    h.mid, h.done, h.frame⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ebp, h.ecx]
    rw [show LN s₀ = BitVec.ofNat 32 (L s₀) by simp [L], sub_ofNat32 hH]
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ebx, h.eax]
    rw [show (128#32 : BitVec 32) = BitVec.ofNat 32 (128 - O s₀) + BitVec.ofNat 32 (O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - O s₀ + O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- After `part1`: the bytes from the buffered block XORed, and `ecx` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (64 * NB s₀)
  zf : s.zf = some (decide (64 * NB s₀ = 0))
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem part1_eq : part1 = .seq (.block start)
    (.seq (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block []))
    (.seq (.block (ptr .edx .ebx 128 ++ [.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)]))
    (.seq xorBytes (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)])))) := rfl

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  rw [part1_eq]
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ hc₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (ptr_ok h₂) fun s₃ h₃ => ?_)
  have eK : (ST s₀ + BitVec.ofNat 32 (128 - O s₀)).setWidth 64 = st s₀ + BitVec.ofNat 64 (128 - O s₀) :=
    hp.eaS (by omega)
  have hb : BPre s₃ (DP s₀) (ST s₀ + BitVec.ofNat 32 (128 - O s₀)) (H s₀) :=
    ⟨h₃.esi, h₃.edx, h₃.ecx, by omega, by rw [hp.sNat (by omega)]; omega,
      fun k hk => ⟨dR s₀, by rw [h₃.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by rw [h₃.rd, h₃.wr, eK, Offset.add_add]; exact hp.r_st (by omega),
      fun j hj k hk => by rw [eK, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hebp : s₄.gpr .ebp = BitVec.ofNat 32 (L s₀ - H s₀) := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide), h₃.ebp]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, hebp, and_mask,
    Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 (show L s₀ - H s₀ < 2 ^ 32 by omega)]
  have hnb : (L s₀ - H s₀) / 64 * 64 = 64 * NB s₀ := by simp only [NB, blocksOf, H]; omega
  rw [hnb]
  have hk4 : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₄.gpr r = s₃.gpr r := h₄.keep
  refine ⟨by simp (config := {decide := true}) [hk4 .ebx (by decide) (by decide) (by decide) (by decide), h₃.ebx],
    by simp (config := {decide := true}) [h₄.esi], by simp (config := {decide := true}) [hebp],
    by simp (config := {decide := true}), ?_,
    by simp (config := {decide := true}) [hk4 .esp (by decide) (by decide) (by decide) (by decide), h₃.esp],
    by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [ofNat32_beq_zero (by omega)]
  · rw [h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · dsimp only
    by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, eK, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)

end VG.Proof.ChaCha20.X86.Stream
