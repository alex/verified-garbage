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
    WP isa (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr))) s (R2 s₀) := by
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
    (.seq (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr)))
    (.seq xorBytes (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)])))) := rfl

/-- The rest of `part1`, after the selection. -/
abbrev rest1 : Prog isa :=
  .seq (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr)))
    (.seq xorBytes (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)]))

set_option simprocs false in
theorem rest1_ok {s₀ : State} (hp : APre s₀) {s₂ : State} (h₂ : R1 s₀ (H s₀) s₂) :
    WP isa rest1 s₂ (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
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

theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  rw [part1_eq]
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  exact WP.seq (WP.mono (sel_ok h₁ hc₁) fun s₂ h₂ => rest1_ok hp h₂)

/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state copied to
`st + 192`, 16 bytes at a time. -/
def copyMem8 (m : Mem) (st : Addr) : Mem :=
  (((m.writeW (st + BitVec.ofNat 64 192) (m.readW (st + BitVec.ofNat 64 0) 128)).writeW (st + BitVec.ofNat 64 208)
    (m.readW (st + BitVec.ofNat 64 16) 128)).writeW (st + BitVec.ofNat 64 224) (m.readW (st + BitVec.ofNat 64 32) 128)).writeW
    (st + BitVec.ofNat 64 240) (m.readW (st + BitVec.ofNat 64 48) 128)

/-- And its counter advanced by `c`. -/
def copyMem (m : Mem) (st : Addr) (c : BitVec 32) : Mem :=
  (copyMem8 m st).writeW (st + BitVec.ofNat 64 48) (c + m.readW (st + BitVec.ofNat 64 48) 32)

/-- The arguments of `vg_chacha20_xor`, after the copy. -/
structure Args (s₀ s : State) : Prop where
  edx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (64 * NB s₀)
  eax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256
  edi : s.gpr .edi = BitVec.ofNat 32 (64 * NB s₀)
  ebx : s.gpr .ebx = ST s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - H s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 32) : BitVec.ofNat 32 (64 * nb) >>> 6 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow]
  omega

set_option simprocs false in
theorem args_exec {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = copyMem s.mem (st s₀) (BitVec.ofNat 32 (NB s₀)) ∧ Args s₀ s' := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  have e : ∀ d, d < 768 → (s.gpr .ebx + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.ebx]; exact hp.eaS hd
  have o : ∀ d n, d + n ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d n, d + n ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e0 := e 0 (by decide); have e16 := e 16 (by decide); have e32 := e 32 (by decide)
  have e48 := e 48 (by decide); have e192 := e 192 (by decide); have e208 := e 208 (by decide)
  have e224 := e 224 (by decide); have e240 := e 240 (by decide)
  have i0 := r 0 16 (by decide); have i16 := r 16 16 (by decide); have i32 := r 32 16 (by decide)
  have i48 := r 48 16 (by decide); have i48' := r 48 4 (by decide)
  have o192 := o 192 16 (by decide); have o208 := o 208 16 (by decide); have o224 := o 224 16 (by decide)
  have o240 := o 240 16 (by decide); have o48 := o 48 4 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, ptr, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32, State.load128, State.store32,
    State.store128, execAlu, execShift, arithFlags, State.setReg, State.setXmm, State.setFlags, e0, e16, e32, e48,
    e192, e208, e224, e240, i0, i16, i32, i48, i48', o192, o208, o224, o240, o48, h.ecx,
    readW_writeW_ofNat, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', shr_eq (show 64 * NB s₀ < 2 ^ 32 by omega)]
  refine ⟨rfl, by simp (config := {decide := true}) [h.ebx], by simp (config := {decide := true}) [h.esi],
    by simp (config := {decide := true}) [h.ecx], by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}) [h.ebp], by simp (config := {decide := true}) [h.esp], h.rd, h.wr⟩

theorem readW_writeW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem copyMem8_frame (m : Mem) (st : Addr) : Frame [⟨st + BitVec.ofNat 64 192, 64⟩] m (copyMem8 m st) := by
  have c : ∀ d, 192 ≤ d → d + 16 ≤ 256 →
      (⟨st + BitVec.ofNat 64 192, 64⟩ : Region).Contains (st + BitVec.ofNat 64 d) (128 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (c 224 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem copyMem_frame (m : Mem) (st : Addr) (c : BitVec 32) :
    Frame [⟨st, 64⟩, ⟨st + BitVec.ofNat 64 192, 64⟩] m (copyMem m st c) :=
  ((copyMem8_frame m st).mono (by simp)).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))

set_option simprocs false in
/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (st : Addr) (c : BitVec 32) :
    stateAt (copyMem m st c) (st + BitVec.ofNat 64 192) = stateAt m st := by
  refine stateAt_congr fun i hi => ?_
  rw [copyMem, Offset.add_add, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  have hw : ∀ k, 12 ≤ k → k < 16 → (copyMem8 m st).readW (st + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (st + BitVec.ofNat 64 (16 * (k - 12))) 128 := by
    intro k h₁ h₂
    simp only [copyMem8]
    obtain rfl | rfl | rfl | rfl : k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    all_goals simp (config := {decide := true}) only [readW_writeW_self128,
      readW_writeW_ofNat]
  have hm : ∀ k, 0 ≤ k → k < 4 → m.readW (st + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (st + BitVec.ofNat 64 (16 * k)) 128 := fun _ _ _ => rfl
  rw [byte_of_words128 hw (by omega) (by omega), byte_of_words128 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 16 - 12 = i / 16 by omega, show (192 + i) % 16 = i % 16 by omega]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (st : Addr) (c : BitVec 32) :
    stateAt (copyMem m st c) st = (stateAt m st).set 12 ((stateAt m st)[12] + c) := by
  rw [copyMem, Proof.ChaCha20.X86.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.X86.Xor.stateAt_frame (copyMem8_frame m st) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), BitVec.add_comm]
  simp [stateAt]

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (T s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀, stkR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.ebx, by rw [h.esi, h0, Nat.add_zero], by rw [h.ebp, hT, h0, Nat.sub_zero], h.esp, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame.mono (by simp)⟩

theorem part2_eq : part2 = .ite .e (.block [])
    (.seq (.block blocksArgs) (.seq callXor (.block [.alu .add .esi (.reg .edi), .alu .sub .ebp (.reg .edi)]))) := rfl

set_option simprocs false in
theorem blocks_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) (hnb : 0 < NB s₀) :
    WP isa (.seq (.block blocksArgs) (.seq callXor (.block [.alu .add .esi (.reg .edi), .alu .sub .ebp (.reg .edi)])))
      s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  have hd := hp.d_fit
  refine WP.seq (WP.mono (args_exec hp h) fun s₁ ⟨m₁, a₁⟩ => ?_)
  refine WP.seq (xor_call hp ⟨a₁.esp, a₁.rd, a₁.wr⟩ hnb a₁.edx a₁.esi a₁.ecx a₁.eax fun s₂ at₂ cs₂ f₂ x₂ => ?_)
  have g : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s₂.gpr r = s₁.gpr r :=
    fun r hr => cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])
  have gsi := g .esi (by simp); have gdi := g .edi (by simp); have gbp := g .ebp (by simp)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_false, gsi, gdi, gbp, a₁.esi, a₁.edi, a₁.ebp]
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      R.Disjoint (stkR s₀) → ∀ r ∈ [cpR s₀, blR s₀, wkR s₀, stkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁, h₂, h₃, h₄]
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁, h₂]
  have fc := copyMem_frame s.mem (st s₀) (BitVec.ofNat 32 (NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have cpS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ (stR s₀) := cpR_sub s₀
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have svS := savR_sub s₀
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have sk : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_st.symm.sub_left hR
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have dk : ∀ R, Region.Sub R (dR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_d.symm.sub_left hR
  refine ⟨by simp (config := {decide := true}) [g .ebx (by simp), a₁.ebx], ?_, ?_,
    by simp (config := {decide := true}) [g .esp (by simp), a₁.esp], by rw [at₂.rd], by rw [at₂.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [sub_ofNat32 (by omega), hT, Nat.sub_sub]
  · rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega)) (sk _ stS)),
      m₁, copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, f₂.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sk _ bufS)) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame f₂ (nd _ ?_ (sd _ svS) ?_ (sk _ svS))
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) cpS))
        (show L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [f₂.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (ds _ _ hpre (cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (wkR_sub s₀)) (dk _ hpre))
          (show H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < H s₀ + 64 * NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - H s₀) (by omega)
      rw [Offset.add_add, show H s₀ + (k - H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, m₁,
        copyMem_copy, h.mid.state, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩ (dR s₀) :=
        Offset.sub_base _ (by omega)
      have := f₂.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (ds _ _ hR (cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (wkR_sub s₀)) (dk _ hR)) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine ((h.frame.mono (by simp)).trans (fc.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, stS⟩
      · exact ⟨stR s₀, by simp, cpS⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨stR s₀, by simp, wkR_sub s₀⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem part2_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) : WP isa part2 s (Q2 s₀) := by
  rw [part2_eq]
  refine WP.ite (decide (64 * NB s₀ = 0)) (by show eval .e s = _; simp only [eval, h.zf])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0
  saved : Saved s₀ s.mem
  done : Done s₀ (L s₀) s.mem
  frame : Frame [stR s₀, dR s₀, stkR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : Q2 s₀ s) (h0 : T s₀ = 0) : Q3 s₀ s := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  refine ⟨h.ebx, h.esp, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

set_option simprocs false in
theorem tailPtr_ok {s₀ : State} {s : State} (h : Q2 s₀ s) :
    WP isa (.block (ptr .eax .ebx 64)) s fun s' => s'.gpr .eax = ST s₀ + BitVec.ofNat 32 64 ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', ite_true, h.ebx]
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

set_option simprocs false in
/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {S : BitVec 32} (hebx : s.gpr .ebx = S)
    (he : (S + BitVec.ofNat 32 48).setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 48)
    (hw : InRegions s.wr (S.setWidth 64 + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (([.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1), .store (at_ .ebx 48) .eax] : List Instr) ++
      ptr .edx .ebx 64 ++ ([.mov .ecx (.reg .ebp)] : List Instr))) s fun s' =>
      s'.mem = s.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 48) (s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .edx = S + BitVec.ofNat 32 64 ∧ s'.gpr .ecx = s.gpr .ebp ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.ea, at_, State.load32, State.store32, execAlu, arithFlags, State.setReg,
    State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false,
    hebx, he, hw, hr]
  exact ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

theorem tailXor_eq : tailXor = .seq (.block (([.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1),
    .store (at_ .ebx 48) .eax] : List Instr) ++ ptr .edx .ebx 64 ++ ([.mov .ecx (.reg .ebp)] : List Instr))) xorBytes := rfl

set_option simprocs false in
theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block (ptr .eax .ebx 64)) (.seq callBlock tailXor)) s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have hd := hp.d_fit
  have hst := hp.st_fit
  refine WP.seq (WP.mono (tailPtr_ok h) fun s₁ ⟨eax₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have at₁ : At s₀ s₁ := ⟨by rw [k₁ _ (by decide), h.esp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
  refine WP.seq (block_call hp at₁ (by rw [k₁ _ (by decide), h.ebx]) eax₁ fun s₂ at₂ cs₂ f₂ blk₂ => ?_)
  have g : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s₂.gpr r = s.gpr r := fun r hr => by
    rw [cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwr₂ : s₂.wr = [stR s₀, dR s₀, aR s₀] := by rw [at₂.wr, hp.wr]
  have hrd₂ : s₂.rd = [] := by rw [at₂.rd, hp.rd]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by rw [at₂.wr]; exact hp.w_st (by decide)
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [at₂.rd, at₂.wr]; exact hp.r_st (by decide)
  rw [tailXor_eq]
  refine WP.seq (WP.mono (ctr_exec (by rw [g .ebx (by simp), h.ebx]) (hp.eaS (by decide)) hw48 hr48)
    fun s₃ ⟨m₃, edx₃, ecx₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hesi₃ : s₃.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀) := by
    rw [k₃ .esi (by decide) (by decide) (by decide), g .esi (by simp), h.esi]
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have eD : (DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)).setWidth 64 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) :=
    hp.eaD (by omega)
  have eK : (ST s₀ + BitVec.ofNat 32 64).setWidth 64 = st s₀ + BitVec.ofNat 64 64 := hp.eaS (by decide)
  have hb : BPre s₃ (DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)) (ST s₀ + BitVec.ofNat 32 64) (T s₀) :=
    ⟨hesi₃, edx₃, by rw [ecx₃, g .ebp (by simp), h.ebp], by rw [hp.dNat (by omega)]; omega,
      by rw [hp.sNat (by decide)]; omega,
      fun k hk => by
        rw [wr₃, at₂.wr, hp.wr, eD, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by rw [rd₃, wr₃, at₂.rd, at₂.wr, eK, Offset.add_add]; exact hp.r_st (by omega),
      fun j hj k hk => by rw [eD, eK, Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) := Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact hp.stk_st.symm.sub_left stS),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eD]; exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  have f₄ : Frame [⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [eD] at this
  refine ⟨?_, ?_, by rw [h₄.rd, rd₃, at₂.rd], by rw [h₄.wr, wr₃, at₂.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide),
      k₃ .ebx (by decide) (by decide) (by decide), g .ebx (by simp), h.ebx]
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide),
      k₃ .esp (by decide) (by decide) (by decide), g .esp (by simp), h.esp]
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.X86.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame f₄ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact hp.stk_st.symm.sub_left svS
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dS _ _ (fun _ h => h) (bufR_sub s₀)
          · exact hp.stk_d.symm) (show L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [f₄.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (H s₀ + 64 * NB s₀)) (by omega)
      rw [eD, eK, Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, bufR_sub s₀⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

theorem part3_eq : part3 = .seq (.block [.alu .test .ebp (.reg .ebp)])
    (.ite .e (.block []) (.seq (.block (ptr .eax .ebx 64)) (.seq callBlock tailXor))) := rfl

set_option simprocs false in
theorem test_ok {s₀ : State} {s : State} (h : Q2 s₀ s) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun s₁ => Q2 s₀ s₁ ∧ s₁.zf = some (decide (T s₀ = 0)) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.ebx, h.esi, h.ebp, h.esp, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
  rw [BitVec.and_self, h.ebp, ofNat32_beq_zero (by omega)]

theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  rw [part3_eq]
  refine WP.seq (WP.mono (test_ok h) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (T s₀ = 0)) (by show eval .e s₁ = _; simp only [eval, hz])
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

theorem retR_stkR (s₀ : State) (hp : APre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_lo
  have := hp.sp_hi
  simp only [retR, stkR, below]
  rw [hp.E64 (by decide)]
  exact Offset.base_disjoint_below _ (n := 32) (k := 4) (by decide)

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have e : ∀ d, d < 768 → (s.gpr .ebx + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.ebx]; exact hp.eaS hd
  have w : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e128 := e 128 (by decide); have e132 := e 132 (by decide); have e576 := e 576 (by decide)
  have e580 := e 580 (by decide); have e584 := e 584 (by decide); have e588 := e 588 (by decide)
  have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o128 := w 128 (by decide); have o132 := w 132 (by decide)
  have i576 := r 576 (by decide); have i580 := r 580 (by decide); have i584 := r 584 (by decide)
  have i588 := r 588 (by decide); have i600 := r 600 (by decide); have i604 := r 604 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, State.store32, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false, e128, e132, e576, e580, e584, e588, e600, e604, o128, o132, i576, i580,
    i584, i588, i600, i604, readW_writeW_ofNat, h.saved.lo, h.saved.hi, h.saved.ebx, h.saved.esi, h.saved.edi,
    h.saved.ebp]
  have hfw : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (N s₀ - L s₀))).writeW
        (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (st s₀) (e := 128) (d := 128) (k := 8) (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (st s₀) (e := 128) (d := 132) (k := 8) (by omega) (by omega) (by omega))
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have hF := h.frame.trans (hfw.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c128⟩)
  have hS : stateAt ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (N s₀ - L s₀))).writeW
      (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((N s₀ - L s₀) / 2 ^ 32))) (st s₀) =
      ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals simp (config := {decide := true}) only [ite_true, ite_false, h.esp]
  · exact hF.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d
      · exact retR_stkR s₀ hp) (by decide)
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

theorem apply_eq : apply = .seq (.block [.mov .eax (.mem (at_ .esp 4))]) (.seq (.block check)
    (.ite .b (.block [.mov .eax (.imm 0)]) (.seq part1 (.seq part2 (.seq part3 (.block finish)))))) := rfl

theorem apply_correct {s₀ : State} (hp : APre s₀) : WP isa apply s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (load_ok hp) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by show eval .b s = _; simp only [eval, h.cf])
    (fun hlt => fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.X86.Stream
