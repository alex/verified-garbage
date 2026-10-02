import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Calls

/-!
# Streaming ChaCha20 on AArch64: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/AArch64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, for any implementation `v` of
`vg_chacha20_xor`. The pieces are those that the proof of constant time
(`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20

open VG.AArch64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- AArch64 contract for `vg_chacha20_apply(state = x0, data = x1, len = x2) -> w0`.
The return address is in `x30`, which the code saves in the state, so no
stack is used. -/
def applyAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 768⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .x0).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .x0) = keyAt s.mem (s.gpr .x0) ∧
      if (s.gpr .x2).toNat ≤ leftAt s.mem (s.gpr .x0) then
        (s'.gpr .x0).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
              ((restAt s.mem (s.gpr .x0)).take (s.gpr .x2).toNat) ∧
          restAt s'.mem (s.gpr .x0) = (restAt s.mem (s.gpr .x0)).drop (s.gpr .x2).toNat
      else
        (s'.gpr .x0).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat = bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat ∧
          restAt s'.mem (s.gpr .x0) = restAt s.mem (s.gpr .x0)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (s₁.gpr .x0)] = [leftAt s₂.mem (s₂.gpr .x0)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)
open VG.Proof.ChaCha20.AArch64.Xor (wp_ldr32 wp_addImm32 wp_str32 wp_addImm wp_mov wp_ldr wp_str wp_movz)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

/-! ## Memory as the model writes it -/

theorem write64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]
theorem write32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp [Mem.writeW]
theorem read64_eq (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by simp [Mem.readW]
theorem read32_eq (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by simp [Mem.readW]

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .x0
abbrev dp : Addr := s₀.gpr .x1
abbrev L : Nat := (s₀.gpr .x2).toNat
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  wrap_st : (st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyAArch64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem APre.w_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

/-- Our caller's `x21`–`x23`, our return address, and the bytes left after
`apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  x21 : m.readW (st s₀ + BitVec.ofNat 64 576) 64 = s₀.gpr .x21
  x22 : m.readW (st s₀ + BitVec.ofNat 64 584) 64 = s₀.gpr .x22
  x23 : m.readW (st s₀ + BitVec.ofNat 64 592) 64 = s₀.gpr .x23
  x30 : m.readW (st s₀ + BitVec.ofNat 64 600) 64 = s₀.gpr .x30
  left : m.readW (st s₀ + BitVec.ofNat 64 608) 64 = BitVec.ofNat 64 (N s₀ - L s₀)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 576, 40⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 8 ≤ 616 → (savR s₀).Contains (st s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.x21],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.x22],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.x23],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.x30],
    by rw [hf.readW (c 608 (by decide) (by decide)) hd (by decide), h.left]⟩

/-! ## The check -/

/-- `(x <<< 58) >>> 58` keeps the low 6 bits. -/
theorem low6 (x : BitVec 64) : (x <<< 58) >>> 58 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The carry of `subs`, moved into a register by `adcs` of zeros. -/
theorem carry_ge (x : Nat) (b : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) + BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ x + (~~~b).toNat + true.toNat)).toNat =
      BitVec.ofNat 64 (decide (b.toNat ≤ x)).toNat := by
  have e : (2 ^ 64 ≤ x + (~~~b).toNat + true.toNat) ↔ b.toNat ≤ x := by
    rw [BitVec.toNat_not]; have := b.isLt; simp only [Bool.toNat_true]; omega
  rw [show BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 by decide]
  simp only [e]
  simp

/-- After the check. -/
structure Q0 (s₀ s : State) : Prop where
  x9 : s.gpr .x9 = BitVec.ofNat 64 (N s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (O s₀)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (decide (L s₀ ≤ N s₀)).toNat
  x12 : s.gpr .x12 = BitVec.ofNat 64 (decide (L s₀ ≤ O s₀)).toNat
  keep : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  v : s.v = s₀.v
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, State.read, State.write, State.addWithCarry, Size.bits, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, i₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have hn : s₀.mem.read (s₀.gpr .x0 + 128#64) 8 = BitVec.ofNat 64 (N s₀) := by
    rw [read64_eq]; simp [N, leftAt]
  have hO : N s₀ % 64 < 2 ^ 64 := by omega
  simp only [hn, low6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (N_lt s₀), Nat.mod_eq_of_lt hO,
    carry_ge]
  refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}),
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl, rfl, rfl⟩


/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.x19, .x20, .x24, .x25, .x26, .x27, .x28]

theorem kept_ne {r : Reg} (hr : r ∈ kept) {r' : Reg} (h : r' ∉ kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- What `apply` guarantees (`applyAArch64`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.applyAArch64.post s₀ s

/-- The low halves of v8–v15 are those on entry. -/
abbrev VKeep (s₀ s : State) : Prop :=
  ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

set_option simprocs false in
theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.movz .x .x0 0 0]) s (Final s₀) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.write,
    Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left']
  unfold Final
  refine ⟨fun r hr => ?_, ?_⟩
  · have : r ≠ .x0 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [this.1, ite_false]
    exact h.keep r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega)]
    dsimp only
    rw [h.mem]
    exact ⟨rfl, by simp (config := {decide := true}), rfl, rfl⟩


/-! ## The bytes left in the buffered block -/

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- After `start`, with `x` in `x2`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  x21 : s.gpr .x21 = st s₀
  x22 : s.gpr .x22 = dp s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (L s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 x
  x10 : s.gpr .x10 = BitVec.ofNat 64 (O s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

/-- The memory after `start`. -/
def startMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (st s₀ + BitVec.ofNat 64 576) (s₀.gpr .x21)).writeW (st s₀ + BitVec.ofNat 64 584)
    (s₀.gpr .x22)).writeW (st s₀ + BitVec.ofNat 64 592) (s₀.gpr .x23)).writeW (st s₀ + BitVec.ofNat 64 600)
    (s₀.gpr .x30)).writeW (st s₀ + BitVec.ofNat 64 608) (BitVec.ofNat 64 (N s₀ - L s₀))

theorem startMem_frame (s₀ : State) : Frame [stR s₀] s₀.mem (startMem s₀) := by
  simp only [startMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_st _ (d := 576) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_st _ (d := 584) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 592) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 600) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 608) (by decide))

theorem startMem_mid (s₀ : State) : Mid s₀ (startMem s₀) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [startMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  all_goals simp (config := {decide := true}) only [startMem, Mem.readW_writeW_self64, readW_writeW_ofNat]

set_option simprocs false in
theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.gpr .x12 = s.gpr .x12 := by
  have o576 := hp.w_st (d := 576) (n := 8) (by decide)
  have o584 := hp.w_st (d := 584) (n := 8) (by decide)
  have o592 := hp.w_st (d := 592) (n := 8) (by decide)
  have o600 := hp.w_st (d := 600) (n := 8) (by decide)
  have o608 := hp.w_st (d := 608) (n := 8) (by decide)
  rw [← h.wr] at o576 o584 o592 o600 o608
  have hx0 := h.keep .x0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx1 := h.keep .x1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2 := h.keep .x2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx21 := h.keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx22 := h.keep .x22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx23 := h.keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx30 := h.keep .x30 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsub : BitVec.ofNat 64 (N s₀) - s₀.gpr .x2 = BitVec.ofNat 64 (N s₀ - L s₀) := by
    rw [show s₀.gpr .x2 = BitVec.ofNat 64 (L s₀) by simp [L]]
    exact Proof.ChaCha20.AArch64.Xor.sub_ofNat hle
  apply WP.of_runBlock
  simp (config := {decide := true}) only [start, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.store, State.read, State.write, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    hx0, hx1, hx2, hx21, hx22, hx23, hx30, h.x9, hsub, o576, o584, o592, o600, o608, ite_true,
    ite_false, Option.some.injEq, exists_eq_left', write64_eq, BitVec.add_zero]
  rw [h.mem]
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}) [L], by simp (config := {decide := true}) [L, hx2],
    by simp (config := {decide := true}) [h.x10], fun r hr => ?_, h.rd, h.wr, startMem_mid s₀, fun k hk => ?_,
    startMem_frame s₀⟩, by simp (config := {decide := true})⟩
  · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · have e := (startMem_frame s₀).bytes (R := dR s₀) (by simpa using hp.st_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk
    simp only [startMem] at e
    dsimp only
    rw [e]
    simp


theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s)
    (hc : s.gpr .x12 = BitVec.ofNat 64 (decide (L s₀ ≤ O s₀)).toNat) :
    WP isa (.ite (.zero .x .x12) (.block [mov .x2 .x10]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by
      have e : isa.eval (.zero .x .x12) s = some (s.gpr .x12 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x12
      rw [e, hc]; by_cases hh : L s₀ ≤ O s₀ <;> simp [hh] <;> omega) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine Proof.ChaCha20.AArch64.Xor.wp_mov fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.x21], by rw [u.other _ (by decide), h.x22],
      by rw [u.other _ (by decide), h.x23],
      by rw [u.gpr, h.x10, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.x10],
      fun r hr => by rw [u.other r (kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], u.mem ▸ h.mid, u.mem ▸ h.done, u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.x21, h.x22, h.x23, ?_, h.x10, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.x2, H, headLen, bufLeft, Nat.min_eq_right hge]

/-- After `part1`: the bytes from the buffered block XORed, and `x2` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = st s₀
  x22 : s.gpr .x22 = dp s₀ + BitVec.ofNat 64 (H s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (L s₀ - H s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (64 * NB s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) : InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 6) <<< 6 = BitVec.ofNat 64 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem wp_lsl {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _))

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ (by rw [hc₁, h.x12])) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.addImm .x .x1 .x21 128, .sub .x .x1 .x1 .x10]) s₂
      fun s₃ => R1 s₀ (H s₀) s₃ ∧ s₃.gpr .x1 = st s₀ + BitVec.ofNat 64 (128 - O s₀) := by
    refine Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide) fun s' u => ?_
    refine Proof.ChaCha20.AArch64.Xor.wp_sub fun s'' u' => WP.block_nil ?_
    have g : ∀ r, r ≠ .x1 → s''.gpr r = s₂.gpr r := fun r hr => by rw [u'.other r hr, u.other r hr]
    refine ⟨⟨by rw [g _ (by decide), h₂.x21], by rw [g _ (by decide), h₂.x22], by rw [g _ (by decide), h₂.x23],
      by rw [g _ (by decide), h₂.x2], by rw [g _ (by decide), h₂.x10],
      fun r hr => by rw [g r (kept_ne hr)]; exact h₂.keep r hr,
      by rw [u'.rd, u.rd, h₂.rd], by rw [u'.wr, u.wr, h₂.wr], by rw [u'.mem, u.mem]; exact h₂.mid,
      by rw [u'.mem, u.mem]; exact h₂.done, by rw [u'.mem, u.mem]; exact h₂.frame⟩, ?_⟩
    rw [u'.gpr, u.gpr, u.other .x10 (by decide), h₂.x21, h₂.x10,
      show (128#64 : BitVec 64) = BitVec.ofNat 64 (128 - O s₀) + BitVec.ofNat 64 (O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - O s₀ + O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hx1⟩ => ?_)
  have hb : BPre s₃ (dp s₀) (st s₀ + BitVec.ofNat 64 (128 - O s₀)) (H s₀) :=
    ⟨h₃.x22, hx1, h₃.x2, by omega, fun k hk => by rw [h₃.wr]; exact dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := stR_byte hp (k := 128 - O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hx23 : s₄.gpr .x23 = BitVec.ofNat 64 (L s₀ - H s₀) := by
    rw [h₄.x23, h₃.x23, Proof.ChaCha20.AArch64.Xor.sub_ofNat hH]
  refine Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₅ u₅ => wp_lsl (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .x2 → s₆.gpr r = s₄.gpr r := fun r hr => by rw [u₆.other r hr, u₅.other r hr]
  have hm : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hnb : 64 * ((L s₀ - H s₀) / 64) = 64 * NB s₀ := by simp only [NB, blocksOf, H]
  refine ⟨by rw [g _ (by decide), h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h₃.x21],
    by rw [g _ (by decide), h₄.x22], by rw [g _ (by decide), hx23],
    by rw [u₆.gpr, u₅.gpr, hx23, round64 (by omega), hnb],
    fun r hr => by
      rw [g r (kept_ne hr), h₄.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr)
        (kept_ne hr)]
      exact h₃.keep r hr,
    by rw [u₆.rd, u₅.rd, h₄.rd, h₃.rd], by rw [u₆.wr, u₅.wr, h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, ?_⟩
  · rw [hm, h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · rw [hm]
    exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)

/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state copied to
`p + 192`. -/
def copyMem8 (m : Mem) (p : Addr) : Mem :=
  (((((((m.writeW (p + BitVec.ofNat 64 192) (m.readW p 64)).writeW (p + BitVec.ofNat 64 200)
    (m.readW (p + BitVec.ofNat 64 8) 64)).writeW (p + BitVec.ofNat 64 208) (m.readW (p + BitVec.ofNat 64 16) 64)).writeW
    (p + BitVec.ofNat 64 216) (m.readW (p + BitVec.ofNat 64 24) 64)).writeW (p + BitVec.ofNat 64 224)
    (m.readW (p + BitVec.ofNat 64 32) 64)).writeW (p + BitVec.ofNat 64 232) (m.readW (p + BitVec.ofNat 64 40) 64)).writeW
    (p + BitVec.ofNat 64 240) (m.readW (p + BitVec.ofNat 64 48) 64)).writeW (p + BitVec.ofNat 64 248)
    (m.readW (p + BitVec.ofNat 64 56) 64)

/-- And its counter advanced by `c`. -/
def copyMem (m : Mem) (p : Addr) (c : BitVec 32) : Mem :=
  (copyMem8 m p).writeW (p + BitVec.ofNat 64 48) ((m.readW (p + BitVec.ofNat 64 48) 64).setWidth 32 + c)

set_option simprocs false in
theorem args_exec {s : State} {p : Addr} (hx21 : s.gpr .x21 = p)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (p + BitVec.ofNat 64 d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = copyMem s.mem p ((s.gpr .x2 >>> 6).setWidth 32) ∧
      s'.gpr .x0 = p + BitVec.ofNat 64 192 ∧ s'.gpr .x1 = s.gpr .x22 ∧ s'.gpr .x3 = p + BitVec.ofNat 64 256 ∧
      s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x22 = s.gpr .x22 + s.gpr .x2 ∧
      s'.gpr .x23 = s.gpr .x23 - s.gpr .x2 ∧ s'.gpr .x21 = p ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (p + BitVec.ofNat 64 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o192 := hw 192 (by decide); have o200 := hw 200 (by decide); have o208 := hw 208 (by decide)
  have o216 := hw 216 (by decide); have o224 := hw 224 (by decide); have o232 := hw 232 (by decide)
  have o240 := hw 240 (by decide); have o248 := hw 248 (by decide)
  simp only [BitVec.add_zero] at i0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, State.store, State.read, State.write, Size.bits, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, hx21, i0, i8, i16, i24, i32, i40, i48, i56, o4, o192, o200, o208, o216,
    o224, o232, o240, o248, ite_true, ite_false, Option.some.injEq, exists_eq_left', write64_eq, read64_eq,
    BitVec.add_zero]
  have e : ∀ v : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := fun v => BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨by rw [write32_eq, e]; rfl, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r hr => ?_, trivial⟩
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})

/-- Reading a word after writing a 64-bit word elsewhere, at offsets from `p`. -/
theorem readW64_ofNat (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  readW_writeW_ofNat m p v h (by omega) (by omega) (by decide)

theorem copyMem8_frame (m : Mem) (p : Addr) : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (copyMem8 m p) := by
  have c : ∀ d, 192 ≤ d → d + 8 ≤ 256 →
      (⟨p + BitVec.ofNat 64 192, 64⟩ : Region).Contains (p + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  simp only [copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m m') (d : Nat), 192 ≤ d → d + 8 ≤ 256 →
      ∀ v : BitVec 64, Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (m'.writeW (p + BitVec.ofNat 64 d) v) :=
    fun hf d h₁ h₂ v => hf.writeW (List.mem_singleton_self _) v (c d h₁ h₂)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 192 (by decide) (by decide) _) 200 (by decide) (by decide) _)
    208 (by decide) (by decide) _) 216 (by decide) (by decide) _) 224 (by decide) (by decide) _) 232 (by decide)
    (by decide) _) 240 (by decide) (by decide) _) 248 (by decide) (by decide) _

theorem copyMem_frame (m : Mem) (p : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨p + BitVec.ofNat 64 192, 64⟩] m (copyMem m p c) := by
  refine ((copyMem8_frame m p).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  exact Offset.contains_base _ (by omega) (by omega)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) (p + BitVec.ofNat 64 192) = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  rw [copyMem, Offset.add_add, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  have hw : ∀ k, 24 ≤ k → k < 32 → (copyMem8 m p).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * (k - 24))) 64 := by
    intro k h₁ h₂
    simp only [copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    all_goals simp (config := {decide := true}) only [Nat.reduceMul, Nat.reduceSub, Mem.readW_writeW_self64,
      readW64_ofNat, BitVec.add_zero]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega) (by omega), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 8 - 24 = i / 8 by omega, show (192 + i) % 8 = i % 8 by omega]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [copyMem, Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.AArch64.Xor.stateAt_frame (copyMem8_frame m p) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)),
    readW64_setWidth]
  simp [stateAt]

theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = st s₀
  x22 : s.gpr .x22 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (T s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.x21, by rw [h.x22, h0, Nat.add_zero], by rw [h.x23, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

theorem Q1.w {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d, d + 8 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
  rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

/-- The registers kept are callee-saved, and not the return address. -/
theorem kept_preserved : ∀ r ∈ kept, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem blocks_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s)
    (hnb : 0 < NB s₀) : WP isa (.seq (.block blocksArgs) (.call v.callee.name v.callee.code)) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  refine WP.seq (WP.mono (args_exec h.x21 (h.w hp) (by rw [h.rd, hp.rd])) fun s₁ ⟨m₁, x0₁, x1₁, x3₁, x2₁,
    x22₁, x23₁, x21₁, k₁, rd₁, wr₁⟩ => ?_)
  rw [h.x2, shr_eq (by omega)] at m₁
  rw [h.x2] at x2₁
  rw [h.x22] at x1₁
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have dSB : (cpR s₀).Disjoint (wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dSD : (cpR s₀).Disjoint (blR s₀) := (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀)
  have dDB : (blR s₀).Disjoint (wkR s₀) := (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀)
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, hHNB⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  refine xor_call v (S := st s₀ + BitVec.ofNat 64 192) (D := dp s₀ + BitVec.ofNat 64 (H s₀))
    (B := st s₀ + BitVec.ofNat 64 256) (n := 64 * NB s₀) x0₁ x1₁ x2₁ x3₁ (by omega) dSD dSB dDB hwrap
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ k₂ x₂
  have g : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s₁.gpr r := k₂.cs
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  have fc := copyMem_frame s.mem (st s₀) (BitVec.ofNat 32 (NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have svS := savR_sub s₀
  -- Anything in the state is apart from the data.
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  refine ⟨by rw [g .x21 (by decide) (by decide), x21₁], ?_, ?_, fun r hr => ?_,
    by rw [k₂.rd, rd₁, h.rd], by rw [k₂.wr, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .x22 (by decide) (by decide), x22₁, h.x22, h.x2, Offset.add_add]
  · rw [g .x23 (by decide) (by decide), x23₁, h.x23, h.x2, Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega), hT,
      Nat.sub_sub]
  · rw [g r (kept_preserved r hr).1 (kept_preserved r hr).2, k₁ r hr]
    exact h.keep r hr
  · rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame k₂.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))),
      m₁, copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, k₂.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame k₂.frame (nd _ ?_ (sd _ svS) ?_)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) (cpR_sub s₀)))
        (show L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [k₂.frame.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (ds _ _ hpre (cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (wkR_sub s₀)))
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
      have := k₂.frame.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (ds _ _ hR (cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (wkR_sub s₀))) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, stS⟩
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨stR s₀, by simp, wkR_sub s₀⟩

theorem part2_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (part2 v.callee) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  refine WP.ite (decide (64 * NB s₀ = 0)) (by
      have e : isa.eval (.zero .x .x2) s = some (s.gpr .x2 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x2
      rw [e, h.x2, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok v hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = st s₀
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
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
  refine ⟨h.x21, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hx21 : s.gpr .x21 = p) (hw : InRegions s.wr (p + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 48) 4) :
    WP isa (.block [.ldr .w .x9 .x21 48, .addImm .w .x9 .x9 1, .str .w .x9 .x21 48, .addImm .x .x1 .x21 64,
      mov .x2 .x23]) s fun s' =>
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 48) (s.mem.readW (p + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .x1 = p + BitVec.ofNat 64 64 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ≠ .x9 → r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_ldr32 (a := p + BitVec.ofNat 64 48) (by decide) (by rw [hx21]) hr fun s₁ u₁ => ?_
  refine wp_addImm32 (by decide) fun s₂ u₂ => ?_
  refine wp_str32 (a := p + BitVec.ofNat 64 48) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21]) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ g₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have e : ∀ v : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := fun v =>
    BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₁.gpr, e, e, u₂.mem, u₁.mem, show (1#32 : BitVec 32) = 1 from rfl]
  · rw [u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx21]
  · rw [u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.other r h₃, u₄.other r h₂, g₃.gpr, u₂.other r h₁, u₁.other r h₁]
  · rw [u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr]

theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) tailXor))
      s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .x0 = st s₀ ∧
      s₁.gpr .x1 = st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine Proof.ChaCha20.AArch64.Xor.wp_mov fun s' u => Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide)
      fun s'' u' => WP.block_nil ?_
    exact ⟨by rw [u'.other _ (by decide), u.gpr, h.x21], by rw [u'.gpr, u.other _ (by decide), h.x21],
      fun r h₁ h₂ => by rw [u'.other r h₂, u.other r h₁], by rw [u'.mem, u.mem], by rw [u'.rd, u.rd],
      by rw [u'.wr, u.wr]⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨x0₁, x1₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  refine WP.seq (block_call x0₁ x1₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  have g : ∀ r ∈ [Reg.x21, .x22, .x23, .x19, .x20, .x24, .x25, .x26, .x27, .x28], s₂.gpr r = s.gpr r :=
    fun r hr => by
      have hp' : r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x0 ∧ r ≠ .x1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [k₂.cs r hp'.1 hp'.2.1, k₁ r hp'.2.2.1 hp'.2.2.2]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (ctr_exec (by rw [g .x21 (by simp), h.x21]) hw48 hr48)
    fun s₃ ⟨m₃, x1₃, x2₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hx22₃ : s₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) := by
    rw [k₃ .x22 (by decide) (by decide) (by decide), g .x22 (by simp), h.x22]
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : BPre s₃ (dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)) (st s₀ + BitVec.ofNat 64 64) (T s₀) :=
    ⟨hx22₃, x1₃, by rw [x2₃, g .x23 (by simp), h.x23], by omega,
      fun k hk => by
        rw [wr₃, k₂.wr, hwr₁, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
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
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₄.rd, rd₃, k₂.rd, rd₁, h.rd], by rw [h₄.wr, wr₃, k₂.wr, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₃ .x21 (by decide) (by decide) (by decide), g .x21 (by simp), h.x21]
  · rw [h₄.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      k₃ r (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g r (by simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (bufR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [h₄.frame.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (H s₀ + 64 * NB s₀)) (by omega)
      rw [Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  refine WP.ite (decide (T s₀ = 0)) (by
      have e : isa.eval (.zero .x .x23) s = some (s.gpr .x23 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x23
      rw [e, h.x23, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h (by simpa using h0)))
    (fun h0 => tail_ok hp h (by simpa using h0))

/-! ## The end -/

theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have w : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.rd, hp.rd, List.nil_append]; exact w d hd
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 608) ⟨by decide, by decide⟩ (by rw [h.x21]) (r 608 (by decide))
    fun s₁ u₁ => ?_
  refine wp_str (a := st s₀ + BitVec.ofNat 64 128) ⟨by decide, by decide⟩ (by rw [u₁.other _ (by decide), h.x21])
    (by rw [u₁.wr]; exact w 128 (by decide)) fun s₂ g₂ => ?_
  have rr : ∀ d, d + 8 ≤ 768 → InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact r d hd
  have x21₂ : s₂.gpr .x21 = st s₀ := by rw [g₂.gpr, u₁.other _ (by decide), h.x21]
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 600) ⟨by decide, by decide⟩ (by rw [x21₂]) (rr 600 (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 584) ⟨by decide, by decide⟩ (by rw [u₃.other _ (by decide), x21₂])
    (by rw [u₃.rd, u₃.wr]; exact rr 584 (by decide)) fun s₄ u₄ => ?_
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 592) ⟨by decide, by decide⟩
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), x21₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact rr 592 (by decide)) fun s₅ u₅ => ?_
  refine wp_ldr (a := st s₀ + BitVec.ofNat 64 576) ⟨by decide, by decide⟩
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x21₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact rr 576 (by decide)) fun s₆ u₆ => ?_
  refine wp_movz fun s₇ u₇ => WP.block_nil ?_
  -- The memory, from the bytes left stored.
  have hm₂ : s₂.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, h.saved.left]
  have hm : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have sv : ∀ d, 576 ≤ d → d + 8 ≤ 616 →
      (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))).readW
        (st s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (st s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => readW64_ofNat _ _ _ (by omega) (by omega) (by omega)
  have g : ∀ r, r ≠ .x0 → r ≠ .x9 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x30 → s₇.gpr r = s.gpr r :=
    fun r h₀ h₉ h₂₁ h₂₂ h₂₃ h₃₀ => by
      rw [u₇.other r h₀, u₆.other r h₂₁, u₅.other r h₂₃, u₄.other r h₂₂, u₃.other r h₃₀, g₂.gpr, u₁.other r h₉]
  have hfw : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))) (st s₀) =
      ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂, sv 576 (by decide) (by decide)]
      exact h.saved.x21
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, hm₂,
        sv 584 (by decide) (by decide)]
      exact h.saved.x22
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, hm₂,
        sv 592 (by decide) (by decide)]
      exact h.saved.x23
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, hm₂, sv 600 (by decide) (by decide)]
      exact h.saved.x30
  · have hd : ∀ k < L s₀, (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)))
        (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    rw [hm]
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by rw [u₇.gpr]; decide, apply_data hle fun k hk => ?_, apply_rest hle ?_ hS fun i hi => ?_⟩
    · rw [hd k hk, h.done k hk, ite_pos hk]
    · simp only [leftAt]
      rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, Mem.readW_writeW_self64,
        toNat_ofNat_lt (by omega)]
    · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq (x : Impl.ChaCha20.AArch64.XorCallee) : apply x = .seq (.block check)
    (.ite (.zero .x .x11) (.block [.movz .x .x0 0 0]) (.seq part1 (.seq (part2 x) (.seq part3 (.block finish))))) :=
  rfl

theorem apply_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa (apply v.callee) s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by
      have e : isa.eval (.zero .x .x11) s = some (s.gpr .x11 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x11
      rw [e, h.x11]; by_cases hh : L s₀ ≤ N s₀ <;> simp [hh] <;> omega)
    (fun hlt => fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok v hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.AArch64.Stream
