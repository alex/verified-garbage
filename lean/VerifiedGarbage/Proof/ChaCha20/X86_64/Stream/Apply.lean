import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Calls

/-!
# Streaming ChaCha20 on x86-64: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/X86_64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, for any implementation `v` of
`vg_chacha20_xor`. The pieces are those that the proof of constant time
(`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20

open VG.X86_64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- x86-64 contract for `vg_chacha20_apply(state = rdi, data = rsi, len = rdx) -> eax`,
with 24 bytes of stack below the return address (8 for the return address
of a call, and 16 for the calls of any implementation of `vg_chacha20_xor`). -/
def applyX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 768⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint data ∧
    (s.gpr .rdi).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .rdi) = keyAt s.mem (s.gpr .rdi) ∧
      if (s.gpr .rdx).toNat ≤ leftAt s.mem (s.gpr .rdi) then
        (s'.gpr .rax).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
              ((restAt s.mem (s.gpr .rdi)).take (s.gpr .rdx).toNat) ∧
          restAt s'.mem (s.gpr .rdi) = (restAt s.mem (s.gpr .rdi)).drop (s.gpr .rdx).toNat
      else
        (s'.gpr .rax).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat ∧
          restAt s'.mem (s.gpr .rdi) = restAt s.mem (s.gpr .rdi)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ leftAt s₁.mem (s₁.gpr .rdi) = leftAt s₂.mem (s₂.gpr .rdi)

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast off_sep)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev dp : Addr := s₀.gpr .rsi
abbrev L : Nat := (s₀.gpr .rdx).toNat
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
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - 24, 24⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  wrap_st : (st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyX86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Our caller's `rbx, rbp, r12`, and the bytes left after `apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (off (st s₀) 576) 64 = s₀.gpr .rbx
  rbp : m.readW (off (st s₀) 584) 64 = s₀.gpr .rbp
  r12 : m.readW (off (st s₀) 592) 64 = s₀.gpr .r12
  left : m.readW (off (st s₀) 600) 64 = BitVec.ofNat 64 (N s₀ - L s₀)

/-! ## Regions -/

theorem APre.w_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (off (st s₀) d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., contains_off h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (off (st s₀) d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

/-! ## The check -/

/-- After the check: `rax` holds the bytes left, and the carry whether they
are fewer than `len`. -/
structure Q0 (s₀ s : State) : Prop where
  rax : s.gpr .rax = BitVec.ofNat 64 (N s₀)
  cf : s.cf = some (decide (N s₀ < L s₀))
  keep : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  simp only [off] at i₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.load64, State.setReg, State.setFlags, i₁, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hn : s₀.mem.readW (st s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) 64 = BitVec.ofNat 64 (N s₀) := by
    rw [ofInt_natCast]; simp [N, leftAt]
  have hn' : s₀.mem.readW (s₀.gpr .rdi + 128) 64 = BitVec.ofNat 64 (N s₀) := by simp [N, leftAt]
  refine ⟨hn', ?_, fun r hr => by simp [hr], rfl, rfl, rfl⟩
  simp only [hn, toNat_ofNat_lt (N_lt s₀)]
  rfl


/-! ## The bytes left in the buffered block -/

/-- `and` with `-64` rounds down to a multiple of 64. -/
theorem and_mask (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 (x.toNat / 64 * 64) := by
  have : BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 ((2 ^ 58 - 1) <<< 6) := by decide
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
  · by_cases h2 : i - 6 < 58
    · simp [hi, h2, show 6 + (i - 6) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 64 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 6 + (i - 6) = i by omega]
  · simp [hi]

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 64) : x &&& BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 64) := by
  have : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

/-- Where our caller's registers and the bytes left after `apply` are. -/
abbrev savR (s₀ : State) : Region := ⟨off (st s₀) 576, 32⟩

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 8 ≤ 608 → (savR s₀).Contains (off (st s₀) d) (64 / 8) := by
    intro d h₁ h₂
    simp only [savR, off_eq]
    exact Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.rbx],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.rbp],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.r12],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.left]⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) := by
  simp only [savR, off_eq]; exact Offset.sub_base _ (by omega)

/-- After `start`, with `x` in `rdx`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 x
  rax : s.gpr .rax = BitVec.ofNat 64 (O s₀)
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 := readW64_writeW_off m p v hd he h

/-- A byte outside a write of at most 8 bytes is unchanged. -/
theorem byte_writeW_off (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {i e : Nat} (hw : w / 8 ≤ 8)
    (hi : i < 2 ^ 32) (he : e < 2 ^ 32) (h : i + 1 ≤ e ∨ e + w / 8 ≤ i) :
    (m.writeW (off p e) v) (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  have hs := off_sep p (d := i) (n := 1) (e := e) (k := w / 8) hi he (by decide) hw h
  rw [← off_eq]
  exact Mem.write_apply (hs _ (by simp))

set_option simprocs false in
theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.cf = some (decide (O s₀ < L s₀)) := by
  have o576 := hp.w_st (d := 576) (n := 8) (by decide)
  have o584 := hp.w_st (d := 584) (n := 8) (by decide)
  have o592 := hp.w_st (d := 592) (n := 8) (by decide)
  have o600 := hp.w_st (d := 600) (n := 8) (by decide)
  rw [← h.wr] at o576 o584 o592 o600
  simp only [off] at o576 o584 o592 o600
  have hrdi := h.keep .rdi (by decide); have hrsi := h.keep .rsi (by decide)
  have hrdx := h.keep .rdx (by decide)
  have hrbx := h.keep .rbx (by decide); have hrbp := h.keep .rbp (by decide)
  have hr12 := h.keep .r12 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [start, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.store64, State.setReg, State.setFlags, hrdi, hrsi, hrdx,
    hrbx, hrbp, hr12, h.rax, o576, o584, o592, o600, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hL := L_lt s₀
  have hN := N_lt s₀
  have hsub : BitVec.ofNat 64 (N s₀) - s₀.gpr .rdx = BitVec.ofNat 64 (N s₀ - L s₀) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt hN]; exact hle),
      toNat_ofNat_lt hN, toNat_ofNat_lt (by omega)]
  have hf : Frame [stR s₀] s₀.mem ((((s₀.mem.writeW (off (st s₀) 576) (s₀.gpr .rbx)).writeW (off (st s₀) 584)
      (s₀.gpr .rbp)).writeW (off (st s₀) 592) (s₀.gpr .r12)).writeW (off (st s₀) 600)
      (BitVec.ofNat 64 (N s₀ - L s₀))) := by
    have c : ∀ d, d + 8 ≤ 768 → (stR s₀).Contains (off (st s₀) d) (64 / 8) :=
      fun d hd => contains_off hd (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 584 (by decide))).writeW (List.mem_singleton_self _) _
      (c 592 (by decide))).writeW (List.mem_singleton_self _) _ (c 600 (by decide))
  rw [hsub, h.mem]
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}) [L], by simp (config := {decide := true}) [L, hrdx], ?_,
    fun r hr => ?_, h.rd, h.wr, ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, hf⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, and_63, toNat_ofNat_lt hN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h.keep _ (by decide)
  · simp only [byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (show i < 2 ^ 32 by omega)
      (show 576 < 2 ^ 32 by decide) (by omega), byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide)
      (show i < 2 ^ 32 by omega) (show 584 < 2 ^ 32 by decide) (by omega),
      byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (show i < 2 ^ 32 by omega)
      (show 592 < 2 ^ 32 by decide) (by omega), byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide)
      (show i < 2 ^ 32 by omega) (show 600 < 2 ^ 32 by decide) (by omega)]
  · exact ⟨by simp (config := {decide := true}) only [readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [Mem.readW_writeW_self64]⟩
  · dsimp only
    rw [hf.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    simp
  · simp (config := {decide := true}) only [and_63, toNat_ofNat_lt hN,
      toNat_ofNat_lt (show N s₀ % 64 < 2 ^ 64 by omega)]


theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)

set_option simprocs false in
theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s) (hc : s.cf = some (decide (O s₀ < L s₀))) :
    WP isa (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by simp only [eval, hc]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .rdx → (s.setReg .rdx (s.gpr .rax)).gpr r = s.gpr r := fun r hr => by
      simp [State.setReg, hr]
    exact ⟨by rw [g _ (by decide), h.rbx], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.r12],
      by simp [State.setReg, h.rax, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [g _ (by decide), h.rax],
      fun r hr => by rw [g r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)]; exact h.keep r hr,
      h.rd, h.wr, h.mid, h.done, h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.rbx, h.rbp, h.r12, ?_, h.rax, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.rdx, H, headLen, bufLeft, Nat.min_eq_right hge]


/-- After `part1`: the bytes from the buffered block XORed, and `rdx` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - H s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 * NB s₀)
  zf : s.zf = some (decide (64 * NB s₀ = 0))
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) : InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

theorem ptr_eq (p : Addr) {o : Nat} (ho : o < 64) :
    p + BitVec.signExtend 64 (128 : BitVec 32) - BitVec.ofNat 64 o = p + BitVec.ofNat 64 (128 - o) := by
  rw [show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (128 - o) + BitVec.ofNat 64 o by
      rw [BitVec.ofNat_add_ofNat, show 128 - o + o = 128 by omega]; decide,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ hc₁) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 128), .alu .sub .rsi (.reg .rax)]) s₂
      fun s₃ => R1 s₀ (H s₀) s₃ ∧ s₃.gpr .rsi = st s₀ + BitVec.ofNat 64 (128 - O s₀) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h₂.rbx, h₂.rax]
    refine ⟨⟨h₂.rbx, h₂.rbp, h₂.r12, h₂.rdx, h₂.rax, fun r hr => ?_, h₂.rd, h₂.wr, h₂.mid, h₂.done,
      h₂.frame⟩, ptr_eq _ hO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h₂.keep _ (by simp)
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hrsi⟩ => ?_)
  have hb : BPre s₃ (dp s₀) (st s₀ + BitVec.ofNat 64 (128 - O s₀)) (H s₀) :=
    ⟨h₃.rbp, hrsi, h₃.rdx, by omega, fun k hk => by rw [h₃.wr]; exact dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := stR_byte hp (k := 128 - O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hr12 : s₄.gpr .r12 = BitVec.ofNat 64 (L s₀ - H s₀) := by
    rw [h₄.r12, h₃.r12, Offset.ofNat_sub_ofNat hH]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, hr12, and_mask,
    toNat_ofNat_lt (show L s₀ - H s₀ < 2 ^ 64 by omega)]
  have hnb : (L s₀ - H s₀) / 64 * 64 = 64 * NB s₀ := by simp only [NB, blocksOf, H]; omega
  rw [hnb]
  have hrbx : s₄.gpr .rbx = st s₀ := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.rbx]
  have hk4 : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₀.gpr r := fun r hr => by
    have := h₃.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [← this]; exact h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨by simp (config := {decide := true}) [hrbx],
    by simp (config := {decide := true}) [h₄.rbp], by simp (config := {decide := true}) [hr12],
    by simp (config := {decide := true}), ?_, fun r hr => ?_, by rw [h₄.rd, h₃.rd],
    by rw [h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [← Offset.ofNat_sub_ofNat_beq (x := 64 * NB s₀) (y := 0) (by omega) (by omega)]
    simp
  · have := hk4 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simpa (config := {decide := true}) using this
  · rw [h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)


/-! ## The whole blocks -/

/-- The memory after the arguments of `vg_chacha20_xor` are set up: the
state copied to `p + 192`, and its counter advanced by `c`. -/
def copyMem (m : Mem) (p : Addr) (c : BitVec 32) : Mem :=
  ((((((((m.writeW (off p 192) (m.readW (off p 0) 64)).writeW (off p 200) (m.readW (off p 8) 64)).writeW
    (off p 208) (m.readW (off p 16) 64)).writeW (off p 216) (m.readW (off p 24) 64)).writeW
    (off p 224) (m.readW (off p 32) 64)).writeW (off p 232) (m.readW (off p 40) 64)).writeW
    (off p 240) (m.readW (off p 48) 64)).writeW (off p 248) (m.readW (off p 56) 64)).writeW
    (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c)

set_option simprocs false in
theorem args_exec {s : State} {p : Addr} (hrbx : s.gpr .rbx = p)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off p d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = copyMem s.mem p ((s.gpr .rdx >>> 6).setWidth 32) ∧
      s'.gpr .rdi = p + BitVec.ofNat 64 192 ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rcx = p + BitVec.ofNat 64 256 ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .rbp = s.gpr .rbp + s.gpr .rdx ∧
      s'.gpr .r12 = s.gpr .r12 - s.gpr .rdx ∧
      (∀ r ∈ [Reg.rbx, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (off p d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (off p 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o192 := hw 192 (by decide); have o200 := hw 200 (by decide); have o208 := hw 208 (by decide)
  have o216 := hw 216 (by decide); have o224 := hw 224 (by decide); have o232 := hw 232 (by decide)
  have o240 := hw 240 (by decide); have o248 := hw 248 (by decide)
  simp only [off] at i0 i8 i16 i24 i32 i40 i48 i56 o4 o192 o200 o208 o216 o224 o232 o240 o248
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, execAlu32, execShift, arithFlags, State.store64, State.store32,
    State.load64, State.setReg, State.setReg32, State.setFlags, hrbx, i0, i8, i16, i24, i32,
    i40, i48, i56, o4, o192, o200, o208, o216, o224, o232, o240, o248, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.setWidth_setWidth_32]
  refine ⟨rfl, rfl, trivial, rfl, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrbx]


/-- The memory before the counter is advanced. -/
def copyMem8 (m : Mem) (p : Addr) : Mem :=
  (((((((m.writeW (off p 192) (m.readW (off p 0) 64)).writeW (off p 200) (m.readW (off p 8) 64)).writeW
    (off p 208) (m.readW (off p 16) 64)).writeW (off p 216) (m.readW (off p 24) 64)).writeW
    (off p 224) (m.readW (off p 32) 64)).writeW (off p 232) (m.readW (off p 40) 64)).writeW
    (off p 240) (m.readW (off p 48) 64)).writeW (off p 248) (m.readW (off p 56) 64)

theorem copyMem_eq (m : Mem) (p : Addr) (c : BitVec 32) :
    copyMem m p c = (copyMem8 m p).writeW (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c) := rfl

theorem copyMem8_frame (m : Mem) (p : Addr) : Frame [⟨off p 192, 64⟩] m (copyMem8 m p) := by
  have c : ∀ d, 192 ≤ d → d + 8 ≤ 256 → (⟨off p 192, 64⟩ : Region).Contains (off p d) (64 / 8) := by
    intro d h₁ h₂; simp only [off_eq]; exact Offset.contains _ h₁ (by omega) (by omega)
  simp only [copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨off p 192, 64⟩] m m') (d : Nat), 192 ≤ d → d + 8 ≤ 256 →
      ∀ v : BitVec 64, Frame [⟨off p 192, 64⟩] m (m'.writeW (off p d) v) :=
    fun hf d h₁ h₂ v => hf.writeW (List.mem_singleton_self _) v (c d h₁ h₂)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 192 (by decide) (by decide) _) 200 (by decide) (by decide) _)
    208 (by decide) (by decide) _) 216 (by decide) (by decide) _) 224 (by decide) (by decide) _) 232 (by decide)
    (by decide) _) 240 (by decide) (by decide) _) 248 (by decide) (by decide) _

theorem copyMem_frame (m : Mem) (p : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨off p 192, 64⟩] m (copyMem m p c) := by
  rw [copyMem_eq]
  refine ((copyMem8_frame m p).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  simp only [off_eq]; exact Offset.contains_base _ (by omega) (by omega)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) (p + BitVec.ofNat 64 192) = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  rw [copyMem_eq, Offset.add_add, byte_writeW_off _ _ _ (show 32 / 8 ≤ 8 by decide) (by omega) (by omega)
    (by omega)]
  have hw : ∀ k, 24 ≤ k → k < 32 → (copyMem8 m p).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * (k - 24))) 64 := by
    intro k h₁ h₂
    rw [word_off, word_off]
    simp only [copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_off]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega) (by omega), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 8 - 24 = i / 8 by omega, show (192 + i) % 8 = i % 8 by omega]


/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [copyMem_eq, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.X86_64.Xor.stateAt_frame (copyMem8_frame m p) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [off_eq]
      exact Offset.base_disjoint _ (by omega) (by omega)),
    readW64_setWidth]
  simp [stateAt, off_eq]


theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, toNat_ofNat_lt h, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (T s₀)
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀, stkR s₀] s₀.mem s.mem

theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.rbx, by rw [h.rbp, h0, Nat.add_zero], by rw [h.r12, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame.mono (by simp)⟩

theorem Q1.w {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d, d + 8 ≤ 768 → InRegions s.wr (off (st s₀) d) 8 := fun d hd => by rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)


theorem part2_eq (x : Impl.ChaCha20.X86_64.Callee) :
    part2 x = .ite .e (.block []) (.seq (.block blocksArgs) (.call x.name x.code)) := rfl

theorem blocks_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s)
    (hnb : 0 < NB s₀) : WP isa (.seq (.block blocksArgs) (.call v.callee.name v.callee.code)) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  refine WP.seq (WP.mono (args_exec h.rbx (h.w hp) (by rw [h.rd, hp.rd])) fun s₁ ⟨m₁, rdi₁, rsi₁, rcx₁, rdx₁,
    rbp₁, r12₁, k₁, rd₁, wr₁⟩ => ?_)
  rw [h.rdx, shr_eq (by omega)] at m₁
  rw [h.rdx] at rdx₁
  rw [h.rbp] at rsi₁
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ .rsp (by simp), h.keep .rsp (by simp)]
  have hstk : below (s₁.gpr .rsp) 24 = stkR s₀ := by rw [hsp₁]; rfl
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
    (B := st s₀ + BitVec.ofNat 64 256) (n := 64 * NB s₀) rdi₁ rsi₁ rdx₁ rcx₁ (by omega) dSD dSB dDB hwrap
    (by rw [hstk]; exact hp.stk_st.sub_right (cpR_sub s₀)) (by rw [hstk]; exact hp.stk_d.sub_right (blR_sub s₀))
    (by rw [hstk]; exact hp.stk_st.sub_right (wkR_sub s₀))
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ rd₂ wr₂ cs₂ f₂ x₂
  rw [hstk] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s₁.gpr r :=
    fun r hr => cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      R.Disjoint (stkR s₀) → ∀ r ∈ [cpR s₀, blR s₀, wkR s₀, stkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨off (st s₀) 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨off (st s₀) 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  have fc := copyMem_frame s.mem (st s₀) (BitVec.ofNat 32 (NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have cpS : Region.Sub ⟨off (st s₀) 192, 64⟩ (stR s₀) := by rw [off_eq]; exact cpR_sub s₀
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have svS := savR_sub s₀
  -- Anything in the state is apart from the data and the stack.
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have sk : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_st.symm.sub_left hR
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have dk : ∀ R, Region.Sub R (dR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_d.symm.sub_left hR
  refine ⟨by rw [g .rbx (by simp), k₁ .rbx (by simp), h.rbx], ?_, ?_, fun r hr => ?_, by rw [rd₂, rd₁, h.rd],
    by rw [wr₂, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .rbp (by simp), rbp₁, h.rbp, h.rdx, Offset.add_add]
  · rw [g .r12 (by simp), r12₁, h.r12, h.rdx, Offset.ofNat_sub_ofNat (by omega), hT, Nat.sub_sub]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g r (by rcases hr with rfl | rfl | rfl | rfl <;> simp), k₁ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
  · rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega)) (sk _ stS)),
      m₁, copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, f₂.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sk _ bufS)) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (by rw [off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame f₂ (nd _ ?_ (sd _ svS) ?_ (sk _ svS))
    · simp only [savR, off_eq]; exact Offset.disjoint_base _ (by omega) (by omega)
    · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
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


theorem part2_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (part2 v.callee) s (Q2 s₀) := by
  rw [part2_eq]
  refine WP.ite (decide (64 * NB s₀ = 0)) (by simp [eval, h.zf])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok v hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
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
  refine ⟨h.rbx, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩


/-- The buffered block. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) :=
  below_sub (by decide) (by decide)

set_option simprocs false in
/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hrbx : s.gpr .rbx = p) (hw : InRegions s.wr (off p 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (off p 48) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1),
      .store32 (at_ .rbx 48) .rax, .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64),
      .mov .rdx (.reg .r12)]) s fun s' =>
      s'.mem = s.mem.writeW (off p 48) (s.mem.readW (off p 48) 32 + 1) ∧
      s'.gpr .rsi = p + BitVec.ofNat 64 64 ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [off] at hw hr
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    readSrc32, execAlu, execAlu32, arithFlags, State.load32, State.store32, State.setReg, State.setReg32,
    State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true,
    ite_false, hrbx, hw, hr, RegUpd.setWidth_setWidth_32]
  exact ⟨trivial, rfl, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

set_option simprocs false in
theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) tailXor))
      s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .rdi = st s₀ ∧
      s₁.gpr .rsi = st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [tailArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx]
    exact ⟨trivial, rfl, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨rdi₁, rsi₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ _ (by decide) (by decide), h.keep .rsp (by simp)]
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have hb8 : below (s₁.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [hsp₁]
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  refine WP.seq (block_call rdi₁ rsi₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by rw [hb8]; exact (hp.stk_st.sub_left (below8_stk s₀)).sub_right (bufR_sub s₀))
    (by rw [hb8]; exact (hp.stk_st.sub_left (below8_stk s₀)).sub_right stS)
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
      exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ blk₂ => ?_)
  rw [hb8] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s.gpr r := fun r hr => by
    rw [cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hw48 : InRegions s₂.wr (off (st s₀) 48) 4 := by
    rw [wr₂, hwr₁]; exact ⟨stR s₀, by simp, contains_off (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (off (st s₀) 48) 4 := by
    rw [rd₂, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (ctr_exec (by rw [g .rbx (by simp), h.rbx]) hw48 hr48)
    fun s₃ ⟨m₃, rsi₃, rdx₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hrbp₃ : s₃.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) := by
    rw [k₃ .rbp (by decide) (by decide) (by decide), g .rbp (by simp), h.rbp]
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : BPre s₃ (dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)) (st s₀ + BitVec.ofNat 64 64) (T s₀) :=
    ⟨hrbp₃, rsi₃, by rw [rdx₃, g .r12 (by simp), h.r12], by omega,
      fun k hk => by
        rw [wr₃, wr₂, hwr₁, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, rd₂, wr₂, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have b8S := below8_stk s₀
  have f₃ : Frame [⟨off (st s₀) 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) := Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨off (st s₀) 48, 4⟩ (stR s₀) := by rw [off_eq]; exact Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.stk_st.sub_left b8S).symm.sub_left stS),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_off _ _ _ (show 32 / 8 ≤ 8 by decide) (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₄.rd, rd₃, rd₂, rd₁, h.rd], by rw [h₄.wr, wr₃, wr₂, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k₃ .rbx (by decide) (by decide) (by decide), g .rbx (by simp), h.rbx]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h₄.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      k₃ r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide), g r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
  · have e12 : s₂.mem.readW (off (st s₀) 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt, off_eq]
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (hp.stk_st.sub_left b8S).symm.sub_left svS
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨off (st s₀) 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dS _ _ (fun _ h => h) (bufR_sub s₀)
          · exact (hp.stk_d.sub_left b8S).symm) (show L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
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
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, bufR_sub s₀⟩
      · exact ⟨stkR s₀, by simp, b8S⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

end VG.Proof.ChaCha20.X86_64.Stream
