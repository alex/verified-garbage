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
    Option.some.injEq, exists_eq_left', ite_true, ite_false, hr12, and_mask,
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

end VG.Proof.ChaCha20.X86_64.Stream
