import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Common

/-!
# ChaCha20-Poly1305 on x86-64: absorbing padded data

Untrusted: everything here is checked by Lean. `macPad p n` absorbs the `n`
bytes at `p` into the Poly1305 state, and zeros to a multiple of 16:
`msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .rbx ∨ p = .r14) ∧ (n = .rbp ∨ n = .r13)

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  stk : (stkR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len w : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x w) : (⟨P, len⟩ : Region).Contains x w := by
  simp only [Region.Contains] at *
  have : (x - P).toNat ≤ (x - (P + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - P = (x - (P + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem Src.cov_sub {s₀ : State} {P : Addr} {len : Nat} (hs : Src s₀ P len) {a n : Nat} (h : a + n ≤ len)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers [⟨P + BitVec.ofNat 64 a, n⟩] (s.rd ++ s.wr) := by
  intro x w ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [hrd, hwr]
  exact hs.cov x w ⟨_, List.mem_singleton_self _, contains_off_sub h hc⟩

theorem Src.disj_sub {P : Addr} {len : Nat} {R : Region} (hd : R.Disjoint ⟨P, len⟩) {a n : Nat}
    (h : a + n ≤ len) : R.Disjoint ⟨P + BitVec.ofNat 64 a, n⟩ :=
  fun x h₁ h₂ => hd x h₁ (contains_off_sub h h₂)

set_option simprocs false in
theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4] : List Instr))) s
      fun s' => s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = s.gpr p ∧
        s'.gpr .rdx = s.gpr n >>> 4 ∧ (∀ q, q ≠ .rdi → q ≠ .rsi → q ≠ .rdx → s'.gpr q = s.gpr q) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hp₁ : s₁.gpr p = s.gpr p := g₁ p (by rcases hp with rfl | rfl <;> decide)
  have hn₁ : s₁.gpr n = s.gpr n := g₁ n (by rcases hn with rfl | rfl <;> decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, State.setReg, State.setFlags, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false]
  have hpd : p ≠ .rdx := by rcases hp with rfl | rfl <;> decide
  have hnd : n ≠ .rsi := by rcases hn with rfl | rfl <;> decide
  refine ⟨by simp [e1], by simp [hp₁], by simp [hnd, hn₁], fun q h₁ h₂ h₃ => by simp [h₂, h₃, g₁ q h₁],
    rd₁, wr₁, m₁⟩

set_option simprocs false in
theorem macC_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block (anchor .rdi 448 ++ ([.mov .rdx (.reg n), .alu .and .rdx (.imm 15)] : List Instr))) s
      fun s' => s'.gpr .r15 = s.gpr .rdi - BitVec.ofNat 64 448 ∧ s'.gpr .rdx = s.gpr n &&& 15 ∧
        s'.zf = some (s.gpr n &&& 15 == 0) ∧
        (∀ q, q ≠ .r15 → q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  refine WP.block_append (WP.mono (anchor_ok .rdi (k := 448) (by omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hn₁ : s₁.gpr n = s.gpr n := g₁ n (by rcases hn with rfl | rfl <;> decide)
  have se15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, se15]
  have hnd : n ≠ .rdx := by rcases hn with rfl | rfl <;> decide
  refine ⟨by simp [e1], by simp [hn₁], by simp [hn₁], fun q h₁ h₂ => by simp [h₂, g₁ q h₁],
    rd₁, wr₁, m₁⟩

set_option simprocs false in
theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.mov .rsi (.reg n), .alu .sub .rsi (.reg .rdx), .alu .add .rsi (.reg p)]) s
      fun s' => s'.gpr .rsi = s.gpr n - s.gpr .rdx + s.gpr p ∧
        (∀ q, q ≠ .rsi → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  have hps : p ≠ .rsi := by rcases hp with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, hps]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem se0' : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

set_option simprocs false in
/-- Zeroing the padded block. -/
theorem padZ_ok {s₀ : State} (hp : APre s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)]) s fun s' =>
      s'.gpr .rcx = 0 ∧ (∀ q, q ≠ .rax → q ≠ .rcx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (576 + j)) = 0 := by
  have o0 := hp.in_ctx (a := 576) (w := 8) (by omega)
  have o1 := hp.in_ctx (a := 584) (w := 8) (by omega)
  rw [← hwr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc32, State.store64, State.setReg, State.setReg32, hr15, o0, o1, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q h₁ h₂ => by simp [h₁, h₂], trivial, trivial, ?_, fun j hj => ?_⟩
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · have z : (BitVec.setWidth 64 (0 : BitVec 32)) = 0 := rfl
    simp only [z]
    rw [VG.Proof.Poly1305.writeW64_zero_apply, VG.Proof.Poly1305.writeW64_zero_apply]
    have e : ∀ d, d ≤ 576 + j → (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 (d : Int))).toNat = 576 + j - d := by
      intro d hd
      rw [show cx s₀ + BitVec.ofInt 64 (d : Int) = off (cx s₀) d from rfl, off_eq, off_eq,
        show cx s₀ + BitVec.ofNat 64 (576 + j) - (cx s₀ + BitVec.ofNat 64 d) = BitVec.ofNat 64 (576 + j - d) by
          rw [show 576 + j = d + (576 + j - d) by omega, BitVec.ofNat_add]; bv_omega,
        toNat_ofNat_lt (by omega)]
    by_cases h : 8 ≤ j
    · rw [e 584 (by omega)]
      simp only [show 576 + j - 584 < 8 by omega, ite_true]
    · have w : ¬ (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int))).toNat < 8 := by
        rw [show cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int) = off (cx s₀) 584 from rfl, off_eq, off_eq,
          show cx s₀ + BitVec.ofNat 64 (576 + j) - (cx s₀ + BitVec.ofNat 64 584) =
            BitVec.ofNat 64 (2 ^ 64 - 8 + j) by bv_omega, toNat_ofNat_lt (by omega)]
        omega
      simp only [w, ite_false, e 576 (by omega), show 576 + j - 576 < 8 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (i : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (576 + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

theorem se1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

set_option simprocs false in
theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hrsi : s₂.gpr .rsi = Q) (hrdx : s₂.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s₂.gpr .r15 = cx s₀)
    (hwr : s₂.wr = s₀.wr) (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q i s) :
    WP isa (.block copyBody) s fun s' =>
      CpInv s₀ s₂ Q (i + 1) s' ∧ s'.zf = some (decide (i + 1 = t)) := by
  have hrsi' : s.gpr .rsi = Q := by rw [h.keep _ (by decide) (by decide), hrsi]
  have hrdx' : s.gpr .rdx = BitVec.ofNat 64 t := by rw [h.keep _ (by decide) (by decide), hrdx]
  have hr15' : s.gpr .r15 = cx s₀ := by rw [h.keep _ (by decide) (by decide), hr15]
  have ea1 : Q + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Q + BitVec.ofNat 64 i := by simp
  have ea2 : cx s₀ + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 576 = off (cx s₀) (576 + i) := by
    rw [BitVec.mul_one, off_eq, show BitVec.ofInt 64 576 = BitVec.ofNat 64 576 by decide, BitVec.ofNat_add]
    bv_omega
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (576 + i)) 1 := by rw [h.wr, hwr]; exact hp.in_ctx (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBody, tailByte, padByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hrsi', hr15', h.rcx, ea1, ea2, hin, hout, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  -- The byte copied is byte `i` of the tail, unchanged since `s₂`.
  have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hc => hdisj i hi r hr _ (by
      simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine ⟨⟨?_, fun r h₁ h₂ => by simp [h₁, h₂, h.keep r h₁ h₂], h.rd, h.wr, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [ite_true]; rw [BitVec.ofNat_add]; rfl
  · exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · dsimp only
    rw [VG.Proof.ChaCha20.X86_64.Xor.writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, BitVec.setWidth_setWidth_of_le _ (by omega :
        8 ≤ 64), BitVec.setWidth_eq, hbyte]
    · have hne : off (cx s₀) (576 + k) ≠ off (cx s₀) (576 + i) := by
        intro he
        rw [off_eq, off_eq] at he
        have := congrArg BitVec.toNat (show BitVec.ofNat 64 (576 + k) = BitVec.ofNat 64 (576 + i) by
          simpa using he)
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
        omega
      simp only [hne, ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [hrdx', show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by rw [BitVec.ofNat_add]; rfl]
    by_cases he : i + 1 = t
    · simp [he]
    · have : BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 t ≠ 0 := by
        intro h0
        have : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 t := by bv_omega
        have := congrArg BitVec.toNat this
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
        exact he this
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

theorem copyLoop_eq : (Code.loop (.block [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]) .ne : Prog isa) = .loop (.block copyBody) .ne := rfl

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) 576 + BitVec.ofNat 64 k = off (cx s₀) (576 + k) by
      rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padE_eq : ptr .rdi .r15 448 ++ ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr) =
    ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr)) := by simp only [List.append_assoc]

set_option simprocs false in
theorem mov32_rdx_ok (v : BitVec 32) (s : State) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' =>
      s'.gpr .rdx = v.setWidth 64 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem padTail_eq : padTail =
    .seq (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block (ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr))))
    (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks) (.block (anchor .rdi 448))))) := by
  rw [padTail, padE_eq]; rfl

/-- The frame of the Poly1305 state and the padded block, and the calls. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144, stkR s₀]

theorem sub_mac (s₀ : State) {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) : Region.Sub (sub s₀ k n) (sub s₀ 448 144) := by
  intro x hx
  simp only [off_eq, Region.Contains] at *
  bv_omega

theorem frame_mac {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩

theorem frame_mac' {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n, below (s₀.gpr .rsp) 8] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩
    · exact ⟨stkR s₀, by simp, below8_stk s₀⟩

theorem padTail_ok {s₀ : State} (hp : APre s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hrsi : s.gpr .rsi = Q) (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s.gpr .r15 = cx s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 576 16)) :
    WP isa padTail s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono (padZ_ok hp hr15 hwr) fun s₂ ⟨rcx₂, g₂, rd₂, wr₂, f₂, z₂⟩ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t) ?_ fun s₃ h₃ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval .ne s' = some false ∧ CpInv s₀ s₂ Q t s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [g₂ _ (by decide) (by decide), hrsi])
        (by rw [g₂ _ (by decide) (by decide), hrdx]) (by rw [g₂ _ (by decide) (by decide), hr15])
        (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI) fun s' ⟨h', hz⟩ => ?_
      by_cases hl : i + 1 = t
      · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
      · exact .inr ⟨by simp [eval, hz, hl], t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [rcx₂]; rfl, fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [h₃.keep r h₁ h₂, g₂ r h₁ h₂]
  refine WP.seq (WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by omega) s₃)
    fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ => ?_))
  refine WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := 576) (by omega) s₄)
    fun s₅ ⟨e5, g₅, rd₅, wr₅, m₅⟩ => ?_)
  refine WP.mono (mov32_rdx_ok 1 s₅) fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ => ?_
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃ _ (by decide) (by decide), hr15]
  have rdi₆ : s₆.gpr .rdi = off (cx s₀) 448 := by rw [g₆ _ (by decide), g₅ _ (by decide), e4, r15₃]
  have rsi₆ : s₆.gpr .rsi = off (cx s₀) 576 := by rw [g₆ _ (by decide), e5, g₄ _ (by decide), r15₃]
  have rdx₆ : s₆.gpr .rdx = BitVec.ofNat 64 1 := by rw [e6]; rfl
  have g₆' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s₆.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₆ r h₅, g₅ r h₄, g₄ r h₃, g₃ r h₁ h₂]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, h₃.rd, rd₂, hrd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, h₃.wr, wr₂, hwr]
  have mm₆ : s₆.mem = s₃.mem := by rw [m₆, m₅, m₄]
  refine WP.seq (blocks_call (n := 1) rdi₆ rsi₆ rdx₆ (by omega)
    (sub_disj s₀ (b := 576) (m := 16 * 1) (by omega) (by omega) (by omega))
    (by rw [hp.off_toNat (by omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₆]; exact hp.below8_sub (by omega)) (by rw [rsp₆]; exact hp.below8_sub (by omega))
    (covers_left _ (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨576, rfl, show 576 + 16 * 1 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    fun s₇ rd₇ wr₇ cs₇ f₇ rdi₇ repr₇ => ?_)
  rw [rsp₆] at f₇
  refine WP.mono (anchor_ok .rdi (k := 448) (by omega) s₇) fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ => ?_
  have hframe : Frame (macR s₀) s.mem s₆.mem := by
    rw [mm₆]
    exact (frame_mac (by omega) (by omega) f₂).trans (frame_mac (by omega) (by omega) h₃.frame)
  refine ⟨fun r hr => ?_, by rw [rd₈, rd₇, rd₆', hrd], by rw [wr₈, wr₇, wr₆', hwr], ?_, fun key msg hr => ?_⟩
  · by_cases h15 : r = .r15
    · subst h15; rw [e8, rdi₇, off_sub, hr15]
    · have h' : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      rw [g₈ r h15, cs₇ r hr, g₆' r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2]
  · rw [m₈]; exact hframe.trans (frame_mac' (by omega) (by omega) f₇)
  · rw [m₈]
    have f26 : Frame [sub s₀ 576 16] s.mem s₆.mem := by rw [mm₆]; exact f₂.trans h₃.frame
    have hr₆ : Repr s₆.mem (off (cx s₀) 448) key msg := Repr.frame f26 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by omega) (by omega) (by omega)) hr
    have hb : bytesAt s₆.mem (off (cx s₀) (576 : Nat)) (16 * 1) = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
        rw [mm₆, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
        congr 1
        simp only [bytesAt]
        apply List.map_congr_left
        intro j hj
        exact src₂ j (List.mem_range.mp hj)
    have := repr₇ key msg hr₆
    rwa [hb] at this

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem and15_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len &&& 15 = BitVec.ofNat 64 (len % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt h, toNat_ofNat_lt (by omega),
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad p n) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpc : p ∈ calleeSaved := by rcases hr.1 with rfl | rfl <;> simp [calleeSaved]
  have hnc : n ∈ calleeSaved := by rcases hr.2 with rfl | rfl <;> simp [calleeSaved]
  have hp15 : p ≠ .r15 := by rcases hr.1 with rfl | rfl <;> decide
  have hn15 : n ≠ .r15 := by rcases hr.2 with rfl | rfl <;> decide
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono (macA_ok hr s) fun s₁ ⟨rdi₁, rsi₁, rdx₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have g₁' : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r h =>
    g₁ r (calleeSaved_ne h).2.2.2.2 (calleeSaved_ne h).2.2.2.1 (calleeSaved_ne h).2.2.1
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁' _ (by simp [calleeSaved]), hrsp]
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  refine WP.seq (blocks_call (P := off (cx s₀) 448) (p := P) (n := len / 16)
    (by rw [rdi₁, hr15]) (by rw [rsi₁, hP]) (by rw [rdx₁, hn, shr4_ofNat hlt]) (by omega)
    ((hcP.sub_left (sub_ctx s₀ (by omega))).sub_right (Region.sub_prefix hk))
    (by have := hs.wrap; omega)
    (by rw [rsp₁]; exact hp.below8_sub (by omega))
    (by rw [rsp₁]; exact (hs.stk.sub_left (below8_stk s₀)).sub_right (Region.sub_prefix hk))
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [rd₁, wr₁, hrd, hwr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · refine covers_left _ (covers_sub hp (by rw [wr₁, hwr]) [sub s₀ 448 128] (fun r hr => ?_)) a w
          ⟨_, List.mem_singleton_self _, hc⟩
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)
    (covers_sub hp (by rw [wr₁, hwr]) _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    fun s₂ rd₂ wr₂ cs₂ f₂ rdi₂ repr₂ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.seq (WP.mono (macC_ok hr s₂) fun s₃ ⟨r15₃, rdx₃, zf₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 64 len := by rw [cs₂ n hnc, g₁' n hnc, hn]
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r h => by
    by_cases h15 : r = .r15
    · subst h15; rw [r15₃, rdi₂, off_sub, hr15]
    · rw [g₃ r h15 (calleeSaved_ne h).2.2.1, cs₂ r h, g₁' r h]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have hdisjP : ∀ r ∈ [sub s₀ 448 128, below (s₀.gpr .rsp) 8], (⟨P, len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hcP.sub_left (sub_ctx s₀ (by omega))).symm
    · exact (hs.stk.sub_left (below8_stk s₀)).symm
  have fr₃ : Frame (macR s₀) s.mem s₃.mem := by rw [m₃]; exact frame_mac' (by omega) (by omega) f₂
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  refine WP.ite (decide (len % 16 = 0)) (by
      simp only [eval, zf₃, n₂, and15_ofNat hlt]
      by_cases h0 : len % 16 = 0
      · simp [h0]
      · have : BitVec.ofNat 64 (len % 16) ≠ 0 := by
          intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat_lt (by omega)] at this; exact h0 this
        simp [h0]; exact this) (fun h => ?_) (fun h => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨cs₃, rd₃', wr₃', fr₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using h
    refine WP.seq (WP.mono (macD_ok hr s₃) fun s₄ ⟨rsi₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
    have g₄' : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r h => by
      rw [g₄ r (calleeSaved_ne h).2.2.2.1, cs₃ r h]
    have hQ : s₄.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [rsi₄, g₃ n hn15 (by rcases hr.2 with rfl | rfl <;> decide), n₂, rdx₃, n₂, and15_ofNat hlt,
        g₃ p hp15 (by rcases hr.1 with rfl | rfl <;> decide), cs₂ p hpc, g₁' p hpc, hP]
      have e : len = 16 * (len / 16) + len % 16 := (Nat.div_add_mod _ _).symm
      have e' : BitVec.ofNat 64 len = BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 (len % 16) := by
        conv => lhs; rw [e]
        rw [BitVec.ofNat_add]
      rw [e']; bv_omega
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov_sub (a := 16 * (len / 16) + j) (n := 1) (by omega) (by rw [rd₄, rd₃', hrd])
        (by rw [wr₄, wr₃', hwr]) _ _ ⟨_, List.mem_singleton_self _, self_contains _⟩
    have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ 576 16) := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by omega))) (a := 16 * (len / 16) + j) (n := 1)
        (by omega)).symm
    refine WP.mono (padTail_ok hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by omega) (by omega) hQ
      (by rw [g₄ _ (by decide), rdx₃, n₂, and15_ofNat hlt])
      (by rw [g₄ _ (by decide), r15₃, rdi₂, off_sub])
      (by rw [g₄' _ (by simp [calleeSaved]), hrsp]) (by rw [rd₄, rd₃', hrd]) (by rw [wr₄, wr₃', hwr])
      hsrc hdj) fun s₅ ⟨cs₅, rd₅, wr₅, f₅, repr₅⟩ => ?_
    refine ⟨fun r h => by rw [cs₅ r h, g₄' r h], by rw [rd₅, rd₄, rd₃'], by rw [wr₅, wr₄, wr₃'],
      fr₃.trans (by rw [← m₄]; exact f₅), fun key msg hr => ?_⟩
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, bytesAt_frame f₂ (fun r hr => (hdisjP r hr).sub_left
      (sub_off P (a := 16 * (len / 16)) (by omega))) (by omega)] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.X86_64
