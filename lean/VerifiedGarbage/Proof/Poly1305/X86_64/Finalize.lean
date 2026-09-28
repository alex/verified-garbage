import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks

/-!
# Poly1305 on x86-64: `finalize`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes mac)

/-! ## Bytes in memory -/

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Byte `k` of the padded block. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (104 + k)

/-- The padded block's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

/-- The region of the padded block. -/
abbrev bufR (st : Addr) : Region := ⟨off st 104, 16⟩

theorem bufR_sub_wR (st : Addr) : Region.Sub (bufR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

theorem bufB_contains (st : Addr) {k : Nat} (hk : k < 16) : (bufR st).Contains (bufB st k) 1 := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 104) = BitVec.ofNat 64 k by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

/-- The bytes of the padded block, as read from memory. -/
theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 104) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  have hk := List.mem_range.mp hk
  rw [← h k hk]
  congr 1
  simp only [off, ofInt_natCast, bufB]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev tp : Addr := s₀.gpr .rsi
abbrev tl : Nat := (s₀.gpr .rdx).toNat
abbrev op : Addr := s₀.gpr .rcx
abbrev tR : Region := ⟨tp s₀, tl s₀⟩
abbrev oR : Region := ⟨op s₀, 16⟩
/-- The message's last bytes. -/
abbrev tail : List Byte := bytesAt s₀.mem (tp s₀) (tl s₀)
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [tR s₀]
  wr : s₀.wr = [sR (st s₀), oR s₀]
  st_t : (sR (st s₀)).Disjoint (tR s₀)
  st_o : (sR (st s₀)).Disjoint (oR s₀)
  t_o : (tR s₀).Disjoint (oR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  tl_lt : tl s₀ < 16

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86_64.pre s₀) : FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Prologue -/

/-- The state after the prologue, with the memory `m₁` it leaves. -/
structure F0 (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = s₀.gpr r
  r8 : s.gpr .r8 = R0 s₀
  r9 : s.gpr .r9 = R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4)
  hv : hval s = A0 s₀
  rbp : (s.gpr .rbp).toNat = H2 s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁

theorem fprologue_eq : save ++ setup ++ [.alu .test .rdx (.reg .rdx)] =
    save ++ (setup ++ [.alu .test .rdx (.reg .rdx)]) := by
  simp only [List.append_assoc]

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (save ++ setup ++ [.alu .test .rdx (.reg .rdx)])) s₀ fun s =>
      ∃ m₁, Mem₁ s₀ m₁ ∧ F0 s₀ m₁ s ∧ s.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [fprologue_eq]
  refine WP.block_append (WP.mono (save_ok s₀ (by rw [hp.wr]; exact List.mem_cons_self))
    fun s₁ ⟨g₁, rd₁, wr₁, _, _, f₁, sv₁⟩ => ?_)
  have hm : Mem₁ s₀ s₁.mem := ⟨f₁, sv₁⟩
  refine WP.block_append (WP.mono (setup_ok s₁ (by
    rw [wr₁, hp.wr, g₁]; exact List.mem_append_right _ List.mem_cons_self))
    fun s₃ ⟨e8, e9, e10, e11, e12, e13, k₃⟩ => ?_)
  refine WP.mono (test_ok s₃ .rdx) fun s₄ ⟨z₄, k₄⟩ => ?_
  have k := k₃.trans k₄
  rw [g₁, hm.readW_low (by omega)] at e8 e9 e11 e12 e13
  refine ⟨s₁.mem, hm, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k.1 r (by rcases hr with h | h | h | h | h <;> subst h <;> decide), g₁]
  · rw [k₄.gpr' (r := .r8), e8]
  · rw [k₄.gpr' (r := .r9), e9]
  · rw [k₄.gpr' (r := .r10), e10, e9]
  · simp only [hval, k₄.gpr' (r := .r11), k₄.gpr' (r := .rbx), k₄.gpr' (r := .rbp), e11, e12, e13]
    rw [A0, leNum_acc]
  · rw [k₄.gpr' (r := .rbp), e13]
  · rw [k.2.2.1, rd₁]
  · rw [k.2.2.2, wr₁]
  · rw [k.2.1]
  · rw [z₄, k₃.gpr' (r := .rdx), g₁]

/-! ## Copying the last bytes into the padded block -/

/-- The copy loop's invariant, before byte `j`, from the state `s₁` after the prologue. -/
structure CInv (s₀ : State) (m₁ : Mem) (s₁ : State) (j : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = BitVec.ofNat 64 j
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) fun k => if k < j then (tail s₀).getD k 0 else 0

theorem zero_setWidth : ((0 : BitVec 32).setWidth 64) = (0 : BitVec 64) := rfl

theorem bufB_zero (m : Mem) (st : Addr) {k : Nat} (hk : k < 16) :
    ((m.writeW (off st 104) (0 : BitVec 64)).writeW (off st 112) (0 : BitVec 64)) (bufB st k) = 0 := by
  rw [writeW64_zero_apply, writeW64_zero_apply]
  simp only [off, ofInt_natCast, bufB]
  by_cases h : 8 ≤ k
  · have hc : (st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 112)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 112) = BitVec.ofNat 64 (k - 8) by
        bv_omega, toNat_ofNat_lt (by omega)]
      omega
    simp only [hc, ↓reduceIte]
  · have hc : ¬ (st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 112)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 112) =
        BitVec.ofNat 64 (2 ^ 64 - 8 + k) by bv_omega, toNat_ofNat_lt (by omega)]
      omega
    have hc' : (st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 104)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (104 + k) - (st + BitVec.ofNat 64 104) = BitVec.ofNat 64 k by
        bv_omega, toNat_ofNat_lt (by omega)]
      omega
    simp only [hc, hc', ↓reduceIte]

theorem bufR_contains (st : Addr) {d : Nat} (h₁ : 104 ≤ d) (h₂ : d + 8 ≤ 120) :
    (bufR st).Contains (off st d) (64 / 8) := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 104) = BitVec.ofNat 64 (d - 104) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem FPre.in_st {s₀ : State} (hp : FPre s₀) {d n : Nat} (h : d + n ≤ 128) :
    InRegions s₀.wr (off (st s₀) d) n :=
  ⟨_, by rw [hp.wr]; exact List.mem_cons_self, contains_off h (by omega)⟩

set_option simprocs false in
theorem zero_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (at_ .rdi 104) .rax, .store (at_ .rdi 112) .rax,
      .mov32 .r12 (.imm 0)]) s₁ (CInv s₀ m₁ s₁ 0) := by
  have hrdi : s₁.gpr .rdi = st s₀ := h₁.keep .rdi (by simp)
  have o1 := hp.in_st (d := 104) (n := 8) (by omega)
  have o2 := hp.in_st (d := 112) (n := 8) (by omega)
  rw [← h₁.wr] at o1 o2
  simp only [off] at o1 o2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc32, State.store64, State.setReg, State.setReg32, hrdi, o1, o2, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r h₁ h₂ => by simp [h₁, h₂], h₁.rd, h₁.wr, ?_, fun k hk => ?_⟩
  · rw [h₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (bufR_contains _ (d := 104) (by omega)
      (by omega))).writeW (List.mem_singleton_self _) _ (bufR_contains _ (d := 112) (by omega) (by omega))
  · rw [zero_setWidth]
    exact bufB_zero _ _ hk

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .r12 }, .store8 (padAt .r12) .rax,
    .alu .add .r12 (.imm 1), .alu .cmp .r12 (.reg .rdx)]

theorem copyLoop_eq : copyLoop = .loop (.block copyBody) .ne := rfl

theorem tail_getD {s₀ : State} {j : Nat} (hj : j < tl s₀) :
    (tail s₀).getD j 0 = s₀.mem (tp s₀ + BitVec.ofNat 64 j) := by
  simp [tail, bytesAt, hj]

set_option simprocs false in
theorem copy_step {s₀ : State} (hp : FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : F0 s₀ m₁ s₁) {j : Nat} (hj : j < tl s₀) {s : State} (h : CInv s₀ m₁ s₁ j s) :
    WP isa (.block copyBody) s fun s' =>
      CInv s₀ m₁ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = tl s₀)) := by
  have htl := hp.tl_lt
  have hrdi : s.gpr .rdi = st s₀ := by rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  have hrsi : s.gpr .rsi = tp s₀ := by rw [h.keep _ (by decide) (by decide), h₁.keep .rsi (by simp)]
  have hrdx : s.gpr .rdx = BitVec.ofNat 64 (tl s₀) := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdx (by simp)]; simp
  have ea1 : tp s₀ + BitVec.ofNat 64 j * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      tp s₀ + BitVec.ofNat 64 j := by simp
  have ea2 : st s₀ + BitVec.ofNat 64 j * BitVec.ofNat 64 1 + BitVec.ofInt 64 104 = bufB (st s₀) j := by
    rw [BitVec.mul_one, show BitVec.ofInt 64 104 = BitVec.ofNat 64 104 by decide]
    bv_omega
  have hin1 : InRegions (s.rd ++ s.wr) (tp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hp.rd]
    refine ⟨tR s₀, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    simp only [Region.Contains]
    rw [show tp s₀ + BitVec.ofNat 64 j - tp s₀ = BitVec.ofNat 64 j by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  have hout : InRegions s.wr (bufB (st s₀) j) 1 := by
    rw [h.wr, hp.wr]
    refine ⟨sR (st s₀), List.mem_cons_self, ?_⟩
    simp only [Region.Contains, bufB]
    rw [show st s₀ + BitVec.ofNat 64 (104 + j) - st s₀ = BitVec.ofNat 64 (104 + j) by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBody, padAt, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg, State.setFlags,
    hrdi, hrsi, h.r12, ea1, ea2, hin1, hout, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se1]
  -- The byte copied is byte `j` of the tail.
  have hbyte : s.mem (tp s₀ + BitVec.ofNat 64 j) = (tail s₀).getD j 0 := by
    rw [tail_getD hj]
    have hf : Frame [wR (st s₀)] s₀.mem s.mem := hm.frame.trans (h.frame.sub fun r hr =>
      ⟨wR (st s₀), List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact bufR_sub_wR _⟩)
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine hp.st_t _ (sub_sR _ (by omega) _ hc) ?_
    simp only [Region.Contains]
    rw [show tp s₀ + BitVec.ofNat 64 j - tp s₀ = BitVec.ofNat 64 j by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  refine ⟨⟨?_, fun r h₁ h₂ => by simp [h₁, h₂, h.keep r h₁ h₂], h.rd, h.wr, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [ite_true]; rw [BitVec.ofNat_add]; rfl
  · exact h.frame.writeW (List.mem_singleton_self _) _ (bufB_contains _ (by omega))
  · dsimp only
    rw [writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, show k < k + 1 by omega, BitVec.setWidth_setWidth_of_le _ (by omega :
        8 ≤ 64), BitVec.setWidth_eq, hbyte]
    · have hne : bufB (st s₀) k ≠ bufB (st s₀) j := by
        intro he
        have := congrArg BitVec.toNat (show BitVec.ofNat 64 (104 + k) = BitVec.ofNat 64 (104 + j) by
          simpa [bufB] using he)
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
        omega
      simp only [hne]
      rw [h.buf k hk]
      by_cases hk' : k < j
      · simp [hk', show k < j + 1 by omega]
      · simp [hk', show ¬ k < j + 1 by omega]
  · rw [hrdx, show BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) by rw [BitVec.ofNat_add]; rfl]
    by_cases he : j + 1 = tl s₀
    · simp [he]
    · have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (tl s₀) ≠ 0 := by
        intro h0
        have : BitVec.ofNat 64 (j + 1) = BitVec.ofNat 64 (tl s₀) := by bv_omega
        have := congrArg BitVec.toNat this
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
        exact he this
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-- The padded block: the tail, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < tl s₀ then (tail s₀).getD k 0 else if k = tl s₀ then 1 else 0

/-- After the `0x01` byte, with `rsi` pointing at the padded block. -/
structure PInv (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  rsi : s.gpr .rsi = off (st s₀) 104
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rsi → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem se104 : BitVec.signExtend 64 (104 : BitVec 32) = BitVec.ofNat 64 104 := by decide

set_option simprocs false in
theorem pad1_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (h : CInv s₀ m₁ s₁ (tl s₀) s) :
    WP isa (.block [.mov32 .rax (.imm 1), .store8 (padAt .rdx) .rax, .mov .rsi (.reg .rdi),
      .alu .add .rsi (.imm 104)]) s (PInv s₀ m₁ s₁) := by
  have htl := hp.tl_lt
  have hrdi : s.gpr .rdi = st s₀ := by rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  have hrdx : s.gpr .rdx = BitVec.ofNat 64 (tl s₀) := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdx (by simp)]; simp
  have ea2 : st s₀ + BitVec.ofNat 64 (tl s₀) * BitVec.ofNat 64 1 + BitVec.ofInt 64 104 =
      bufB (st s₀) (tl s₀) := by
    rw [BitVec.mul_one, show BitVec.ofInt 64 104 = BitVec.ofNat 64 104 by decide]
    bv_omega
  have hout : InRegions s.wr (bufB (st s₀) (tl s₀)) 1 := by
    rw [h.wr, hp.wr]
    refine ⟨sR (st s₀), List.mem_cons_self, ?_⟩
    simp only [Region.Contains, bufB]
    rw [show st s₀ + BitVec.ofNat 64 (104 + tl s₀) - st s₀ = BitVec.ofNat 64 (104 + tl s₀) by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [padAt, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.ea, readSrc, readSrc32, execAlu, arithFlags, State.store8, State.setReg, State.setReg32,
    State.setFlags, hrdi, hrdx, ea2, hout, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se104]
  refine ⟨by simp [off], fun r h₁ h₂ h₃ => by simp [h₁, h₃, h.keep r h₁ h₂], h.rd,
    h.wr, h.frame.writeW (List.mem_singleton_self _) _ (bufB_contains _ (by omega)), fun k hk => ?_⟩
  dsimp only
  rw [writeW8_apply]
  by_cases hkj : k = tl s₀
  · subst hkj
    simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
    decide
  · have hne : bufB (st s₀) k ≠ bufB (st s₀) (tl s₀) := by
      intro he
      have := congrArg BitVec.toNat (show BitVec.ofNat 64 (104 + k) = BitVec.ofNat 64 (104 + tl s₀) by
        simpa [bufB] using he)
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
      omega
    simp only [hne]
    rw [h.buf k hk]
    by_cases hk' : k < tl s₀
    · simp [padded, hk']
    · simp [padded, hk', hkj]

/-- The padded block as a number: the tail with `0x01` appended. -/
theorem padded_value {s₀ : State} (hp : FPre s₀) {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    word m (off (st s₀) 104) 0 + 2 ^ 64 * word m (off (st s₀) 104) 8 + 2 ^ 128 * (0 : BitVec 32).toNat =
      leNum (tail s₀ ++ [0x01]) := by
  have htl := hp.tl_lt
  have hl : (List.range 16).map (padded s₀) =
      (tail s₀ ++ [0x01]) ++ List.replicate (15 - tl s₀) 0 := by
    apply List.ext_getElem
    · simp [tail, Poly1305.length_bytesAt]; omega
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rcases Nat.lt_trichotomy k (tl s₀) with hk | rfl | hk
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_append_left (by omega)]
        simp only [padded, hk, ite_true]
        simp [tail, bytesAt, hk]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega)]
        simp [padded, show ¬ k < tl s₀ by omega, show k ≠ tl s₀ by omega]
  simp only [word]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, ← leNum_key,
    bytesAt_buf h, hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero,
    Nat.mul_zero, Nat.add_zero]

/-- After the last bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rcx, .rsp, .r8, .r9, .r10], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  acc : H2 s₀ ≤ 4 → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧
    (s.gpr .rbp).toNat ≤ 4

theorem tail_nil {s₀ : State} (h : tl s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : F0 s₀ m₁ s₁) (hpos : 0 < tl s₀) : WP isa lastBlock s₁ (Tail s₀ m₁ s₁) := by
  have htl := hp.tl_lt
  refine WP.seq (WP.mono (zero_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := CInv s₀ m₁ s₁ (tl s₀)) ?_ fun s₃ h₃ => ?_)
  · -- The copy loop.
    rw [copyLoop_eq]
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = tl s₀ - j ∧ j < tl s₀ ∧ CInv s₀ m₁ s₁ j s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval .ne s' = some false ∧ CInv s₀ m₁ s₁ (tl s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, h⟩
      refine WP.mono (copy_step hp hm h₁ hj h) fun s' ⟨h', hz⟩ => ?_
      by_cases hl : j + 1 = tl s₀
      · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
      · exact .inr ⟨by simp [eval, hz, hl], tl s₀ - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (tl s₀) s₂ ⟨0, by simp, hpos, h₂⟩
  · -- The `0x01` byte, and the block.
    refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
    have g : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rsi → s₄.gpr r = s₁.gpr r := h₄.keep
    have hin : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
      intro d hd
      rw [h₄.rd, h₄.wr, h₄.rsi, ← off, off_off]
      exact ⟨_, List.mem_append_right _ (by rw [hp.wr]; exact List.mem_cons_self),
        contains_off (by omega) (by omega)⟩
    have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
    have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
    have hab := absorb_ok s₄ (pad := 0) (Or.inl rfl) (q := (R1 s₀).toNat / 4)
      (by rw [g .r8 (by decide) (by decide) (by decide), h₁.r8]; exact r0_lt _)
      (by rw [g .r9 (by decide) (by decide) (by decide), h₁.r9]; omega) (by omega)
      (by rw [g .r10 (by decide) (by decide) (by decide), h₁.r10]) (hin 0 (by omega)) (hin 8 (by omega))
    refine WP.mono hab fun s₅ ⟨ha, k₅⟩ => ?_
    refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr], by rw [k₅.2.1]; exact h₄.frame,
      fun hH2 => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [k₅.gpr', g _ (by decide) (by decide) (by decide)]
    · have hv4 : hval s₄ = A0 s₀ := by
        simp only [hval, g .r11 (by decide) (by decide) (by decide), g .rbx (by decide) (by decide)
          (by decide), g .rbp (by decide) (by decide) (by decide)]
        exact h₁.hv
      have hb4 : (s₄.gpr .rbp).toNat ≤ 4 := by
        rw [g .rbp (by decide) (by decide) (by decide), h₁.rbp]; exact hH2
      obtain ⟨hv, hb⟩ := ha hb4
      refine ⟨?_, hb⟩
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rw [hv, hv4, h₄.rsi, padded_value hp h₄.buf, g .r8 (by decide) (by decide) (by decide),
        g .r9 (by decide) (by decide) (by decide), h₁.r8, h₁.r9,
        Poly1305.absorbAll_block (by omega) (by omega), Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

/-- An addition with carry into a second word, as numbers, modulo `2¹²⁸`. -/
theorem add_adc_mod (a b c d : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      (a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat)) % 2 ^ 128 := by
  simp only [BitVec.toNat_add]
  rw [carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem tagWords_eq : [Instr.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore =
    [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx, .mov .rbx (.mem (at_ .rdi 56)),
    .mov .rbp (.mem (at_ .rdi 64)), .mov .r12 (.mem (at_ .rdi 72)), .mov .r13 (.mem (at_ .rdi 80)),
    .mov .r14 (.mem (at_ .rdi 88)), .mov .r15 (.mem (at_ .rdi 96))] := rfl

set_option simprocs false in
/-- Adding `s`, storing the tag and restoring the callee-saved registers. -/
theorem tagWords_ok (s : State) (hin : sR (s.gpr .rdi) ∈ s.wr) (hout : ⟨s.gpr .rcx, 16⟩ ∈ s.wr)
    (hsep : (sR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, 16⟩) :
    WP isa (.block ([.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore)) s fun s' =>
      (s'.mem.readW (off (s.gpr .rcx) 0) 64).toNat + 2 ^ 64 * (s'.mem.readW (off (s.gpr .rcx) 8) 64).toNat =
        ((s.gpr .r11).toNat + (s.mem.readW (off (s.gpr .rdi) 40) 64).toNat +
          2 ^ 64 * ((s.gpr .rbx).toNat + (s.mem.readW (off (s.gpr .rdi) 48) 64).toNat)) % 2 ^ 128 ∧
      Frame [⟨s.gpr .rcx, 16⟩] s.mem s'.mem ∧
      s'.gpr .rbx = s.mem.readW (off (s.gpr .rdi) 56) 64 ∧ s'.gpr .rbp = s.mem.readW (off (s.gpr .rdi) 64) 64 ∧
      s'.gpr .r12 = s.mem.readW (off (s.gpr .rdi) 72) 64 ∧ s'.gpr .r13 = s.mem.readW (off (s.gpr .rdi) 80) 64 ∧
      s'.gpr .r14 = s.mem.readW (off (s.gpr .rdi) 88) 64 ∧ s'.gpr .r15 = s.mem.readW (off (s.gpr .rdi) 96) 64 ∧
      s'.gpr .rsp = s.gpr .rsp := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hin, contains_off hd (by omega)⟩
  have o : ∀ d, d + 8 ≤ 16 → InRegions s.wr (off (s.gpr .rcx) d) 8 :=
    fun d hd => ⟨_, hout, contains_off hd (by omega)⟩
  have i40 := i 40 (by omega); have i48 := i 48 (by omega)
  have i0 := i 56 (by omega); have i1 := i 64 (by omega); have i2 := i 72 (by omega)
  have i3 := i 80 (by omega); have i4 := i 88 (by omega); have i5 := i 96 (by omega)
  have o0 := o 0 (by omega); have o8 := o 8 (by omega)
  -- The stores to the tag do not change the state.
  have sep : ∀ d, d + 8 ≤ 128 → ∀ e, e + 8 ≤ 16 → ∀ (m : Mem) (v : BitVec 64),
      (m.writeW (off (s.gpr .rcx) e) v).readW (off (s.gpr .rdi) d) 64 = m.readW (off (s.gpr .rdi) d) 64 :=
    fun d hd e he m v => Mem.readW_writeW_sep (hsep.sep (contains_off hd (by omega))
      (contains_off he (by omega))) (by decide)
  simp only [off] at i40 i48 i0 i1 i2 i3 i4 i5 o0 o8 sep
  apply WP.of_runBlock
  rw [tagWords_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, execAlu, arithFlags, State.setFlags, State.store64, State.load64, State.setReg, i40, i48,
    i0, i1, i2, i3, i4, i5, o0, o8, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', sep]
  have e40 : s.gpr .rdi + BitVec.ofInt 64 ↑(40 : Nat) = off (s.gpr .rdi) 40 := rfl
  have e48 : s.gpr .rdi + BitVec.ofInt 64 ↑(48 : Nat) = off (s.gpr .rdi) 48 := rfl
  rw [e40, e48]
  generalize s.gpr .r11 = a, s.mem.readW (off (s.gpr .rdi) 40) 64 = b, s.gpr .rbx = c,
    s.mem.readW (off (s.gpr .rdi) 48) 64 = d
  refine ⟨?_, ?_, trivial⟩
  · have r0 : ((s.mem.writeW (off (s.gpr .rcx) 0) (a + b)).writeW (off (s.gpr .rcx) 8)
        (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64)).readW
          (off (s.gpr .rcx) 0) 64 = a + b := by
      rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    have r8 : ((s.mem.writeW (off (s.gpr .rcx) 0) (a + b)).writeW (off (s.gpr .rcx) 8)
        (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64)).readW
          (off (s.gpr .rcx) 8) 64 = c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64 :=
      Mem.readW_writeW_self64 _ _ _
    simp only [off] at r0 r8
    rw [r0, r8]
    exact add_adc_mod a b c d
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem off_zero (p : Addr) : off p 0 = p := by simp [off]

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : F0 s₀ m₁ s₁) {s : State} (ht : Tail s₀ m₁ s₁ s) :
    WP isa (.block (reduce ++ [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [k₂.gpr' (r := .rdi), ht.keep .rdi (by simp), h₁.keep .rdi (by simp)]
  have rcx₂ : s₂.gpr .rcx = op s₀ := by
    rw [k₂.gpr' (r := .rcx), ht.keep .rcx (by simp), h₁.keep .rcx (by simp)]
  have wr₂ : s₂.wr = [sR (st s₀), oR s₀] := by rw [k₂.2.2.2, ht.wr, hp.wr]
  refine WP.mono (tagWords_ok s₂ (by rw [wr₂, rdi₂]; exact List.mem_cons_self)
    (by rw [wr₂, rcx₂]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    (by rw [rdi₂, rcx₂]; exact hp.st_o)) fun s₃ ⟨hw, hf₃, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
  rw [rdi₂, rcx₂, k₂.2.1] at hw
  rw [rcx₂, k₂.2.1] at hf₃
  rw [rdi₂, k₂.2.1] at g1 g2 g3 g4 g5 g6
  -- The state outside the padded block is as the prologue left it.
  have low : ∀ d, d + 8 ≤ 104 → s.mem.readW (off (st s₀) d) 64 = m₁.readW (off (st s₀) d) 64 := by
    intro d hd
    refine ht.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro a h₁ h₂
    simp only [Region.Contains, off, ofInt_natCast] at h₁ h₂
    bv_omega
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hm.saved
  have hf : Frame [wR (st s₀), oR s₀] s₀.mem s₃.mem :=
    (hm.frame.mono (by simp)).trans ((ht.frame.sub fun r hr => ⟨wR (st s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact bufR_sub_wR _⟩).trans (hf₃.mono (by simp)))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, low 56 (by omega), sv1]
    · rw [g2, low 64 (by omega), sv2]
    · rw [g7, k₂.gpr' (r := .rsp), ht.keep .rsp (by simp), h₁.keep .rsp (by simp)]
    · rw [g3, low 72 (by omega), sv3]
    · rw [g4, low 80 (by omega), sv4]
    · rw [g5, low 88 (by omega), sv5]
    · rw [g6, low 96 (by omega), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.ret_st.sub_right (sub_sR _ (by omega))
    · exact hp.ret_o
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hH2 := H2_le ⟨hlen, hkey, hacc⟩
    obtain ⟨hv, hb⟩ := ht.acc hH2
    have hR := hr hb
    rw [← off_24] at hkey
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := hkey
    have hA : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA]; exact Poly1305.accumulate_lt _ _
    have hV := Poly1305.absorbAll_lt (r := Rn s₀) hlt (tail s₀)
    rw [low 40 (by omega), low 48 (by omega), hm.readW_low (by omega), hm.readW_low (by omega)] at hw
    have e₀ := (s₂.gpr .r11).isLt; have e₁ := (s₂.gpr .rbx).isLt
    have hh : hval s₂ = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) := by
      rw [hR, hv, Nat.mod_eq_of_lt hV]
    unfold hval at hh
    simp only [mac]
    rw [← hkey', clamp_key, key_drop, leNum_key, off_off, off_off, Poly1305.accumulate_append hlen, hA]
    have w0 := (s₃.mem.readW (off (op s₀) 0) 64).isLt
    have w1 := (s₃.mem.readW (off (op s₀) 8) 64).isLt
    rw [off_zero] at hw w0
    rw [show off (st s₀) (40 + 0) = off (st s₀) 40 from rfl, show off (st s₀) (40 + 8) = off (st s₀) 48 from rfl]
    refine Poly1305.bytesAt_leBytes_16 _ (op s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) +
      ((s₀.mem.readW (off (st s₀) 40) 64).toNat + 2 ^ 64 * (s₀.mem.readW (off (st s₀) 48) 64).toNat)) ?_ ?_
    · omega
    · change (s₃.mem.readW (off (op s₀) 8) 64).toNat = _; omega

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ ⟨m₁, hm, h₁, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ m₁ s₁) ?_ fun s₂ h₂ => fepilogue_ok hp hm h₁ h₂)
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : tl s₀ = 0 := by simp at h; simp [tl, h]
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, by rw [h₁.mem]; exact Frame.refl _ _,
      fun hH2 => ⟨?_, by rw [h₁.rbp]; exact hH2⟩⟩
    rw [tail_nil h0, Poly1305.absorbAll_nil, h₁.hv]
  · have hpos : 0 < tl s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact lastBlock_ok hp hm h₁ hpos

/-- A state satisfying the precondition (with no tail). -/
def finalizeSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩]

theorem finalize_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.finalize Proof.Poly1305.finalizeX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := finalize_correct (FPre.of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨finalizeSat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, finalizeSat] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.X86_64
