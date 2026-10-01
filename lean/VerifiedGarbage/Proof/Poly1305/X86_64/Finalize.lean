import VerifiedGarbage.Proof.Poly1305.X86_64.Buffer
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on x86-64: `finalize`

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

open VG.Proof.Poly1305.Limbs64

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

/-- The bytes of the buffer, as read from memory. -/
theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 56) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  rw [← h k (List.mem_range.mp hk), bufB_eq]

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The number of bytes buffered. -/
abbrev kf : Nat := (s₀.gpr .rsi).toNat % 16
abbrev op : Addr := s₀.gpr .rdx
abbrev oR : Region := ⟨op s₀, 16⟩
/-- The bytes buffered. -/
abbrev tail : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kf s₀)
end

structure FPre (s₀ : State) : Prop where
  st_in : sR (st s₀) ∈ s₀.wr
  o_in : oR s₀ ∈ s₀.wr
  st_o : (sR (st s₀)).Disjoint (oR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86_64.pre s₀) : FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem kf_lt (s₀ : State) : kf s₀ < 16 := Nat.mod_lt _ (by decide)

/-! ## Prologue -/

/-- The state after the prologue, with the memory `m₁` it leaves. -/
structure F0 (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rsp], s.gpr r = s₀.gpr r
  rcx : s.gpr .rcx = op s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (kf s₀)
  r8 : s.gpr .r8 = R0 s₀
  r9 : s.gpr .r9 = R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4)
  hv : hval s = A0 s₀
  rbp : (s.gpr .rbp).toNat = H2 s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁

set_option simprocs false in
theorem args_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)]) s fun s' =>
      s'.gpr .rcx = s.gpr .rdx ∧ s'.gpr .rdx = BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', and15]
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem fprologue_eq : [Instr.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] ++
    save ++ setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr) =
    [Instr.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] ++
    (save ++ (setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) := by
  simp only [List.append_assoc]

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] : List Instr) ++ save ++
      setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s =>
      ∃ m₁, Mem₁ s₀ m₁ ∧ F0 s₀ m₁ s ∧
        s.zf = some (BitVec.ofNat 64 (kf s₀) &&& BitVec.ofNat 64 (kf s₀) == 0) := by
  rw [fprologue_eq]
  refine WP.block_append (WP.mono (args_ok s₀) fun s₁ ⟨c₁, d₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := k₁.gpr'
  have hw₁ : sR (s₁.gpr .rdi) ∈ s₁.wr := by rw [k₁.2.2.2, rdi₁]; exact hp.st_in
  refine WP.block_append (WP.mono (save_ok s₁ hw₁) fun s₂ ⟨g₂, rd₂, wr₂, _, _, f₂, sv₂⟩ => ?_)
  refine WP.block_append (WP.mono (setup_ok s₂ (by
    rw [wr₂, g₂]; exact List.mem_append_right _ hw₁))
    fun s₃ ⟨e8, e9, e10, e11, e12, e13, k₃⟩ => ?_)
  refine WP.mono (test_ok s₃ .rdx) fun s₄ ⟨z₄, k₄⟩ => ?_
  -- The callee-saved registers are those on entry: `args` does not write them.
  have sv : Saved (st s₀) s₀ s₂.mem := by
    rw [← rdi₁]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sv₂
    exact ⟨a1.trans k₁.gpr', a2.trans k₁.gpr', a3.trans k₁.gpr', a4.trans k₁.gpr', a5.trans k₁.gpr',
      a6.trans k₁.gpr'⟩
  have hm : Mem₁ s₀ s₂.mem := ⟨by rw [← rdi₁, ← k₁.2.1]; exact f₂, sv⟩
  have k := k₃.trans k₄
  rw [g₂, rdi₁, hm.readW_low (by decide)] at e8 e9 e11 e12 e13
  refine ⟨s₂.mem, hm, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [k.gpr', g₂, k₁.gpr']
  · rw [k.gpr' (r := .rcx), g₂, c₁]
  · rw [k.gpr' (r := .rdx), g₂, d₁]
  · rw [k₄.gpr' (r := .r8), e8]
  · rw [k₄.gpr' (r := .r9), e9]
  · rw [k₄.gpr' (r := .r10), e10, e9]
  · simp only [hval, k₄.gpr' (r := .r11), k₄.gpr' (r := .rbx), k₄.gpr' (r := .rbp), e11, e12, e13]
    rw [A0, leNum_acc]
  · rw [k₄.gpr' (r := .rbp), e13]
  · rw [k.2.2.1, rd₂, k₁.2.2.1]
  · rw [k.2.2.2, wr₂, k₁.2.2.2]
  · rw [k.2.1]
  · rw [z₄, k₃.gpr' (r := .rdx), g₂, d₁]

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kf s₀ then (tail s₀).getD k 0 else if k = kf s₀ then 1 else 0

/-- The buffered bytes in the memory the prologue leaves. -/
theorem Mem₁.tail {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) {k : Nat} (hk : k < kf s₀) :
    m₁ (bufB (st s₀) k) = (tail s₀).getD k 0 := by
  have hkl := kf_lt s₀
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [← bufB_eq]
  refine hm.frame _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [svR, off, ofInt_natCast] at hc
  exact Offset.disjoint (st s₀) (d := 56 + k) (n := 1) (by omega_using [hk, hkl]) (by omega_using [hk, hkl]) (by decide) _
    (Region.contains_self _ _) hc

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZInv (s₀ : State) (m₁ : Mem) (s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kf s₀ ≤ j ∧ j ≤ 16
  r12 : s.gpr .r12 = BitVec.ofNat 64 j
  rax : s.gpr .rax = 0
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) fun k =>
    if k < kf s₀ then (tail s₀).getD k 0 else if k < j then 0 else m₁ (bufB (st s₀) k)

theorem zinit_ok {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State} (h₁ : F0 s₀ m₁ s₁) :
    WP isa (.block [.mov32 .rax (.imm 0), .mov .r12 (.reg .rdx)]) s₁ (ZInv s₀ m₁ s₁ (kf s₀)) := by
  refine wp_mov32i fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨⟨(Nat.le_refl _), Nat.le_of_lt (kf_lt s₀)⟩, by rw [u₃.gpr, u₂.other _ (by decide), h₁.rdx], by
    rw [u₃.other _ (by decide), u₂.gpr]; rfl, fun r h1 h2 => by rw [u₃.other r h2, u₂.other r h1],
    by rw [u₃.rd, u₂.rd, h₁.rd], by rw [u₃.wr, u₂.wr, h₁.wr],
    by rw [u₃.mem, u₂.mem, h₁.mem]; exact Frame.refl _ _, fun k hk => ?_⟩
  rw [u₃.mem, u₂.mem, h₁.mem]
  by_cases hkf : k < kf s₀
  · simp only [hkf, ite_true]; exact hm.tail hkf
  · simp only [hkf, ite_false]

theorem FPre.buf_in {s₀ : State} (hp : FPre s₀) {s : State} (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB (st s₀) k) 1 := by
  rw [hwr]
  exact ⟨_, hp.st_in, by rw [bufB, ← ofInt_natCast]; exact contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem zero_step {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {j : Nat}
    (hj : j < 16) {s : State} (h : ZInv s₀ m₁ s₁ j s) :
    WP isa (.block [.store8 (bufAt .r12) .rax, .alu .add .r12 (.imm 1), .alu .cmp .r12 (.imm 16)]) s
      fun s' => ZInv s₀ m₁ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 16)) := by
  have hrdi : s.gpr .rdi = st s₀ := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  refine wp_store8 (r := .rax) (a := bufB (st s₀) j) (by rw [ea_bufAt s .r12 h.r12, hrdi])
    (hp.buf_in h.wr hj) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_cmpi fun s₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have hr12 : s₃.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [u₃.gpr, g₂, h.r12, show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ofNat_succ]
  refine ⟨⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, by rw [g₄, hr12], by
      rw [g₄, u₃.other _ (by decide), g₂, h.rax], fun r h1 h2 => by
      rw [g₄, u₃.other r h2, g₂, h.keep r h1 h2], by rw [rd₄, u₃.rd, rd₂, h.rd],
      by rw [wr₄, u₃.wr, wr₂, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [m₄, u₃.mem, m₂]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega_using [hj]))
  · rw [m₄, u₃.mem, m₂, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.rax, show ¬ k < kf s₀ by have := h.j_le.1; omega_using [this],
        show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]
  · rw [z₄, hr12, se16', sub_beq (by omega_using [hj]) (by decide)]

theorem zeroLoop_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (h : ZInv s₀ m₁ s₁ (kf s₀) s) : WP isa zeroLoop s (ZInv s₀ m₁ s₁ 16) := by
  have hk := kf_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ m₁ s₁ j s) ?_ _ s
    ⟨kf s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by simp [eval, hz', hl], hl ▸ h'⟩
  · exact .inr ⟨by simp [eval, hz', hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (h : ZInv s₀ m₁ s₁ 16 s) :
    WP isa (.block [.mov32 .rax (.imm 1), .store8 (bufAt .rdx) .rax]) s (PInv s₀ m₁ s₁) := by
  have hk := kf_lt s₀
  have hrdi : s.gpr .rdi = st s₀ := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  refine wp_mov32i fun s₂ u₂ => ?_
  refine wp_store8 (r := .rax) (a := bufB (st s₀) (kf s₀))
    (by rw [ea_bufAt s₂ .rdx (by rw [u₂.other _ (by decide), h.keep _ (by decide) (by decide), h₁.rdx]),
      u₂.other _ (by decide), hrdi])
    (by rw [u₂.wr]; exact hp.buf_in h.wr hk) fun s₃ g₃ m₃ rd₃ wr₃ => WP.block_nil ?_
  refine ⟨fun r h1 h2 => by rw [g₃, u₂.other r h1, h.keep r h1 h2], by rw [rd₃, u₂.rd, h.rd],
    by rw [wr₃, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₃, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega_using [hk]))
  · rw [m₃, u₂.mem, writeW8_apply, u₂.gpr]
    by_cases hkj : k = kf s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
      decide
    · simp only [bufB_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true, padded]
      · simp only [h1, ite_false, hk', ite_true, padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    leNum (bytesAt m (off (st s₀) 56) 16) + 2 ^ 128 * (0 : BitVec 32).toNat = leNum (tail s₀ ++ [0x01]) := by
  have hk := kf_lt s₀
  have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (padded s₀) = (tail s₀ ++ [0x01]) ++ List.replicate (15 - kf s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (tail s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kf s₀ by omega_using [hlen, hk'], show k ≠ kf s₀ by omega_using [hlen, hk']]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rcx, .rsp, .r8, .r9, .r10], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  acc : H2 s₀ ≤ 4 → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧
    (s.gpr .rbp).toNat ≤ 4

theorem tail_nil {s₀ : State} (h : kf s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : F0 s₀ m₁ s₁) (hpos : 0 < kf s₀) : WP isa lastBlock s₁ (Tail s₀ m₁ s₁) := by
  have hk := kf_lt s₀
  refine WP.seq (WP.mono (zinit_ok hm h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₁ h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ .rax → r ≠ .r12 → s₄.gpr r = s₁.gpr r := h₄.keep
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hrdi : s₄.gpr .rdi = st s₀ := by rw [g _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  have hab := absorbBuf_ok s₄ (pad := 0) (Or.inl rfl) (by rw [h₄.wr, hrdi]; exact hp.st_in)
    (q := (R1 s₀).toNat / 4)
    (by rw [g .r8 (by decide) (by decide), h₁.r8]; exact r0_lt _)
    (by rw [g .r9 (by decide) (by decide), h₁.r9]; omega_using [hq]) (by omega_using [hq, hq'])
    (by rw [g .r10 (by decide) (by decide), h₁.r10])
  refine WP.mono hab fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr], by rw [k₅.2.1]; exact h₄.frame,
    fun hH2 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₅.gpr', g _ (by decide) (by decide)]
  · have hv4 : hval s₄ = A0 s₀ := by
      simp only [hval, g .r11 (by decide) (by decide), g .rbx (by decide) (by decide),
        g .rbp (by decide) (by decide)]
      exact h₁.hv
    have hb4 : (s₄.gpr .rbp).toNat ≤ 4 := by
      rw [g .rbp (by decide) (by decide), h₁.rbp]; exact hH2
    obtain ⟨hv, hb⟩ := ha hb4
    refine ⟨?_, hb⟩
    have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv4, hrdi, padded_value h₄.buf, g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide), h₁.r8, h₁.r9,
      Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen]), Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

/-- An addition with carry into a second word, as numbers, modulo `2¹²⁸`. -/
theorem add_adc_mod (a b c d : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      (a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat)) % 2 ^ 128 := by
  simp only [BitVec.toNat_add]
  rw [carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [ha, hb, h2]

theorem tagWords_eq : [Instr.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore =
    [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx, .mov .rbx (.mem (at_ .rdi 72)),
    .mov .rbp (.mem (at_ .rdi 80)), .mov .r12 (.mem (at_ .rdi 88)), .mov .r13 (.mem (at_ .rdi 96)),
    .mov .r14 (.mem (at_ .rdi 104)), .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
/-- Adding `s`, storing the tag and restoring the callee-saved registers. -/
theorem tagWords_ok (s : State) (hin : sR (s.gpr .rdi) ∈ s.wr) (hout : ⟨s.gpr .rcx, 16⟩ ∈ s.wr)
    (hsep : (sR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, 16⟩) :
    WP isa (.block (([.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] : List Instr) ++ restore)) s fun s' =>
      (s'.mem.readW (off (s.gpr .rcx) 0) 64).toNat + 2 ^ 64 * (s'.mem.readW (off (s.gpr .rcx) 8) 64).toNat =
        ((s.gpr .r11).toNat + (s.mem.readW (off (s.gpr .rdi) 40) 64).toNat +
          2 ^ 64 * ((s.gpr .rbx).toNat + (s.mem.readW (off (s.gpr .rdi) 48) 64).toNat)) % 2 ^ 128 ∧
      Frame [⟨s.gpr .rcx, 16⟩] s.mem s'.mem ∧
      s'.gpr .rbx = s.mem.readW (off (s.gpr .rdi) 72) 64 ∧ s'.gpr .rbp = s.mem.readW (off (s.gpr .rdi) 80) 64 ∧
      s'.gpr .r12 = s.mem.readW (off (s.gpr .rdi) 88) 64 ∧ s'.gpr .r13 = s.mem.readW (off (s.gpr .rdi) 96) 64 ∧
      s'.gpr .r14 = s.mem.readW (off (s.gpr .rdi) 104) 64 ∧ s'.gpr .r15 = s.mem.readW (off (s.gpr .rdi) 112) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rcx = s.gpr .rcx := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hin, contains_off hd (by omega_using [hd])⟩
  have o : ∀ d, d + 8 ≤ 16 → InRegions s.wr (off (s.gpr .rcx) d) 8 :=
    fun d hd => ⟨_, hout, contains_off hd (by omega_using [hd])⟩
  have i40 := i 40 (by decide); have i48 := i 48 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  have i3 := i 96 (by decide); have i4 := i 104 (by decide); have i5 := i 112 (by decide)
  have o0 := o 0 (by decide); have o8 := o 8 (by decide)
  -- The stores to the tag do not change the state.
  have sep : ∀ d, d + 8 ≤ 128 → ∀ e, e + 8 ≤ 16 → ∀ (m : Mem) (v : BitVec 64),
      (m.writeW (off (s.gpr .rcx) e) v).readW (off (s.gpr .rdi) d) 64 = m.readW (off (s.gpr .rdi) d) 64 :=
    fun d hd e he m v => Mem.readW_writeW_sep (hsep.sep (contains_off hd (by omega_using [hd]))
      (contains_off he (by omega_using [he]))) (by decide)
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
      rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    have r8 : ((s.mem.writeW (off (s.gpr .rcx) 0) (a + b)).writeW (off (s.gpr .rcx) 8)
        (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64)).readW
          (off (s.gpr .rcx) 8) 64 = c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64 :=
      Mem.readW_writeW_self64 _ _ _
    simp only [off] at r0 r8
    rw [r0, r8]
    exact add_adc_mod a b c d
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))

theorem off_zero (p : Addr) : off p 0 = p := by simp [off]

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : F0 s₀ m₁ s₁) {s : State} (ht : Tail s₀ m₁ s₁ s) :
    WP isa (.block (reduce ++ ([.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] : List Instr) ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [k₂.gpr' (r := .rdi), ht.keep .rdi (by simp), h₁.keep .rdi (by simp)]
  have rcx₂ : s₂.gpr .rcx = op s₀ := by
    rw [k₂.gpr' (r := .rcx), ht.keep .rcx (by simp), h₁.rcx]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.2.2.2, ht.wr]
  refine WP.mono (tagWords_ok s₂ (by rw [wr₂, rdi₂]; exact hp.st_in) (by rw [wr₂, rcx₂]; exact hp.o_in)
    (by rw [rdi₂, rcx₂]; exact hp.st_o)) fun s₃ ⟨hw, hf₃, g1, g2, g3, g4, g5, g6, g7, g8⟩ => ?_
  rw [rdi₂, rcx₂, k₂.2.1] at hw
  rw [rcx₂, k₂.2.1] at hf₃
  rw [rdi₂, k₂.2.1] at g1 g2 g3 g4 g5 g6
  -- The state outside the buffer is as the prologue left it.
  have low : ∀ d, d + 8 ≤ 56 ∨ 72 ≤ d → d + 8 ≤ 128 →
      s.mem.readW (off (st s₀) d) 64 = m₁.readW (off (st s₀) d) 64 := by
    intro d hd hd'
    refine ht.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq, bfR, off, ofInt_natCast]
    exact Offset.disjoint (st s₀) (by omega_using [hd]) (by omega_using [hd']) (by decide)
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hm.saved
  have hf : Frame [wR (st s₀), oR s₀] s₀.mem s₃.mem :=
    (hm.frame_wR.mono (by simp)).trans ((ht.frame.sub fun r hr => ⟨wR (st s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact bfR_sub_wR _⟩).trans (hf₃.mono (by simp)))
  refine ⟨⟨fun r hr => ?_, ?_⟩, by rw [g8, rcx₂], fun key msg hbuf hcnt => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, low 72 (by decide) (by decide), sv1]
    · rw [g2, low 80 (by decide) (by decide), sv2]
    · rw [g7, k₂.gpr' (r := .rsp), ht.keep .rsp (by simp), h₁.keep .rsp (by simp)]
    · rw [g3, low 88 (by decide) (by decide), sv3]
    · rw [g4, low 96 (by decide) (by decide), sv4]
    · rw [g5, low 104 (by decide) (by decide), sv5]
    · rw [g6, low 112 (by decide) (by decide), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.ret_st.sub_right (sub_sR _ (by decide))
    · exact hp.ret_o
  · obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
    have hk : kf s₀ = (W ++ B).length % 16 := hcnt
    have htail : tail s₀ = B := by rw [tail, hk, off_56, hBb]
    rw [← htail]
    obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hH2 := H2_le ⟨hlen, hkey, hacc⟩
    obtain ⟨hv, hb⟩ := ht.acc hH2
    have hR := hr hb
    rw [← off_24] at hkey
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := hkey
    have hA : accumulate (Rn s₀) W = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA]; exact Poly1305.accumulate_lt _ _
    have hV := Poly1305.absorbAll_lt (r := Rn s₀) hlt (tail s₀)
    rw [low 40 (by decide) (by decide), low 48 (by decide) (by decide), hm.readW_low (by decide),
      hm.readW_low (by decide)] at hw
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
    · omega_using [hw, hh]
    · change (s₃.mem.readW (off (op s₀) 8) 64).toNat = _; omega_using [hw, hh]

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ ⟨m₁, hm, h₁, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ m₁ s₁) ?_ fun s₂ h₂ => fepilogue_ok hp hm h₁ h₂)
  refine WP.ite (BitVec.ofNat 64 (kf s₀) &&& BitVec.ofNat 64 (kf s₀) == 0) (by simp [eval, hzf])
    (fun h => ?_) (fun h => ?_)
  · rw [BitVec.and_self, ofNat_beq_zero (by have := kf_lt s₀; omega_using [this])] at h
    simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, by rw [h₁.mem]; exact Frame.refl _ _,
      fun hH2 => ⟨?_, by rw [h₁.rbp]; exact hH2⟩⟩
    rw [tail_nil h, Poly1305.absorbAll_nil, h₁.hv]
  · rw [BitVec.and_self, ofNat_beq_zero (by have := kf_lt s₀; omega_using [this])] at h
    simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp hm h₁ (Nat.pos_of_ne_zero h)

/-- A state satisfying the precondition (with 128 bytes of working space at `rcx`). -/
def finalizeSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x3000 | .rcx => 0x5000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩, ⟨0x5000, 128⟩]

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeX86_64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.X86_64.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := finalize_correct (FPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeX86_64.pre
    Proof.Poly1305.finalizeX86_64.pub Impl.Poly1305.X86_64.finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem finalize_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.finalize (Spec.Poly1305.finalizeContract X86_64.abi)
      :=
  Verified.of_correct finalize_ok finalize_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86_64.abi,
            X86_64.argRegs]
        intro key msg hb hc
        exact h.2 key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86_64.abi,
          X86_64.argRegs,
          Proof.Poly1305.X86_64.finalizeSat]
          [Proof.Poly1305.X86_64.finalizeSat] using Proof.Poly1305.X86_64.finalizeSat }

end VG.Proof.Poly1305.X86_64
