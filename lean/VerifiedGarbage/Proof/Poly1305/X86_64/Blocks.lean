import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on x86-64: `blocks`

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The clamped `r`. -/
abbrev R0 : BitVec 64 := s₀.mem.readW (off (st s₀) 24) 64 &&& M0
abbrev R1 : BitVec 64 := s₀.mem.readW (off (st s₀) 32) 64 &&& M1
abbrev Rn : Nat := (R0 s₀).toNat + 2 ^ 64 * (R1 s₀).toNat
/-- The accumulator on entry, and its top word. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
abbrev H2 : Nat := (s₀.mem.readW (off (st s₀) 16) 64).toNat
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksX86_64.pre s₀) : BPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- What holds between blocks, after `i` of them, with the memory `m₁` left
by the prologue. -/
structure Common (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r8 : s.gpr .r8 = R0 s₀
  r9 : s.gpr .r9 = R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : H2 s₀ ≤ 4 →
    hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ (s.gpr .rbp).toNat ≤ 4

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop extends Common s₀ m₁ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)

/-- The memory the prologue leaves. -/
structure Mem₁ (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [svR (st s₀)] s₀.mem m₁
  saved : Saved (st s₀) s₀ m₁

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 8 := by
  have := hp.nb_lt
  rw [ofInt_natCast, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

/-- Block words read from memory the code has written only in the state. -/
theorem blk_word {m : Mem} (hf : Frame [sR (st s₀)] s₀.mem m) {i d : Nat} (hi : i < nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 64 =
      s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 64 :=
  hf.readW (hp.blk_contains hi hd) (by simpa using hp.st_bl.symm) (by decide)

end BPre

theorem Mem₁.frame_sR {s₀ : State} {m₁ : Mem} (h : Mem₁ s₀ m₁) : Frame [sR (st s₀)] s₀.mem m₁ :=
  h.frame.sub fun r hr => ⟨sR (st s₀), List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_sR _ (by decide)⟩

theorem Mem₁.frame_wR {s₀ : State} {m₁ : Mem} (h : Mem₁ s₀ m₁) : Frame [wR (st s₀)] s₀.mem m₁ :=
  h.frame.sub fun r hr => ⟨wR (st s₀), List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact svR_sub_wR _⟩

/-- A word of the accumulator or the key, which the prologue does not change. -/
theorem Mem₁.readW_low {s₀ : State} {m₁ : Mem} (h : Mem₁ s₀ m₁) {d : Nat} (hd : d + 8 ≤ 56) :
    m₁.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine h.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq, svR, off, ofInt_natCast]
  exact Offset.disjoint (st s₀) (by omega_using [hd]) (by omega_using [hd]) (by decide)

theorem se16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keeps [.rsi, .rcx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.some.injEq, exists_eq_left', se16, se1]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [sR (st s₀)] s₀.mem m)
    {i : Nat} (hi : i < nb s₀) :
    word m (blkAddr s₀ i) 0 + 2 ^ 64 * word m (blkAddr s₀ i) 8 + 2 ^ 128 * (1 : BitVec 32).toNat =
      leNum (bytesAt s₀.mem (blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [word]
  rw [hp.blk_word hf hi (by decide), hp.blk_word hf hi (by decide), Poly1305.leNum_append,
    Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  rw [h1, h2]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

theorem body_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : LInv s₀ m₁ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ m₁ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ m₁ (i + 1) s') := by
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hin : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.rsi, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hr0 : (s.gpr .r8).toNat < 2 ^ 60 := by rw [hL.r8]; exact r0_lt _
  have hr1 : (s.gpr .r9).toNat = 4 * ((R1 s₀).toNat / 4) := by rw [hL.r9]; omega_using [hq]
  have hq2 : (R1 s₀).toNat / 4 < 2 ^ 58 := by omega_using [hq, hq']
  have hs1 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4) := hL.r10
  have hab := absorb_ok s (pad := 1) (Or.inr rfl) hr0 hr1 hq2 hs1 (hin 0 (by decide)) (hin 8 (by decide))
  rw [body]
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance_ok s₁) fun s₂ ⟨a₁, a₂, a₃, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : Common s₀ m₁ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hH2 => ?_⟩
    · rw [k.gpr' (r := .rdi), hL.rdi]
    · rw [k.gpr' (r := .rsp), hL.rsp]
    · rw [k.gpr' (r := .r8), hL.r8]
    · rw [k.gpr' (r := .r9), hL.r9]
    · rw [k.gpr' (r := .r10), hL.r10]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv, hb⟩ := hL.acc hH2
      obtain ⟨hv', hb'⟩ := ha hb
      have hval₂ : hval s₂ = hval s₁ := by
        simp only [hval, k₂.gpr' (r := .r11), k₂.gpr' (r := .rbx), k₂.gpr' (r := .rbp)]
      have hrbp₂ : s₂.gpr .rbp = s₁.gpr .rbp := k₂.gpr'
      refine ⟨?_, by rw [hrbp₂]; exact hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [hval₂, hv', hL.rsi, hL.mem, block_value hp (hL.mem ▸ hm.frame_sR) hi, hL.r8, hL.r9,
        mod_step hv, blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hrcx : s₂.gpr .rcx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .rcx), hL.rcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval .ne s₂ = some (!(BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, a₃, Option.map_some]; rw [← hrcx, a₂]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have := hp.nb_lt
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with rsi := ?_, rcx := hrcx }⟩
    rw [a₁, k₁.gpr' (r := .rsi), hL.rsi, blkAddr, blkAddr,
      show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, Nat.mul_succ]

/-! ## Prologue and epilogue -/

set_option simprocs false in
theorem mov_rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx)]) s fun s' =>
      s'.gpr .rcx = s.gpr .rdx ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp [hr]

set_option simprocs false in
theorem test_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .test r (.reg r)]) s fun s' =>
      s'.zf = some (s.gpr r &&& s.gpr r == 0) ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r _ => rfl, rfl, rfl, rfl⟩

theorem prologue_eq : save ++ ([.mov .rcx (.reg .rdx)] : List Instr) ++ setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr) =
    save ++ (([.mov .rcx (.reg .rdx)] : List Instr) ++ (setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) := by
  simp only [List.append_assoc]

theorem blks_zero (s₀ : State) : blks s₀ 0 = [] := by simp [blks, bytesAt]

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (save ++ ([.mov .rcx (.reg .rdx)] : List Instr) ++ setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s₀
      fun s => ∃ m₁, Mem₁ s₀ m₁ ∧ Common s₀ m₁ 0 s ∧ s.gpr .rsi = bp s₀ ∧
        s.gpr .rcx = s₀.gpr .rdx ∧ s.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [prologue_eq]
  refine WP.block_append (WP.mono (save_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ ⟨g₁, rd₁, wr₁, _, _, f₁, sv₁⟩ => ?_)
  have hm : Mem₁ s₀ s₁.mem := ⟨f₁, sv₁⟩
  refine WP.block_append (WP.mono (mov_rcx_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [k₂.gpr' (r := .rdi), g₁]
  refine WP.block_append (WP.mono (setup_ok s₂ (by
    rw [k₂.2.2.2, wr₁, hp.wr, rdi₂]; exact List.mem_append_right _ (List.mem_singleton_self _)))
    fun s₃ ⟨e8, e9, e10, e11, e12, e13, k₃⟩ => ?_)
  refine WP.mono (test_ok s₃ .rcx) fun s₄ ⟨z₄, k₄⟩ => ?_
  have k := (k₂.trans k₃).trans k₄
  rw [k₂.2.1, rdi₂, hm.readW_low (by decide)] at e8 e9 e11 e12 e13
  have g : ∀ r, r ∉ [Reg.rcx, .rax, .r8, .r9, .r10, .r11, .rbx, .rbp] → s₄.gpr r = s₀.gpr r :=
    fun r hr => by rw [k.1 r (by simpa using hr), g₁]
  refine ⟨s₁.mem, hm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hH2 => ?_⟩, ?_, ?_, ?_⟩
  · exact g .rdi (by decide)
  · exact g .rsp (by decide)
  · rw [k₄.gpr' (r := .r8), e8]
  · rw [k₄.gpr' (r := .r9), e9]
  · rw [k₄.gpr' (r := .r10), e10, e9]
  · rw [k.2.2.1, rd₁]
  · rw [k.2.2.2, wr₁]
  · rw [k.2.1]
  · rw [blks_zero, Poly1305.absorbAll_nil]
    simp only [hval, k₄.gpr' (r := .r11), k₄.gpr' (r := .rbx), k₄.gpr' (r := .rbp), e11, e12, e13]
    refine ⟨?_, hH2⟩
    rw [A0, leNum_acc]
  · exact g .rsi (by decide)
  · rw [k₄.gpr' (r := .rcx), k₃.gpr' (r := .rcx), c₂, g₁]
  · rw [z₄, k₃.gpr' (r := .rcx), c₂, g₁]

/-- The memory after storing `h0, h1, h2` in the state. -/
def storeH (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) h0).writeW (off st 8) h1).writeW (off st 16) h2

theorem storeRestore_eq : [Instr.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
    .store (at_ .rdi 16) .rbp] ++ restore = [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
    .store (at_ .rdi 16) .rbp, .mov .rbx (.mem (at_ .rdi 72)), .mov .rbp (.mem (at_ .rdi 80)),
    .mov .r12 (.mem (at_ .rdi 88)), .mov .r13 (.mem (at_ .rdi 96)), .mov .r14 (.mem (at_ .rdi 104)),
    .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
/-- Storing `h` and restoring the callee-saved registers. -/
theorem storeRestore_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block (([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] : List Instr) ++ restore)) s fun s' =>
      let m := storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)
      s'.mem = m ∧ s'.gpr .rbx = m.readW (off (s.gpr .rdi) 72) 64 ∧
      s'.gpr .rbp = m.readW (off (s.gpr .rdi) 80) 64 ∧ s'.gpr .r12 = m.readW (off (s.gpr .rdi) 88) 64 ∧
      s'.gpr .r13 = m.readW (off (s.gpr .rdi) 96) 64 ∧ s'.gpr .r14 = m.readW (off (s.gpr .rdi) 104) 64 ∧
      s'.gpr .r15 = m.readW (off (s.gpr .rdi) 112) 64 ∧ s'.gpr .rsp = s.gpr .rsp := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  have i3 := i 96 (by decide); have i4 := i 104 (by decide); have i5 := i 112 (by decide)
  simp only [off] at o0 o8 o16 i0 i1 i2 i3 i4 i5
  apply WP.of_runBlock
  rw [storeRestore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.load64, State.setReg, o0, o8, o16, i0, i1, i2, i3, i4, i5,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem storeH_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') (h0 h1 h2 : BitVec 64) :
    Frame [hR st, wR st] m (storeH m' st h0 h1 h2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _ (c 8 (by decide))).writeW
    List.mem_cons_self _ (c 16 (by decide))

theorem storeH_saved (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) {d : Nat} (h₁ : 24 ≤ d)
    (h₂ : d < 2 ^ 32) : (storeH m st h0 h1 h2).readW (off st d) 64 = m.readW (off st d) 64 := by
  simp only [storeH]
  rw [readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂]),
    readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂]),
    readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂])]

theorem storeH_acc (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) :
    leNum (bytesAt (storeH m st h0 h1 h2) st 24) = h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat := by
  rw [leNum_acc]
  simp only [storeH]
  rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    Mem.readW_writeW_self64]

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem H2_le {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : H2 s₀ ≤ 4 := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2, leNum_acc] at this
  simp only [H2, P] at this ⊢
  omega_using [this]

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s : State}
    (hc : Common s₀ m₁ (nb s₀) s) :
    WP isa (.block (reduce ++ ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] : List Instr) ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [k₁.gpr' (r := .rdi), hc.rdi]
  have hw : sR (s₁.gpr .rdi) ∈ s₁.wr := by
    rw [k₁.2.2.2, hc.wr, hp.wr, rdi₁]; exact List.mem_singleton_self _
  refine WP.mono (storeRestore_ok s₁ hw) fun s₂ ⟨m₂, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
  rw [rdi₁, k₁.2.1, hc.mem] at m₂ g1 g2 g3 g4 g5 g6
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hm.saved
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeH_frame (hm.frame_wR.mono (by simp)) _ _ _
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, storeH_saved _ _ _ _ _ (by decide) (by decide), sv1]
    · rw [g2, storeH_saved _ _ _ _ _ (by decide) (by decide), sv2]
    · rw [g7, k₁.gpr' (r := .rsp), hc.rsp]
    · rw [g3, storeH_saved _ _ _ _ _ (by decide) (by decide), sv3]
    · rw [g4, storeH_saved _ _ _ _ _ (by decide) (by decide), sv4]
    · rw [g5, storeH_saved _ _ _ _ _ (by decide) (by decide), sv5]
    · rw [g6, storeH_saved _ _ _ _ _ (by decide) (by decide), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    have hd := hp.ret_st
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hd.sub_right (Region.sub_prefix (by decide))
    · exact hd.sub_right (sub_sR _ (by decide))
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hH2 := H2_le ⟨hlen, hkey, hacc⟩
    obtain ⟨hv, hb⟩ := hc.acc hH2
    have hR := hr hb
    rw [← off_24] at hkey
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := hkey
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
    · rw [← off_24, key_frame hf, hkey']
    · rw [m₂, storeH_acc, ← hkey', clamp_key, Poly1305.accumulate_append hlen]
      have hA : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
      rw [hA]
      change hval s₁ = _
      have hlt : A0 s₀ < P := by rw [← hA]; exact Poly1305.accumulate_lt _ _
      rw [hR, hv, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨m₁, hm, hc, hrsi, hrcx, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ m₁ (nb s₀)) ?_ fun s₂ hc₂ => epilogue_ok hp hm hc₂)
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ m₁ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ m₁ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hm hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ m₁ 0 s₁ :=
      { hc with
        rsi := by rw [hrsi]; simp [blkAddr]
        rcx := by rw [hrcx]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksX86_64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.X86_64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksX86_64.pre Proof.Poly1305.blocksX86_64.pub
    Impl.Poly1305.X86_64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem blocks_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.blocks (Spec.Poly1305.blocksContract X86_64.abi) :=
  Verified.of_correct blocks_ok blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Poly1305.X86_64.blocksSat] using
      Proof.Poly1305.X86_64.blocksSat)

end VG.Proof.Poly1305.X86_64
