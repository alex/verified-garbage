import VerifiedGarbage.Proof.Poly1305.X86.Buffer
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on x86 (32-bit): `finalize`
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev op : BitVec 32 := arg s₀ 3
abbrev oR : Region := ⟨(op s₀).setWidth 64, 16⟩
abbrev fsR : Region := ⟨(arg s₀ 4).setWidth 64, 128⟩
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨argAddr s₀ 0, 20⟩]
  wr : s₀.wr = [sR (stp s₀), oR s₀, fsR s₀]
  st_o : (sR (stp s₀)).Disjoint (oR s₀)
  st_sc : (sR (stp s₀)).Disjoint (fsR s₀)
  o_sc : (oR s₀).Disjoint (fsR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (sR (stp s₀))
  arg_o : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (oR s₀)
  arg_sc : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (fsR s₀)
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_sc : (retR s₀).Disjoint (fsR s₀)
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  o_fit : (op s₀).toNat + 16 ≤ 2 ^ 32
  sc_fit : (arg s₀ 4).toNat + 128 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86.pre s₀) : FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

namespace FPre
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 20⟩, by rw [hp.rd]; simp, arg_contains (n := 20) (by have := hp.sp_fit; omega_using [this])
    (by omega_using [hi])⟩

/-- An argument, in memory the code has written only in the state and `out`. -/
theorem arg_same {m : Mem} (hf : Frame [sR (stp s₀), oR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains (n := 20) (by have := hp.sp_fit; omega_using [this]) (by omega_using [hi]))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
        <;> [exact hp.arg_st; exact hp.arg_o]) (by decide)

theorem st_in : sR (stp s₀) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self

theorem o_in : oR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end FPre

/-! ## Prologue -/

/-- After the prologue, with the words `F` of `setup`. -/
structure F0 (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  buf : bytesAt s.mem (bq (stp s₀)) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s.mem

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (setup ++ ([.mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15),
      .alu .test .edx (.reg .edx)] : List Instr))) s₀ fun s => ∃ F, SetupF s₀ F ∧ F0 s₀ F s ∧
        s.gpr .edx = BitVec.ofNat 32 (kb s₀) ∧
        s.zf = some (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit hp.st_in)
    fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  have hF' := SetupF.of hF sv co
  have hf₁ : Frame [sR (stp s₀), oR s₀] s₀.mem s₁.mem := A₁.frame.mono (by simp)
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine wp_andx (readSrc_imm _ _) fun s₃ u₃ => wp_test fun s₄ k₄ z₄ => WP.block_nil ?_
  have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
  have hedx₃ : s₃.gpr .edx = BitVec.ofNat 32 (kb s₀) := by
    rw [u₃.gpr, u₂.gpr, hp.arg_same hf₁ (i := 1) (by decide), and15]
  have hw : ∀ k < 32, words s₄.mem (stp s₀) k = F k := fun k hk => by rw [hm]; exact A₁.words k hk
  refine ⟨F, hF', ⟨⟨c₁.keep (by rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, by rw [hm]; exact A₁.frame,
      by rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd], by rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr],
      fun k hk _ _ => hw k hk⟩, ?_, fun hA => ?_⟩, by rw [k₄.1 _ (by simp), hedx₃], by rw [z₄, hedx₃]⟩
  · rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
  · refine bytes_words hfit (fun k h₁ h₂ => ?_) (Nat.le_of_lt (kb_lt s₀))
    rw [hw k (by omega_using [h₁, h₂]), hF'.low k (by omega_using [h₂]) (by omega_using [h₁, h₂])]
  · exact acc_entry hfit hF' (fun k hk => hw k (by omega_using [hk])) hA

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kb s₀ then (Bf s₀).getD k 0 else if k = kb s₀ then 1 else 0

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : BitVec 32) (f : Nat → Byte) : Prop :=
  ∀ k < 16, m (bq st + BitVec.ofNat 64 k) = f k

theorem bytesAt_buf {m : Mem} {st : BitVec 32} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (bq st) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  exact List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

theorem bq_ne {st : BitVec 32} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bq st + BitVec.ofNat 64 j ≠ bq st + BitVec.ofNat 64 k := by
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := (bq st).isLt
  omega

/-- The buffered bytes in the memory the prologue leaves. -/
theorem F0.byte {s₀ : State} {F : Nat → Nat} {s : State} (h : F0 s₀ F s) {k : Nat} (hk : k < kb s₀) :
    s.mem (bq (stp s₀) + BitVec.ofNat 64 k) = (Bf s₀).getD k 0 := by
  rw [← h.buf]
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZeroInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kb s₀ ≤ j ∧ j ≤ 16
  ecx : s.gpr .ecx = stp s₀ + BitVec.ofNat 32 j
  edx : s.gpr .edx = BitVec.ofNat 32 j
  eax : s.gpr .eax = 0
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [bfR (stp s₀)] s₁.mem s.mem
  buf : BufHas s.mem (stp s₀) fun k =>
    if k < kb s₀ then (Bf s₀).getD k 0 else if k < j then 0 else s₁.mem (bq (stp s₀) + BitVec.ofNat 64 k)

theorem zinit_ok {s₀ : State} {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁)
    (hedx : s₁.gpr .edx = BitVec.ofNat 32 (kb s₀)) :
    WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.reg .edx), .alu .add .ecx (.reg .edi)]) s₁
      (ZeroInv s₀ s₁ (kb s₀)) := by
  refine wp_movi fun s₂ u₂ _ => wp_mov fun s₃ u₃ _ => wp_addx (readSrc_reg _ _) fun s₄ u₄ _ =>
    WP.block_nil ⟨⟨(Nat.le_refl _), Nat.le_of_lt (kb_lt s₀)⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [u₄.rd, u₃.rd, u₂.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr], by rw [u₄.mem, u₃.mem, u₂.mem]; exact Frame.refl _ _, fun k hk => ?_⟩
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), hedx,
      h₁.ctx.edi, BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hedx]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other r h2, u₃.other r h2, u₂.other r h1]
  · rw [u₄.mem, u₃.mem, u₂.mem]
    by_cases hkf : k < kb s₀
    · simp only [hkf, ite_true]; exact h₁.byte hkf
    · simp only [hkf, ite_false]

theorem zero_step {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) {j : Nat}
    (hj : j < 16) {s : State} (h : ZeroInv s₀ s₁ j s) :
    WP isa (.block [.store8 (at_ .ecx 56) .al, .alu .add .ecx (.imm 1), .alu .add .edx (.imm 1),
      .alu .cmp .edx (.imm 16)]) s fun s' => ZeroInv s₀ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 16)) := by
  have hfit := hp.st_fit
  refine wp_store8 (r := .al) (a := bq (stp s₀) + BitVec.ofNat 64 j)
    (by rw [ea_at, h.ecx, addr_buf hfit (by omega_using [hj])])
    (by rw [h.wr, h₁.wr]; exact ⟨_, hp.st_in, bfR_sub hfit _ (bfR_contains _ (d := j) (n := 1) (by omega_using [hj]))⟩)
    fun s₂ m₂ => ?_
  refine wp_addx (readSrc_imm _ _) fun s₃ u₃ _ => wp_addx (readSrc_imm _ _) fun s₄ u₄ _ => ?_
  refine wp_cmpx (readSrc_imm _ _) fun s₅ k₅ z₅ _ => WP.block_nil ?_
  have hedx : s₄.gpr .edx = BitVec.ofNat 32 (j + 1) := by
    rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.edx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add]
  refine ⟨⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, by rw [k₅.gpr', hedx], ?_,
      fun r h1 h2 h3 => ?_, by rw [k₅.2.2.1, u₄.rd, u₃.rd, m₂.rd, h.rd],
      by rw [k₅.2.2.2, u₄.wr, u₃.wr, m₂.wr, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [k₅.gpr', u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.ecx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  · rw [k₅.gpr', u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.eax]
  · rw [k₅.1 r List.not_mem_nil, u₄.other r h3, u₃.other r h2, m₂.gpr, h.keep r h1 h2 h3]
  · rw [k₅.2.1, u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_contains _ (by omega_using [hj]))
  · rw [k₅.2.1, u₄.mem, u₃.mem, m₂.mem, Poly1305.writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, show Reg8.al.reg = Reg.eax from rfl, h.eax,
        show ¬ k < kb s₀ by have := h.j_le.1; omega_using [this], show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [bq_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kb s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]
  · rw [z₅, hedx, eq16_beq (by omega_using [hj])]

theorem zeroLoop_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) {s : State}
    (h : ZeroInv s₀ s₁ (kb s₀) s) : WP isa zeroLoop s (ZeroInv s₀ s₁ 16) := by
  have hk := kb_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZeroInv s₀ s₁ j s) ?_ _ s
    ⟨kb s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by simp [eval, hz', hl], hl ▸ h'⟩
  · exact .inr ⟨by simp [eval, hz', hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [bfR (stp s₀)] s₁.mem s.mem
  buf : BufHas s.mem (stp s₀) (padded s₀)

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) {s : State}
    (h : ZeroInv s₀ s₁ 16 s) :
    WP isa (.block [.mov .eax (.imm 1), .mov .ecx (.mem (at_ .esp 8)), .alu .and .ecx (.imm 15),
      .alu .add .ecx (.reg .edi), .store8 (at_ .ecx 56) .al]) s (PInv s₀ s₁) := by
  have hfit := hp.st_fit
  have hk := kb_lt s₀
  have hedi : s.gpr .edi = stp s₀ := by
    rw [h.keep _ (by decide) (by decide) (by decide), h₁.ctx.edi]
  have hesp : s.gpr .esp = s₀.gpr .esp := by
    rw [h.keep _ (by decide) (by decide) (by decide), h₁.esp]
  have hf : Frame [sR (stp s₀), oR s₀] s₀.mem s.mem :=
    (h₁.frame.trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, bfR_sub hfit⟩)).mono (by simp)
  refine wp_movi fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, u₂.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, h.rd, h.wr, h₁.rd, h₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine wp_andx (readSrc_imm _ _) fun s₄ u₄ => wp_addx (readSrc_reg _ _) fun s₅ u₅ _ => ?_
  have hecx : s₅.gpr .ecx = stp s₀ + BitVec.ofNat 32 (kb s₀) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.mem, hp.arg_same hf (i := 1) (by decide), and15, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hedi, BitVec.add_comm]
  refine wp_store8 (r := .al) (a := bq (stp s₀) + BitVec.ofNat 64 (kb s₀))
    (by rw [ea_at, hecx, addr_buf hfit (by omega_using [hk])])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr, h₁.wr]
        exact ⟨_, hp.st_in, bfR_sub hfit _ (bfR_contains _ (d := kb s₀) (n := 1) (by omega_using [hk]))⟩)
    fun s₆ m₆ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, by rw [m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₆.gpr, u₅.other r h2, u₄.other r h2, u₃.other r h2, u₂.other r h1, h.keep r h1 h2 h3]
  · rw [m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_contains _ (by omega_using [hk]))
  · rw [m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, Poly1305.writeW8_apply,
      show Reg8.al.reg = Reg.eax from rfl, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
    by_cases hkj : k = kb s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
      decide
    · simp only [bq_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < kb s₀
      · simp only [h1, ite_true, padded]
      · simp only [h1, ite_false, hk', ite_true, padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (stp s₀) (padded s₀)) :
    leNum (bytesAt m (bq (stp s₀)) 16) = leNum (Bf s₀ ++ [0x01]) := by
  have hk := kb_lt s₀
  have hlen : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (padded s₀) = (Bf s₀ ++ [0x01]) ++ List.replicate (15 - kb s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kb s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (Bf s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kb s₀ by omega_using [hlen, hk'], show k ≠ kb s₀ by omega_using [hlen, hk']]
  rw [bytesAt_buf h, hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero,
    Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure TInv (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  acc : Acc s₀ (Bf s₀) s.mem

theorem Bf_nil {s₀ : State} (h : kb s₀ = 0) : Bf s₀ = [] := by
  simp [Bf, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s₁ : State}
    (h₁ : F0 s₀ F s₁) (hedx : s₁.gpr .edx = BitVec.ofNat 32 (kb s₀)) (hpos : 0 < kb s₀) :
    WP isa lastBlock s₁ (TInv s₀ F) := by
  have hfit := hp.st_fit
  have hk := kb_lt s₀
  refine WP.seq (WP.mono (zinit_ok h₁ hedx) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₁ h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have hU₄ : UCommon s₀ F s₄ := h₁.toUCommon.buf (h₄.keep _ (by decide) (by decide) (by decide))
    (h₄.keep _ (by decide) (by decide) (by decide)) h₄.frame h₄.rd h₄.wr hfit
  have hacc₄ : Acc s₀ [] s₄.mem := h₁.acc.words fun k hk => words_bf hfit h₄.frame (by omega_using [hk]) (by omega_using [hk])
  have hc := hU₄.ctx
  refine WP.mono (absorbAtFull_ok hc (bp := stp s₀ + BitVec.ofNat 32 56) (absorbBuf_okList 0)
    (fun h => absurd h (by decide)) (by decide) (fun k _ => by rw [hc.edi, buf_ea])
    (fun k hk => by rw [← buf_ea]; exact hc.inRW (by omega_using [hk]) (by decide))
    (fun k _ => .inr (by rw [← buf_ea]; congr 1; omega_using [])) (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁' h₂' => hU₄.keep k (by omega_using [h₁', h₂']) (not_hS (.inl ⟨by omega_using [h₁', h₂'], h₂'⟩))
      (.inr h₁'), (hacc₄ hA).1⟩))
    fun s' ⟨S, ha⟩ => ?_
  refine ⟨⟨hc.keep (S.gpr _ (by decide)) S.wr, by rw [S.gpr _ (by decide)]; exact hU₄.esp,
    hU₄.frame.trans S.frame, by rw [S.rd]; exact hU₄.rd, by rw [S.wr]; exact hU₄.wr,
    fun k hk hS h' => (S.same k hk hS).trans (hU₄.keep k hk hS h')⟩, fun hA => ?_⟩
  obtain ⟨-, hv⟩ := hacc₄ hA
  obtain ⟨h4, hv'⟩ := ha hA
  refine ⟨h4, ?_⟩
  have hlen : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
  rw [Poly1305.absorbAll_nil] at hv
  rw [hv', buf_value hfit, padded_value h₄.buf, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero,
    Nat.add_zero, mod_step hv, Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen])]

/-! ## Regions -/

/-- The bytes `[x + d, x + d + n)` of a region of `k` bytes at `x`. -/
theorem contains0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    (⟨x.setWidth 64, k⟩ : Region).Contains (addr x d) n := by
  have := sub_contains (x := x) (a := 0) (k := k) (d := d) (n := n) (by omega_using [hx]) (by omega_using []) (by omega_using [h]) hn
  simpa [sub, addr] using this

theorem sub_sub0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    Region.Sub (sub x d n) ⟨x.setWidth 64, k⟩ := fun a ha =>
  (contains0 hx h hn).byte (by simp only [Region.Contains] at ha; omega_using [ha])


/-- The words of the state, after writes only to a region disjoint from it. -/
theorem words_frame {m m' : Mem} {st o : BitVec 32} (hst : st.toNat + 128 ≤ 2 ^ 32)
    (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) (hf : Frame [⟨o.setWidth 64, 16⟩] m m') {k : Nat}
    (hk : k < 32) : words m' st k = words m st k := by
  show wv _ _ _ = wv _ _ _
  rw [wv, wv, wd_frame hf (by
    simp only [List.mem_singleton]; rintro r rfl; exact hd.sub_left (sub_sub0 hst (by omega_using [hk]) (by decide)))]

/-! ## After the last bytes -/

/-! ## The tag -/

theorem words_lt (m : Mem) (st : BitVec 32) (k : Nat) : words m st k < 2 ^ 32 := BitVec.isLt _

/-- Word `i` of `h` plus word `i` of `s`. -/
abbrev ta (m : Mem) (st : BitVec 32) (i : Nat) : Nat := words m st i + words m st (10 + i)

/-- The carry into word `k` of the tag. -/
def cs (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (a k + cs a k) / 2 ^ 32

theorem cs_succ (a : Nat → Nat) (k : Nat) : cs a (k + 1) = (a k + cs a k) / 2 ^ 32 := rfl

theorem cs_le {a : Nat → Nat} (ha : ∀ i, a i < 2 ^ 33 - 1) : ∀ k, cs a k ≤ 1
  | 0 => Nat.zero_le _
  | k + 1 => by rw [cs_succ]; have := cs_le ha k; have := ha k; omega

/-- The words of the tag: those of `x + y` modulo `2¹²⁸`. -/
theorem tag_words (x y : Nat → Nat) {X : Nat}
    (hX : X % 2 ^ 128 = x 0 + 2 ^ 32 * x 1 + 2 ^ 64 * x 2 + 2 ^ 96 * x 3) {k : Nat} (hk : k < 4) :
    (x k + y k + cs (fun i => x i + y i) k) % 2 ^ 32 =
      (X + (y 0 + 2 ^ 32 * y 1 + 2 ^ 64 * y 2 + 2 ^ 96 * y 3)) / 2 ^ (32 * k) % 2 ^ 32 := by
  obtain ⟨a0, a1, a2, a3⟩ := addS_arith (x0 := x 0) (x1 := x 1) (x2 := x 2) (x3 := x 3) (s0 := y 0)
    (s1 := y 1) (s2 := y 2) (s3 := y 3) X _ hX rfl
  have c1 : cs (fun i => x i + y i) 1 = (x 0 + y 0) / 2 ^ 32 := rfl
  have c2 : cs (fun i => x i + y i) 2 = (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32 := rfl
  have c3 : cs (fun i => x i + y i) 3 =
      (x 2 + y 2 + (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32 := rfl
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show cs (fun i => x i + y i) 0 = 0 from rfl, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    exact a0
  · rw [c1]; exact a1
  · rw [c2]; exact a2
  · rw [c3]; exact a3

/-- The tag's words so far, from the state `s` before them. -/
structure TagInv (st o : BitVec 32) (s : State) (k : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem
  out : ∀ i < k, wv s'.mem o (4 * i) = (ta s.mem st i + cs (ta s.mem st) i) % 2 ^ 32
  cf : 0 < k → ∃ c, s'.cf = some c ∧ c.toNat = cs (ta s.mem st) k

theorem tagWord_ok {st o : BitVec 32} {s₁ : State} (hc : Ctx st s₁) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (hesi : s₁.gpr .esi = o) (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s₁.wr)
    (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) {k : Nat} (hk : k < 4) {s : State}
    (h : TagInv st o s₁ k s) :
    WP isa (.block [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax]) s (TagInv st o s₁ (k + 1)) := by
  have hfit := hc.fit
  have hw : ∀ j < 32, words s.mem st j = words s₁.mem st j := fun j hj => words_frame hfit hd h.frame hj
  have edi : s.gpr .edi = st := by rw [h.gpr _ (by decide), hc.edi]
  have hta : ∀ i, ta s₁.mem st i < 2 ^ 33 - 1 := fun i => by
    have := words_lt s₁.mem st i; have := words_lt s₁.mem st (10 + i)
    show words s₁.mem st i + words s₁.mem st (10 + i) < _
    omega
  have hcs : cs (ta s₁.mem st) k ≤ 1 := cs_le hta k
  have htk := hta k
  refine wp_movm (a := addr st (4 * k)) (by rw [ea_at, edi]; rfl)
    (by rw [h.rd, h.wr]; exact hc.inRW (by omega_using [hk]) (by decide)) fun s₂ u₂ cf₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = words s₁.mem st k := by rw [u₂.gpr, ← hw k (by omega_using [hk])]; rfl
  have hx : readSrc s₂ (.mem (at_ .edi (40 + 4 * k))) = some (s.mem.readW (addr st (40 + 4 * k)) 32) := by
    rw [readSrc_mem (a := addr st (40 + 4 * k)) (by rw [ea_at, u₂.other _ (by decide), edi])
      (by rw [u₂.rd, u₂.wr, h.rd, h.wr]; exact hc.inRW (by omega_using [hk]) (by decide)), u₂.mem]
  have ex : (s.mem.readW (addr st (40 + 4 * k)) 32).toNat = words s₁.mem st (10 + k) := by
    rw [← hw (10 + k) (by omega_using [hk])]
    show _ = wv _ _ (4 * (10 + k))
    rw [show 4 * (10 + k) = 40 + 4 * k by omega_using []]
  have fin : ∀ (s₃ : State) (y : BitVec 32), Upd s₂ s₃ .eax y →
      y.toNat = (ta s₁.mem st k + cs (ta s₁.mem st) k) % 2 ^ 32 →
      s₃.cf = some (decide (2 ^ 32 ≤ ta s₁.mem st k + cs (ta s₁.mem st) k)) →
      WP isa (.block [.store (at_ .esi (4 * k)) .eax]) s₃ (TagInv st o s₁ (k + 1)) := by
    intro s₃ y u₃ hy cf₃
    refine wp_store (a := addr o (4 * k))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), h.gpr _ (by decide), hesi])
      (by rw [u₃.wr, u₂.wr, h.wr]; exact ⟨_, hout, contains0 ho (by omega_using [hk]) (by decide)⟩) fun s₄ u₄ =>
        WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, fun i hi => ?_, fun _ => ⟨_, by rw [u₄.cf]; exact cf₃, ?_⟩⟩
    · rw [u₄.gpr, u₃.other r hr, u₂.other r hr, h.gpr r hr]
    · rw [u₄.rd, u₃.rd, u₂.rd, h.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, h.wr]
    · rw [u₄.mem, u₃.mem, u₂.mem]
      exact h.frame.writeW (List.mem_singleton_self _) _ (contains0 ho (by omega_using [hk]) (by decide))
    · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem]
      by_cases hik : i = k
      · subst hik; rw [wv, wd_write_self]; exact hy
      · rw [wv, wd_write_ne _ _ (by omega_using [ho, hk, hi]) (by omega_using [ho, hk]) (by omega_using [hi, hik])]; exact h.out i (by omega_using [hi, hik])
    · rw [carry_dec (by omega_using [hcs, htk, hy]), cs_succ]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [ite_eq_left rfl]
    refine wp_addx hx fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [BitVec.toNat_add, e₂, ex]; rfl
    · rw [cf₃, e₂, ex]; rfl
  · rw [ite_eq_right (by omega_using [hk, hk0])]
    obtain ⟨c, hcf, hcv⟩ := h.cf hk0
    refine wp_adcx hx (by rw [cf₂, hcf]) fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [add3_toNat, e₂, ex, hcv]
    · rw [cf₃, e₂, ex, hcv]

/-- `addS`: the tag into `out`. -/
theorem addS_ok {st o : BitVec 32} {s : State} (hc : Ctx st s) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (harg : s.mem.readW (addr (s.gpr .esp) 16) 32 = o)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s.wr) (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) :
    WP isa (.block addS) s fun s' => (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem ∧
      ∀ i < 4, wv s'.mem o (4 * i) = (ta s.mem st i + cs (ta s.mem st) i) % 2 ^ 32 := by
  refine wp_movm (a := addr (s.gpr .esp) 16) (ea_at _ _ _) hin fun s₁ u₁ _ => ?_
  have c₁ : Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  have esi : s₁.gpr .esi = o := by rw [u₁.gpr, harg]
  have ind : ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s₁ (TagInv st o s₁ n) := by
    intro n hn
    induction n with
    | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [hi]),
        fun h => absurd h (by decide)⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact WP.block_append (WP.mono (ih (by omega_using [hn])) fun s' h' =>
        tagWord_ok c₁ ho esi (by rw [u₁.wr]; exact hout) hd (by omega_using [hn]) h')
  refine WP.mono (ind 4 (Nat.le_refl _)) fun s₂ h₂ =>
    ⟨fun r h₁ h₂' => ?_, by rw [h₂.rd, u₁.rd], by rw [h₂.wr, u₁.wr], ?_, fun i hi => ?_⟩
  · rw [h₂.gpr r h₁, u₁.other r h₂']
  · rw [← u₁.mem]; exact h₂.frame
  · rw [h₂.out i hi, u₁.mem]

/-! ## Epilogue -/

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hL : TInv s₀ F s) :
    WP isa (.block (reduce ++ addS ++ restore)) s
      fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  have hfit := hp.st_fit
  have ho := hp.o_fit
  refine WP.block_append (WP.block_append (WP.mono (reduceFull_ok hL.ctx) fun s₁ ⟨S₁, h₁⟩ => ?_))
  have c₁ := hL.ctx.keep (S₁.gpr _ (by decide)) S₁.wr
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [S₁.gpr _ (by decide), hL.esp]
  have hf₁ : Frame [sR (stp s₀), oR s₀] s₀.mem s₁.mem := (hL.frame.trans S₁.frame).mono (by simp)
  refine WP.mono (addS_ok c₁ ho (by rw [esp₁]; exact hp.arg_same hf₁ (i := 3) (by decide))
    (by rw [S₁.rd, S₁.wr, hL.rd, hL.wr, esp₁]; exact hp.argIn (i := 3) (by decide))
    (by rw [S₁.wr, hL.wr]; exact hp.o_in) hp.st_o) fun s₂ ⟨g₂, rd₂, wr₂, f₂, o₂⟩ => ?_
  have c₂ : Ctx (stp s₀) s₂ := c₁.keep (g₂ _ (by decide) (by decide)) wr₂
  refine WP.mono (restore_ok c₂) fun s₃ ⟨b₃, si₃, di₃, bp₃, sp₃, A₃⟩ => ?_
  -- Words of the state that neither the reduction nor the tag changes.
  have hk : ∀ k < 32, k ∉ hS → words s₂.mem (stp s₀) k = words s.mem (stp s₀) k := by
    intro k hk h₁'
    rw [words_frame hfit hp.st_o f₂ hk]
    exact S₁.same k hk h₁'
  have hframe : Frame [sR (stp s₀), oR s₀] s₀.mem s₃.mem :=
    hf₁.trans ((f₂.mono (by simp)).trans (A₃.frame.mono (by simp)))
  refine ⟨abi_of hF.saved ?_ ?_ ?_ ?_ ?_ ?_, fun key msg hbuf hcnt => ?_⟩
  · rw [b₃, hk 29 (by decide) (by decide), hL.keep 29 (by decide) (by decide) (by decide)]
  · rw [si₃, hk 30 (by decide) (by decide), hL.keep 30 (by decide) (by decide) (by decide)]
  · rw [di₃, hk 31 (by decide) (by decide), hL.keep 31 (by decide) (by decide) (by decide)]
  · rw [bp₃, hk 5 (by decide) (by decide), hL.keep 5 (by decide) (by decide) (by decide)]
  · rw [sp₃, g₂ _ (by decide) (by decide), esp₁]
  · refine hframe.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hp.ret_st, hp.ret_o]
  · obtain ⟨W, rfl, hrep⟩ := buffered_split hfit hbuf hcnt
    have hA := A0_lt hrep
    obtain ⟨hcl, hac⟩ := repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hL.acc hA
    obtain ⟨hr, -⟩ := h₁ h4
    -- `h`, reduced.
    have hX : hw5 (words s₁.mem (stp s₀)) = accumulate (clamp (leNum (key.take 16))) (W ++ Bf s₀) := by
      rw [hr, hv, hcl, Poly1305.accumulate_append hrep.1, hac, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    -- `s`, words 10 to 13 of the state.
    have e : ∀ k < 4, words s₁.mem (stp s₀) (10 + k) = wv s₀.mem (stp s₀) (24 + 16 + 4 * k) := by
      intro k hk
      rw [show words s₁.mem (stp s₀) (10 + k) = wv s₁.mem (stp s₀) (4 * (10 + k)) from rfl,
        S₁.same _ (by omega_using [hk]) (not_hS (.inl ⟨by omega_using [hk], by omega_using [hk]⟩))]
      have := (hL.keep (10 + k) (by omega_using [hk]) (not_hS (.inl ⟨by omega_using [hk], by omega_using [hk]⟩)) (by omega_using [hk])).trans
        (hF.low (10 + k) (by omega_using [hk]) (by omega_using [hk]))
      simp only [words] at this
      rw [this, show 4 * (10 + k) = 24 + 16 + 4 * k by omega_using []]
    have hSk : leNum ((key.drop 16).take 16) = words s₁.mem (stp s₀) (10 + 0) +
        2 ^ 32 * words s₁.mem (stp s₀) (10 + 1) + 2 ^ 64 * words s₁.mem (stp s₀) (10 + 2) +
        2 ^ 96 * words s₁.mem (stp s₀) (10 + 3) := by
      rw [← hrep.2.1, show bytesAt s₀.mem ((stp s₀).setWidth 64 + 24) 32 =
          bytesAt s₀.mem ((stp s₀).setWidth 64 + 24) (16 + 16) from rfl, Poly1305.bytesAt_add,
        List.drop_left' (Poly1305.length_bytesAt _ _ _),
        List.take_of_length_le (by rw [Poly1305.length_bytesAt]), leNum_bytesAt_16,
        show (24 : Addr) = BitVec.ofNat 64 24 from rfl, add_ofNat_add, w32_off hfit (by decide),
        w32_off hfit (by decide), w32_off hfit (by decide), w32_off hfit (by decide), e 0 (by decide),
        e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    have hXm : hw5 (words s₁.mem (stp s₀)) % 2 ^ 128 = words s₁.mem (stp s₀) 0 +
        2 ^ 32 * words s₁.mem (stp s₀) 1 + 2 ^ 64 * words s₁.mem (stp s₀) 2 +
        2 ^ 96 * words s₁.mem (stp s₀) 3 := by
      have := words_lt s₁.mem (stp s₀) 0; have := words_lt s₁.mem (stp s₀) 1
      have := words_lt s₁.mem (stp s₀) 2; have := words_lt s₁.mem (stp s₀) 3
      simp only [hw5, val5]
      omega
    have hout : bytesAt s₃.mem ((op s₀).setWidth 64) 16 = bytesAt s₂.mem ((op s₀).setWidth 64) 16 :=
      Poly1305.bytesAt_frame A₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o.symm) (by decide)
    rw [hout]
    show bytesAt s₂.mem ((op s₀).setWidth 64) 16 = leBytes 16
      (accumulate (clamp (leNum (key.take 16))) (W ++ Bf s₀) + leNum ((key.drop 16).take 16))
    rw [← hX, hSk]
    refine bytesAt_leBytes_16w _ _ _ fun k hk => ?_
    rw [show w32 s₂.mem ((op s₀).setWidth 64) k = wv s₂.mem (op s₀) (4 * k) by
      simp only [w32, wv, wd]; rw [addr_eq (by omega_using [ho, hk])], o₂ k hk]
    exact tag_words (fun i => words s₁.mem (stp s₀) i) (fun i => words s₁.mem (stp s₀) (10 + i)) hXm hk

/-! ## The whole function -/

theorem finalize_eq : finalize = .seq (.block (setup ++ ([.mov .edx (.mem (at_ .esp 8)),
    .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)] : List Instr)))
    (.seq (.ite .e (.block []) lastBlock) (.block (reduce ++ addS ++ restore))) := rfl

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  rw [finalize_eq]
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ ⟨F, hF, h₁, hedx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := TInv s₀ F) ?_ fun s₂ h₂ => fepilogue_ok hp hF h₂)
  refine WP.ite (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) (by simp [eval, hz])
    (fun h => ?_) (fun h => ?_)
  · rw [BitVec.and_self, ofNat32_beq_zero (by have := kb_lt s₀; omega_using [this])] at h
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨h₁.toUCommon, by rw [Bf_nil h]; exact h₁.acc⟩
  · rw [BitVec.and_self, ofNat32_beq_zero (by have := kb_lt s₀; omega_using [this])] at h
    simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp hF h₁ hedx (by omega_using [h])

/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public. -/
def finalizeτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem finalize_wf₀ {s : State} (hp : FPre s) : VG.X86.Taint.Wf finalizeτ₀ s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [finalizeτ₀]; omega_using [hs], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_st hp.arg_st
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_o hp.arg_o
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_sc hp.arg_sc

theorem finalize_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeX86.pre s₁)
    (h₂ : Proof.Poly1305.finalizeX86.pre s₂) (hpub : Proof.Poly1305.finalizeX86.pub s₁ s₂) :
    VG.X86.Taint.Agree finalizeτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := FPre.of _ h₁; have hp₂ := FPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, finalize_wf₀ hp₁, finalize_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi]))
      h4 hk⟩
  simp only [finalizeτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
  subst hr; exact hesp

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0x3000` at `0x4004`. -/
def finalizeSatMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def finalizeSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finalizeSatMem
  rd := [⟨0x4004, 20⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x3000, 128⟩]

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeX86.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.finalizeX86.post s s' :=
  finalize_correct (FPre.of s hs)

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeX86.pre Proof.Poly1305.finalizeX86.pub
    finalize :=
  VG.Taint.constantTime (A := taint) finalizeτ₀ (fun _ _ h₁ h₂ hp => finalize_agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- The per-target contract of `finalize` only needs the length of the
message modulo 16. -/
theorem finalize_verified :
    Verified X86.target Impl.Poly1305.X86.finalize (Spec.Poly1305.finalizeContract X86.abi) :=
  Verified.of_correct finalize_ok finalize_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
        intro key msg hb hc
        exact h key msg hb (Proof.Poly1305.X86.count_mod16 hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        have a0 : arg finalizeSat 0 = 0x1000 := by decide
        have a3 : arg finalizeSat 3 = 0x2000 := by decide
        have a4 : arg finalizeSat 4 = 0x3000 := by decide
        have e : argAddr finalizeSat 0 = 0x4004 := by decide
        have esp : finalizeSat.gpr .esp = 0x4000 := rfl
        sig_implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a3, a4, e, esp] using Proof.Poly1305.X86.finalizeSat }

end VG.Proof.Poly1305.X86
