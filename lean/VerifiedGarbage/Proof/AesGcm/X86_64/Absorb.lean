import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM on x86-64: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`rbp` bytes at `r12` into GHASH, with the accumulator at `St + yo` and the
`rbx` buffered bytes at `St + 32` (`absorb_ok`): it fills the buffer
(`head_ok`), absorbs whole blocks (`whole_ok`) and buffers the rest
(`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (St W SP : Addr) (yo : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨St + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r12`, `rbp`, `rbx` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)
  data : DataOk St W SP s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x : List Byte) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  r12 : s.gpr .r12 = D + BitVec.ofNat 64 j
  rbp : s.gpr .rbp = BitVec.ofNat 64 (n - j)
  data : DataOk St W SP s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H (x ++ bytesAt m₀ D j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame St W SP yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame St W SP yo) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk St W SP s D n) :
    ∀ r ∈ absFrame St W SP yo, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame St W SP yo, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame St W SP yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP 8] m m') : Frame (absFrame St W SP yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer. -/
theorem head_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn Ctx St W SP yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead v.callees yo) s
      (AbsMid Ctx St W SP yo H x D n s.mem (min (16 - x.length % 16) n)) := by
  have hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.rbx h.rbp (by omega) hn') fun s₁ ⟨hcx, hg, hm, hrd, hwr⟩ => ?_)
  generalize hk : min (16 - x.length % 16) n = k at hcx ⊢
  have hk1 : 1 ≤ k := by omega
  have hk16 : x.length % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rdi (.reg .r14),
      .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm 32), .mov .rsi (.reg .r12)] s₁ = some s₂ ∧
      s₂.gpr .rdi = St + BitVec.ofNat 64 (32 + x.length % 16) ∧ s₂.gpr .rsi = D ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg _ (by decide : Reg.r14 ≠ .rcx), hg _ (by decide : Reg.rbx ≠ .rcx), he.r14, h.rbx,
        add_ofNat_assoc, Nat.add_comm]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg _ (by decide : Reg.r12 ≠ .rcx), h.r12]
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have lp : LoopPre s₂ D (St + BitVec.ofNat 64 (32 + x.length % 16)) k := by
    refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], hk1, by omega, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂, hrd, hwr]; exact (h.data.take hkn).rd
    · rw [hwr₂, hwr]; exact he.perm.stC (by omega)
    · exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
  have hreg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₃.gpr r = s.gpr r :=
    fun r a b c d e => by rw [hg₃ r a b, hg₂ r c d, hg r e]
  have h3rcx : s₃.gpr .rcx = BitVec.ofNat 64 k := by
    rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide), hcx]
  rw [hm₂, hm] at hm₃
  rw [hrd₂, hrd] at hrd₃
  rw [hwr₂, hwr] at hwr₃
  -- The bytes copied, and the buffer.
  have hdk := length_bytesAt s.mem D k
  have hB : bytesAt s₃.mem (St + BitVec.ofNat 64 32) (x.length % 16 + k) =
      bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ bytesAt s.mem D k := by
    rw [hm₃, show St + BitVec.ofNat 64 (32 + x.length % 16) =
        St + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (St + BitVec.ofNat 64 32) (x.length % 16) (bytesAt s.mem D k)
      (by rw [hdk]; omega)
    rwa [hdk] at this
  have fw : Frame [⟨St + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hdk
  have hY : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
    blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)
  have hH3 : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), h.hH]
  -- The block after the copy.
  obtain ⟨s₄, run₄, h12, hbp, hbx, hzf, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx), .alu .add .rbx (.reg .rcx),
        .alu .cmp .rbx (imm 16)] s₃ = some s₄ ∧
      s₄.gpr .r12 = D + BitVec.ofNat 64 k ∧ s₄.gpr .rbp = BitVec.ofNat 64 (n - k) ∧
      s₄.gpr .rbx = BitVec.ofNat 64 (x.length % 16 + k) ∧
      s₄.zf = some (decide (x.length % 16 + k = 16)) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have e12 := hreg .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebp := hreg .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebx := hreg .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e12, h3rcx, h.r12]
    · simp [gpr_setReg, ebp, h3rcx, h.rbp, ofNat_sub hkn hn']
    · simp [gpr_setReg, ebx, h3rcx, h.rbx, ofNat_add_ofNat]
    · simp only [zf_arithFlags, ebx, h3rcx, h.rbx, ofNat_add_ofNat]
      rw [sub_beq (by omega) (by decide)]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide) (by decide),
        hreg _ (by decide) (by decide) (by decide) (by decide) (by decide)]) (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  have hd₄ : DataOk St W SP s₄ D n := h.data.of_eq (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    have h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_ok v L hyo he₄ .r14 32 (.inl rfl) (P := St + BitVec.ofNat 64 32) (by rw [he₄.r14])
      (by decide) (L.st_st (.inl (by omega)) (by omega) (by decide)) (L.st_w (by decide) (.inr ⟨by decide, by decide⟩))
      (L.stk_st (by decide)) (covers_left (he₄.perm.stC (by decide)))) fun s₅ g => ?_
    refine ⟨g.env he₄, hkn, by rw [g.saved _ (by decide)]; exact h12, by rw [g.saved _ (by decide)]; exact hbp,
      hd₄.of_eq g.rd g.wr, ?_, ?_, .inr (by omega), ?_⟩
    · rw [blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm, hm₄, hH3]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16) (B := bytesAt s₃.mem (St + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, hB, ha.2]
      · rw [g.out, hm₄, hY, hH3]; rfl
    · have f₁ : Frame (absFrame St W SP yo) s.mem s₃.mem := buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16
      have f₂ : Frame (absFrame St W SP yo) s₄.mem s₅.mem := gh_absFrame g.frame
      rw [← hm₄] at f₁; exact f₁.trans f₂
  · -- Not full: the data is used up.
    have h16 : x.length % 16 + k < 16 := by simp at hf; omega
    have hkn' : k = n := by omega
    refine WP.block_nil ⟨he₄, hkn, h12, hbp, hd₄, by rw [hm₄]; exact hH3, fun ha => ?_, .inl (by omega),
      by rw [hm₄]; exact buf_absFrame (yo := yo) (W := W) (SP := SP) fw hk16⟩
    rw [hm₄]
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) hY (by rw [hdk]; exact hB)

omit L hyo in
/-- The whole blocks split off: `p` and `k` hold them, `r12` and `rbp` the rest. -/
theorem wholeSplit_ok (p k : Reg) (hpk : (p = .rdx ∧ k = .rcx) ∨ (p = .rcx ∧ k = .r8)) {D : Addr} {n j : Nat}
    {s : State} (hn' : n < 2 ^ 64) (hj : j ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (h13 : s.gpr .rbp = BitVec.ofNat 64 (n - j)) :
    ∃ s₁, runBlock isa (splitWhole p k ++ ([.alu .test k (.reg k)] : List Instr)) s = some s₁ ∧
      s₁.gpr p = D + BitVec.ofNat 64 j ∧ s₁.gpr k = BitVec.ofNat 64 ((n - j) / 16) ∧
      s₁.gpr .r12 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      s₁.zf = some (decide ((n - j) / 16 = 0)) ∧
      (∀ r, r ≠ p → r ≠ k → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  have hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat_ofNat_of_lt (by omega), imm_eq (by decide)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) = BitVec.ofNat 64 (16 * nb) := by
    rw [ofNat_sub (Nat.mod_le _ _) (by omega)]; congr 1; omega
  rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨_, by simp only [splitWhole]; xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_setFlags, h12]
    · simp [gpr_setReg, gpr_setFlags, h13, shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12, h13,
        hand, hsub, BitVec.add_assoc, ofNat_add_ofNat]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h13, hand]
      congr 1
      omega
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq,
        h13, shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
      rw [and_self_beq (by omega)]
    · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄, h₅]
    all_goals rfl

/-- The whole blocks. -/
theorem whole_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid Ctx St W SP yo H x D n m₀ j s) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa (absorbWhole v.callees yo) s
      (AbsMid Ctx St W SP yo H x D n m₀ (j + 16 * ((n - j) / 16))) := by
  have hn' := h.data.lt
  have he := h.env
  obtain ⟨s₁, run₁, hdx, hcx, h12, hbp, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := wholeSplit_ok .rdx .rcx (.inl ⟨rfl, rfl⟩) hn' h.le h.r12 h.rbp
  generalize hnb : (n - j) / 16 = nb at *
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hrd₁ hwr₁
  have hd₁ : DataOk St W SP s₁ D n := h.data.of_eq hrd₁ hwr₁
  refine WP.ite (decide (nb = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    simp only [Nat.mul_zero, Nat.add_zero]
    refine WP.block_nil ⟨he₁, h.le, by rw [h12]; rfl, by rw [hbp]; rfl, hd₁, by rw [hm₁]; exact h.hH,
      fun ha => by rw [hm₁]; exact h.abs ha, h.whole, by rw [hm₁]; exact h.frame⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := (h.data.drop h.le).take (k := 16 * nb) h16
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hdi, hsi, h8, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO) s₁ = some s₂ ∧
        s₂.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 yo ∧
        s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h15]
      · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    refine WP.mono (ghCall_ok v L hyo he₂ (P := D + BitVec.ofNat 64 j) (n := nb) hdi hsi
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hdx])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), hcx]) h8 (by have := hdj.lt; omega)
      (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
      (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hdj.rd)) fun s₃ g => ?_
    have hg₃ : ∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 →
        r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r a b c d e f g' i hr => by
      rw [g.saved r hr, hg₂ r f g' i, hg₁ r a b c d e]
    refine ⟨g.env he₂, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hrd₂) (g.wr.trans hwr₂), ?_, ?_,
      .inr (by omega), ?_⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h12]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), hbp]
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hm₂, hm₁]; exact h.hH
    · intro ha
      have ex : x ++ bytesAt m₀ D (j + 16 * nb) = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega) (by simp [length_bytesAt]) ?_
      rw [g.out, hm₂, hm₁, h.hH, Proof.Gcm.blocksAt_eq]
      congr 2
      -- The data is as in `m₀`.
      have e₁ := congrArg (fun l => l.drop j) hm₀
      have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      have e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      have e₄ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hm₂, hm₁] at this; exact h.frame.trans (gh_absFrame this)

/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid Ctx St W SP yo H x D n m₀ j s) (hj : n - j < 16) (hm₀ : bytesAt s.mem D n = bytesAt m₀ D n) :
    WP isa absorbTail s (AbsOut Ctx St W SP yo H x (x ++ bytesAt m₀ D n) m₀) := by
  have hn' := h.data.lt
  have he := h.env
  obtain ⟨s₁, run₁, hcx, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rcx (.reg .rbp), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n - j) ∧ s₁.zf = some (decide (n - j = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.rbp]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, h.rbp]; rw [and_self_beq (by omega)]
    · intro r h₁; simp [gpr_setReg, h₁]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, fun ha => by rw [hm₁]; exact h.abs ha, by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.drop h.le
    have h14 := he₁.r14
    obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (ptr .rdi .r14 32 ++ [.mov .rsi (.reg .r12)]) s₁ = some s₂ ∧
        s₂.gpr .rdi = St + BitVec.ofNat 64 32 ∧ s₂.gpr .rsi = D + BitVec.ofNat 64 j ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁ _ (by decide : Reg.r12 ≠ .rcx), h.r12]
      · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have lp : LoopPre s₂ (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 32) (n - j) := by
      refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], by omega, by omega, ?_, ?_, ?_⟩
      · rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hdj.rd
      · rw [hwr₂, hwr₁]; exact he.perm.stC (by omega)
      · exact hdj.st.sub_right (Lay.stSub (by omega))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
    rw [hm₂, hm₁] at hm₃
    have hlen := length_bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨St + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide)]) (hrd₃.trans hrd₂) (hwr₃.trans hwr₂),
      ?_, ?_⟩
    · intro ha
      have ex : x ++ bytesAt m₀ D n = (x ++ bytesAt m₀ D j) ++ bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
      have ed : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
        have e₁ := congrArg (fun l => l.drop j) hm₀
        have e₂ : ∀ m : Mem, (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := fun m => by
          rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega)) (by omega) (by omega)]
      · rw [hm₃]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

omit L hyo in
theorem AbsIn.keep {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s s' : State}
    (h : AbsIn Ctx St W SP yo H x D n s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : AbsIn Ctx St W SP yo H x D n s' where
  env := h.env.keep (fun r _ => by rw [hg]) hrd hwr
  r12 := by rw [hg]; exact h.r12
  rbp := by rw [hg]; exact h.rbp
  rbx := by rw [hg]; exact h.rbx
  data := h.data.of_eq hrd hwr
  hH := by rw [hm]; exact h.hH

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid Ctx St W SP yo H x D n m₀ j s) : bytesAt s.mem D n = bytesAt m₀ D n :=
  bytesAt_frame h.frame (data_absFrame hyo h.data) (by have := h.data.lt; omega)

/-- `absorb yo`. -/
theorem absorb_ok {H : Block} {x : List Byte} {D : Addr} {n : Nat} {s : State}
    (h : AbsIn Ctx St W SP yo H x D n s) :
    WP isa (absorb v.callees yo) s (AbsOut Ctx St W SP yo H x (x ++ bytesAt s.mem D n) s.mem) := by
  have hn' := h.data.lt
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp hn'
  have h₁ := h.keep hg₁ hm₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    obtain ⟨s₂, run₂, hzf₂, hg₂, hm₂, hrd₂, hwr₂⟩ := test_ok s₁ .rbx h₁.rbx
      (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
    have h₂ := h₁.keep hg₂ hm₂ hrd₂ hwr₂
    have hm₀ : s₂.mem = s.mem := hm₂.trans hm₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (Q := fun s' => ∃ j, AbsMid Ctx St W SP yo H x D n s.mem j s')
      (WP.ite (decide (x.length % 16 = 0)) (eval_e hzf₂) (fun ht => ?_) (fun hf => ?_)) fun s' hj => ?_)
    · have ho : x.length % 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨0, h₂.env, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data, h₂.hH,
        fun ha => by rw [hm₀]; simpa [bytesAt] using ha, .inr (by omega), by rw [← hm₀]; exact Frame.refl _ _⟩
    · have := head_ok v L hyo h₂ h0 (by simpa using hf)
      rw [hm₀] at this; exact WP.mono this fun _ h => ⟨_, h⟩
    · obtain ⟨j, hj⟩ := hj
      refine WP.seq (WP.mono (whole_ok v L hyo hj (hj.data_eq hyo)) fun s'' hj' => ?_)
      exact tail_ok L hyo hj' (by have := hj.le; omega) (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.X86_64