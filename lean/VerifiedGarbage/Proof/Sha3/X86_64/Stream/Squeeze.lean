import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# The SHA-3 sponge on x86-64: `squeeze`
-/

namespace VG.Proof.Sha3.X86_64.Stream.Squeeze

open VG VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Impl.Sha3.X86_64.Stream (squeeze squeezeBody squeezeWord squeezeByte wordTest permuteAt save restore stByte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .rdi
abbrev rate : Nat := (s₀.gpr .rsi).toNat
abbrev pos₀ : Nat := (s₀.gpr .rdx).toNat
abbrev outp : Addr := s₀.gpr .rcx
abbrev outn : Nat := (s₀.gpr .r8).toNat
abbrev scrp : Addr := s₀.gpr .r9
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
abbrev CR : Region := ⟨scrp s₀, 640⟩
abbrev RR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of `vg_keccak_f1600` stores its return address. -/
abbrev KR : Region := below (s₀.gpr .rsp) 8
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

theorem saved_bound : ∀ p ∈ Impl.Sha3.X86_64.Stream.saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (scrp s₀) s₀.gpr Impl.Sha3.X86_64.Stream.saved

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  ret_st : (RR s₀).Disjoint (SR s₀)
  ret_o : (RR s₀).Disjoint (OR s₀)
  ret_c : (RR s₀).Disjoint (CR s₀)
  stk_st : (KR s₀).Disjoint (SR s₀)
  stk_o : (KR s₀).Disjoint (OR s₀)
  stk_c : (KR s₀).Disjoint (CR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeX86_64.pre s₀) : SPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := hp.rate_mem
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt

theorem ret_stk (s₀ : State) : (RR s₀).Disjoint (KR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-- The saved registers lie in the scratch space, past the permutation's. -/
theorem slot_sub (s₀ : State) {p : Reg × Nat} (hp : p ∈ Impl.Sha3.X86_64.Stream.saved) :
    Region.Sub ⟨Spill.slot (scrp s₀) p.2, 8⟩ (CR s₀) := by
  have := saved_bound p hp; exact sub_offset (by omega) (by omega)

theorem slot_scr (s₀ : State) {p : Reg × Nat} (hp : p ∈ Impl.Sha3.X86_64.Stream.saved) :
    Region.Disjoint ⟨Spill.slot (scrp s₀) p.2, 8⟩ ⟨scrp s₀, 512⟩ := by
  have := saved_bound p hp; exact Offset.disjoint_base _ (by omega) (by omega)

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ p ∈ Impl.Sha3.X86_64.Stream.saved, ∀ r ∈ rs, Region.Disjoint ⟨Spill.slot (scrp s₀) p.2, 8⟩ r) : Saved s₀ m' :=
  Spill.Saved.frame h hf hd

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-! ## The prologue -/

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = stp s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = BitVec.ofNat 64 pos
  r13 : s.gpr .r13 = outp s₀ + BitVec.ofNat 64 i
  r14 : s.gpr .r14 = BitVec.ofNat 64 (outn s₀ - i)
  r15 : s.gpr .r15 = scrp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [SR s₀, OR s₀, CR s₀, KR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r13 := by rw [hg _ (by simp)]; exact h.r13
  r14 := by rw [hg _ (by simp)]; exact h.r14
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr))) s₀
      fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.zf = some (decide (outn s₀ = 0)) := by
  refine WP.block_append_iff.mpr (WP.mono (Spill.save_ok .r9 Impl.Sha3.X86_64.Stream.saved s₀ fun p hp' => ?_)
    fun s ⟨hg, hrd, hwr, hm₀⟩ => ?_)
  · have := saved_bound p hp'
    rw [hp.wr]; exact ⟨CR s₀, by simp, contains_offset (by omega) (by omega)⟩
  have hf : Frame [CR s₀] s₀.mem s.mem := hm₀ ▸ Spill.saveMem_frame_base _ _ _ _
    (fun p hp => by have := saved_bound p hp; omega) (by decide)
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => wp_nil ?_
  have hm : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h14 : s₇.gpr .r14 = s₀.gpr .r8 := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hg]
  refine ⟨⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf.mono (by simp), by rw [hm, hm₀]; exact Spill.saveMem_saved _ _ _ _ (by decide), ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩, ?_⟩
  · rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  · rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [h14]; simp
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]
  · rw [hm]
    exact VG.Proof.Sha3.stateAt_congr fun j hj => hf.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj
  · rw [z₇, ← g₇, h14, BitVec.and_self, beq_zero]

/-! ## One iteration -/

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  refine WP.seq (wp_mov32i fun s₁ u₁ => wp_nil ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [u₁.other _ (by decide), hI.rsp]
  have e200 : Region.Sub ⟨stp s₀, 200⟩ (SR s₀) := fun _ h => h
  have e512 : Region.Sub ⟨scrp s₀, 512⟩ (CR s₀) := sub_prefix' (by omega)
  refine permuteAt_ok (st := stp s₀) (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.rbx])
    (by rw [u₁.other _ (by decide), hI.r15]) (hp.st_c.sub_right e512) (by rw [hsp]; exact hp.stk_st)
    (by rw [hsp]; exact hp.stk_c.sub_right e512) ?_ fun s' rd' wr' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨CR s₀, by simp, 0, by simp, by simp⟩
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r := cs'
  have hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨scrp s₀, 512⟩, below (s₁.gpr .rsp) 8], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right e512
    · rw [hsp]; exact hp.stk_o.symm
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.rbx]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.rbp]
  · rw [cs _ (by decide), u₁.gpr]; rfl
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r13]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r14]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r15]
  · rw [cs _ (by decide), hsp]
  · have hfs : Frame [SR s₀, OR s₀, CR s₀, KR s₀] s₁.mem s'.mem := by
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨SR s₀, by simp, e200⟩
      · exact ⟨CR s₀, by simp, e512⟩
      · exact ⟨KR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
    rw [u₁.mem] at hfs
    exact hI.frame.trans hfs
  · refine Saved.frame (by rw [u₁.mem]; exact hI.saved) hf fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_c.symm.sub_left (slot_sub s₀ hk)
    · exact slot_scr s₀ hk
    · rw [hsp]; exact hp.stk_c.symm.sub_left (slot_sub s₀ hk)
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀)) (by have := hI.i_le; omega : j < outn s₀)) ?_
    rw [u₁.mem]; exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s fun s' =>
      Inv s₀ (i + 1) k (pos + 1) s' ∧ s'.zf = some (decide (outn s₀ - (i + 1) = 0)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  unfold squeezeByte
  refine wp_movzx8 (a := stp s₀ + BitVec.ofNat 64 pos) (by simp [State.ea, stByte, hI.rbx, hI.r12])
    ⟨SR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_store8 (a := outp s₀ + BitVec.ofNat 64 i) (by simp [State.ea, u₁.other .r13 (by decide), hI.r13])
    (by rw [u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega) (by omega)⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => wp_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1]
  have hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega)]
  have hm : s₅.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by omega),
      BitVec.setWidth_eq, hb]
  have hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have h14 : s₅.gpr .r14 = BitVec.ofNat 64 (outn s₀ - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx1,
      ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, by have := hI.hi; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, hI.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hI.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r12, sx1,
      ofNat_succ]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hI.r13, sx1,
      ofNat_succ, BitVec.add_assoc]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · refine hI.saved.frame hfw fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.o_c.symm.sub_left (slot_sub s₀ hk)
  · rw [VG.Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega) (by omega) e)]
      exact hI.out j (by omega)
  · rw [hz₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx1,
      ofNat_pred (by omega), beq_zero, toNat_ofNat_lt (by omega), Nat.sub_sub]

theorem storeW_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos + 8 ≤ rate s₀) (hi : i + 8 ≤ outn s₀) :
    WP isa (.block squeezeWord) s fun s' =>
      Inv s₀ (i + 8) k (pos + 8) s' ∧ s'.zf = some (decide (outn s₀ - (i + 8) = 0)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  unfold squeezeWord
  refine wp_movm (a := stp s₀ + BitVec.ofNat 64 pos) (by simp [State.ea, stByte, hI.rbx, hI.r12])
    ⟨SR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_store (a := outp s₀ + BitVec.ofNat 64 i) (by simp [State.ea, u₁.other .r13 (by decide), hI.r13])
    (by rw [u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega) (by omega)⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => wp_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1]
  have hm : s₅.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (s.mem.readW (stp s₀ + BitVec.ofNat 64 pos) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem]
  have hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have h14 : s₅.gpr .r14 = BitVec.ofNat 64 (outn s₀ - (i + 8)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx8,
      sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, by have := hI.hi; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, hI.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hI.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r12, sx8,
      ← BitVec.ofNat_add]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hI.r13, sx8,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · refine hI.saved.frame hfw fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.o_c.symm.sub_left (slot_sub s₀ hk)
  · rw [VG.Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : i ≤ j
    · rw [show outp s₀ + BitVec.ofNat 64 j = outp s₀ + BitVec.ofNat 64 i + BitVec.ofNat 64 (j - i) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' e],
        writeW64_byte _ _ _ (by omega), Mem.readW, BitVec.setWidth_eq,
        Mem.extractLsb'_read s.mem (stp s₀ + BitVec.ofNat 64 pos) (n := 64 / 8) (show j - i < 64 / 8 by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add,
        ← byteOf_stateAt s.mem (stp s₀) (show pos + (j - i) < 200 by omega), hI.state]
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 (show pos + (j - i) < rate s₀ by omega)
      rw [show pos₀ s₀ + j = rate s₀ * k + (pos + (j - i)) by have := hI.hi; omega, d, m]
    · rw [Mem.writeW, Mem.write_apply (by
        rw [Offset.sub_toNat' _ (by omega) (by omega), ite_eq_right_of_eq_false _ _ (eq_false e)]
        omega)]
      exact hI.out j (by omega)
  · rw [hz₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hI.r14, sx8,
      sub_ofNat (by omega), beq_zero, toNat_ofNat_lt (by omega), Nat.sub_sub]

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ i' k' pos', i < i' ∧ i' ≤ outn s₀ ∧ Inv s₀ i' k' pos' s' ∧
      s'.zf = some (decide (outn s₀ - i' = 0)) := by
  have ⟨hr0, _⟩ := hp.rate_pos
  have h8 := rate_mod8 hp.rate_mem
  unfold squeezeBody
  refine WP.seq (wp_cmp fun s₁ g₁ m₁ rd₁ wr₁ _ z₁ => wp_nil ?_)
  have hI₁ := hI.congr (fun r _ => by rw [g₁]) m₁ rd₁ wr₁
  have hz : s₁.zf = some (decide (pos = rate s₀)) := by
    rw [z₁, hI.r12, hI.rbp, sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .rsi).isLt; omega)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => ?_)
  · refine WP.ite (decide (pos = rate s₀)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact wp_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega⟩
  -- a lane or a byte
  refine WP.seq (WP.mono (wordTest_ok hI₂.r12 hI₂.r14 (by have := outn_lt s₀; omega))
    fun s₃ ⟨g₃, m₃, rd₃, wr₃, b, z₃, hb₃⟩ => ?_)
  have hI₃ := hI₂.congr (fun r hr => g₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) m₃ rd₃ wr₃
  refine WP.ite b (by rw [show isa.eval .e s₃ = s₃.zf from rfl, z₃]) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hb₃ hb
    exact WP.mono (storeW_ok hp hI₃ (by omega) (by omega))
      fun s' ⟨h, hz⟩ => ⟨i + 8, k', pos' + 8, by omega, by omega, h, hz⟩
  · exact WP.mono (store_ok hp hI₃ hlt hi) fun s' ⟨h, hz⟩ => ⟨i + 1, k', pos' + 1, by omega, by omega, h, hz⟩

/-! ## The epilogue -/

theorem epilogue_ok {s₀ : State} (hp : SPre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block (.mov .rax (.reg .r12) :: restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.squeezeX86_64.post s₀ s' := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  refine wp_mov fun s₁ u₁ => ?_
  have hI₁ : Inv s₀ (outn s₀) k pos s₁ := hI.congr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem u₁.rd u₁.wr
  have hax : s₁.gpr .rax = BitVec.ofNat 64 pos := by rw [u₁.gpr, hI.r12]
  refine WP.mono (Spill.restore_ok .r15 Impl.Sha3.X86_64.Stream.saved s₀.gpr s₁ (by decide) (fun p hp' => ?_)
    (by rw [hI₁.r15]; exact hI₁.saved)) fun s' ⟨h₁, h₂, m, _⟩ => ?_
  · have := saved_bound p hp'
    rw [hI₁.r15]
    exact ⟨CR s₀, by simp [hI₁.rd, hI₁.wr, hp.rd, hp.wr], contains_offset (by omega) (by omega)⟩
  · have ax : s'.gpr .rax = s₁.gpr .rax := h₂ _ (by decide)
    have hpos : pos ≤ rate s₀ := hI.pos_le
    have hst : stateAt s'.mem (stp s₀) = iterF k (S₀ s₀) := by rw [m]; exact hI₁.state
    have hrax : (s'.gpr .rax).toNat = pos := by rw [ax, hax, toNat_ofNat_lt (by omega)]
    refine ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hI₁.rsp, ?_⟩, ?_, by rw [hrax]; exact hpos,
      fun d => ?_⟩
    · rw [m]
      exact hI₁.frame.readW (Region.contains_self _ _)
        (by simpa using ⟨hp.ret_st, hp.ret_o, hp.ret_c, ret_stk s₀⟩) (by decide)
    · show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
      rw [m]
      refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
      have hj : j < outn s₀ := by simpa [bytesAt] using h₁
      rw [squeezeFrom_getElem hr0 hr200 _ hj]
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      exact hI₁.out j hj
    · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .rax).toNat d =
        Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
      rw [hst, hrax, squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : SPre s₀) :
    WP isa squeeze s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.squeezeX86_64.post s₀ s' := by
  unfold squeeze
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact wp_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_
      (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega, by omega, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨i', k', pos', hii, hi', hI', hz'⟩ => ?_
    by_cases hl : outn s₀ - i' = 0
    · exact .inl ⟨by simp [eval, hz', hl], k', pos', by rwa [show i' = outn s₀ by omega] at hI'⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, i', k', pos', rfl, by omega, hI'⟩

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi`, `rcx`
and `r9` point at the writable regions (of which `out` has unknown length). -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [200, 0, 640],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0), (.r9, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeX86_64.pre s₁)
    (h₂ : Proof.Sha3.squeezeX86_64.pre s₂) (hpub : Proof.Sha3.squeezeX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  have wf : ∀ s, Proof.Sha3.squeezeX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3],
      by simpa [hw] using (Nat.le_of_lt (s.gpr .r8).isLt)⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 72 | .rcx => 0x2000 | .r8 => 16 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 16⟩, ⟨0x3000, 640⟩]

theorem squeeze_correct (s : State) (hs : Proof.Sha3.squeezeX86_64.pre s) :
    ∃ t s', Exec isa squeeze s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.squeezeX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezeX86_64.pre Proof.Sha3.squeezeX86_64.pub
    squeeze := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)

theorem squeeze_verified :
    Verified X86_64.target Impl.Sha3.X86_64.Stream.squeeze (Spec.Sha3.squeezeContract X86_64.abi 8) :=
  Verified.of_correct squeeze_correct squeeze_ct (by
    sig_implies [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Proof.Sha3.squeezeX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Sha3.X86_64.Stream.Squeeze.sat] using
      Proof.Sha3.X86_64.Stream.Squeeze.sat)

end VG.Proof.Sha3.X86_64.Stream.Squeeze
