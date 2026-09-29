import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Contract
import VerifiedGarbage.Proof.Sha3.SqueezeFrom
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# The SHA-3 sponge on AArch64: `squeeze`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Squeeze`), inside the frame that
saves `x30` (`WP.frameReg`).
-/

namespace VG.Proof.Sha3.AArch64.Stream.Squeeze

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Stream
open VG.Proof.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF ofNat_beq_zero sub_beq_zero sub_ofNat writeW8_self writeW8_other div_mod_eq)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .x0
abbrev rate : Nat := (s₀.gpr .x1).toNat
abbrev pos₀ : Nat := (s₀.gpr .x2).toNat
abbrev outp : Addr := s₀.gpr .x3
abbrev outn : Nat := (s₀.gpr .x4).toNat
abbrev scrp : Addr := s₀.gpr .x5
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
abbrev CR : Region := ⟨scrp s₀, 640⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev KR : Region := ⟨s₀.sp - 16, 16⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (KR s₀).Disjoint (SR s₀)
  o : (KR s₀).Disjoint (OR s₀)
  c : (KR s₀).Disjoint (CR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeAArch64.pre s₀) : SPre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := Proof.Sha3.rate_bounds hp.rate_mem
  omega

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = stp s₀
  x20 : s.gpr .x20 = scrp s₀
  x21 : s.gpr .x21 = s₀.gpr .x1
  x22 : s.gpr .x22 = BitVec.ofNat 64 pos
  x23 : s.gpr .x23 = outp s₀ + BitVec.ofNat 64 i
  x24 : s.gpr .x24 = BitVec.ofNat 64 (outn s₀ - i)
  sp : s.sp = s₀.sp
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : Saved (scrp s₀) s₀.gpr s.mem
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  x23 := by rw [hg _ (by simp)]; exact h.x23
  x24 := by rw [hg _ (by simp)]; exact h.x24
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0 0 (pos₀ s₀)) := by
  unfold setup
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok fun k hk => ⟨CR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s ⟨hg, hrd, hwr, hsp, hf, hv⟩ => ?_
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_nil ?_
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf.mono (by simp), by rw [hm]; exact hv, ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg]; simp
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hsp]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun j hj => hf.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj

/-! ## One iteration -/

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.movz .x .x22 0 0]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  refine WP.seq (wp_movz fun s₁ u₁ => wp_nil ?_)
  have e200 : Region.Sub ⟨stp s₀, 200⟩ (SR s₀) := fun _ h => h
  have e512 : Region.Sub ⟨scrp s₀, 512⟩ (CR s₀) := Region.sub_prefix (by omega)
  refine permuteAt_ok (st := stp s₀) (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.x19])
    (by rw [u₁.other _ (by decide), hI.x20]) (hp.st_c.sub_right e512) ?_
    fun s' rd' wr' sp' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨CR s₀, by simp, 0, by simp, by simp⟩
  have cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₁.gpr r := cs'
  have hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨scrp s₀, 512⟩], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right e512
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, ?_, by rw [sp', u₁.sp, hI.sp], ?_, ?_, ?_,
    fun j hj => ?_⟩
  · rw [cs _ (by decide) (by decide), u₁.other _ (by decide), hI.x19]
  · rw [cs _ (by decide) (by decide), u₁.other _ (by decide), hI.x20]
  · rw [cs _ (by decide) (by decide), u₁.other _ (by decide), hI.x21]
  · rw [cs _ (by decide) (by decide), u₁.gpr]; rfl
  · rw [cs _ (by decide) (by decide), u₁.other _ (by decide), hI.x23]
  · rw [cs _ (by decide) (by decide), u₁.other _ (by decide), hI.x24]
  · have hfs : Frame [SR s₀, OR s₀, CR s₀] s₁.mem s'.mem := by
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨SR s₀, by simp, e200⟩
      · exact ⟨CR s₀, by simp, e512⟩
    rw [u₁.mem] at hfs
    exact hI.frame.trans hfs
  · exact Saved.permute (by rw [u₁.mem]; exact hI.saved) hp.st_c hf
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀)) (by have := hI.i_le; omega : j < outn s₀)) ?_
    rw [u₁.mem]; exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block [.add .x .x10 .x19 .x22, .ldrb .x9 .x10 0, .strb .x9 .x23 0, .addImm .x .x23 .x23 1,
      .addImm .x .x22 .x22 1, .subImm .x .x24 .x24 1]) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_ldrb (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.x19, hI.x22]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega) (by omega)⟩
    fun s₂ u₂ => ?_
  refine wp_strb (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.x23]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega) (by omega)⟩)
    fun s₃ g₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => wp_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x9 → r ≠ .x23 → r ≠ .x22 → r ≠ .x24 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega)]
  have hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by omega),
      BitVec.setWidth_eq, hb]
  have hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  refine ⟨by omega, by have := hI.hi; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide), hI.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide), hI.x20]
  · rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide), hI.x21]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x22, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x23, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x24, sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · refine hI.saved.frame hfw fun k hk r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.o_c.symm.sub_left (slot_sub (scrp s₀) hk)
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (by intro h'; apply e; bv_omega)]
      exact hI.out j (by omega)

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ k' pos', Inv s₀ (i + 1) k' pos' s' := by
  have ⟨hr0, _⟩ := hp.rate_pos
  unfold squeezeBody
  refine WP.seq (wp_sub fun s₁ u₁ => wp_nil ?_)
  have hI₁ := hI.congr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem u₁.rd u₁.wr u₁.sp
  have hz : eval (.zero .x .x9) s₁ = some (decide (pos = rate s₀)) := by
    rw [eval_zero, u₁.gpr, hI.x22, hI.x21,
      sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .x1).isLt; omega)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => WP.mono (store_ok hp hI₂ hlt hi) fun s' h => ⟨k', pos' + 1, h⟩)
  refine WP.ite (decide (pos = rate s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact wp_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega⟩

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ k < 6, s'.gpr (sv k) = s₀.gpr (sv k)) ∧ s'.sp = s₀.sp ∧ Proof.Sha3.squeezeAArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : SPre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block (Impl.Sha3.AArch64.mov .x0 .x22 :: restore)) s (Post s₀) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hpl := hI.pos_le
  refine wp_mov fun s₁ u₁ => ?_
  have hx0 : s₁.gpr .x0 = BitVec.ofNat 64 pos := by rw [u₁.gpr, hI.x22]
  refine WP.mono (restores_ok (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.x20])
    fun k hk => ⟨CR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr],
      contains_offset (by omega) (by omega)⟩)
    fun s' ⟨ax, sp, m, _, _, _, v⟩ => ⟨fun k hk => ?_, by rw [sp, u₁.sp, hI.sp], ?_, ?_, fun d => ?_⟩
  · rw [v k hk, u₁.mem]; exact hI.saved k hk
  · show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [m, u₁.mem]
    refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
    have hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr0 hr200 _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · rw [ax, hx0, toNat_ofNat_lt (by omega)]; exact hI.pos_le
  · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .x0).toNat d =
      Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [m, u₁.mem, hI.state, ax, hx0, toNat_ofNat_lt (by have := hI.pos_le; omega),
      squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

/-- No instruction of `squeezeMain` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs squeezeMain, dstOf i ≠ some r := by
  have : ((instrs squeezeMain).all fun i => untouched.all fun r => dstOf i != some r) = true :=
    instrs_keeps (by decide +kernel)
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem squeeze_eq : squeezeMain = .seq (.block setup)
    (.seq (.ite (.zero .x .x24) (.block []) (.loop squeezeBody (.nonzero .x .x24)))
      (.block (Impl.Sha3.AArch64.mov .x0 .x22 :: restore))) := rfl

/-- `squeeze` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain {s₀ : State} (hp : SPre s₀) :
    WP isa squeezeMain s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Sha3.squeezeAArch64.post s₀ s' := by
  have hn := outn_lt s₀
  refine WP.mono (WP.gprs (Q := Post s₀) ?_ untouched_ok) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨fun r hr h30 => ?_, hsp, hpost⟩
  · rw [squeeze_eq]
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
    refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
      fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
    refine WP.ite (decide (outn s₀ = 0))
      (by show VG.AArch64.eval (.zero .x .x24) s₁ = _
          rw [eval_zero, hI.x24, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact wp_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s)
        ?_ (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega, by omega, hI⟩
      rintro n s ⟨i, k, pos, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hI hi) fun s' ⟨k', pos', hI'⟩ => ?_
      have hz : isa.eval (.nonzero .x .x24) s' = some (decide (outn s₀ - (i + 1) ≠ 0)) := by
        show VG.AArch64.eval (.nonzero .x .x24) s' = _
        rw [eval_nonzero, hI'.x24, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases hl : outn s₀ - (i + 1) = 0
      · exact .inl ⟨by rw [hz]; simp [hl], k', pos', by rwa [show i + 1 = outn s₀ by omega] at hI'⟩
      · exact .inr ⟨by rw [hz]; simp [hl], _, by omega, i + 1, k', pos', rfl, by omega, hI'⟩
  · rcases preserved_cases r hr h30 with ⟨k, hk, rfl⟩ | hu'
    · exact hsv k hk
    · exact hu r hu'

/-- The state `squeezeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {s₀ : State} (hp : SPre s₀) (hs : Stack s₀) :
    WP isa squeeze s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.squeezeAArch64.post s₀ s' := by
  have hpi : SPre (inner s₀) := ⟨hp.rd, hp.wr, hp.st_o, hp.st_c, hp.o_c, hp.rate_mem, hp.pos_le⟩
  have e : stateAt (inner s₀).mem (stp s₀) = stateAt s₀.mem (stp s₀) := write_frame_state hs.st
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.st
    · exact hs.o
    · exact hs.c
  · obtain ⟨h1, h2, h3⟩ := hpost
    refine ⟨⟨fun r hr => ?_, rfl⟩, ?_, h2, fun d => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have := h1
      rw [show stateAt (inner s₀).mem (inner s₀ |>.gpr .x0) = stateAt s₀.mem (stp s₀) from e] at this
      exact this
    · have := h3 d
      rw [show stateAt (inner s₀).mem (inner s₀ |>.gpr .x0) = stateAt s₀.mem (stp s₀) from e] at this
      exact this

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha3.squeezeAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 72 | .x3 => 0x2000 | .x4 => 16 | .x5 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 16⟩, ⟨0x3000, 640⟩]

theorem squeeze_verified : Verified AArch64.target squeeze Proof.Sha3.squeezeAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha3.AArch64.Stream.Squeeze
