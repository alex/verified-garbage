import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Common
import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20-Poly1305 on x86-64: the prologue

Untrusted: everything here is checked by Lean. Saving the registers, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Saving the registers -/

theorem saveMoves_eq : save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) =
    [.store (at_ .rdi 592) .rbx, .store (at_ .rdi 600) .rbp, .store (at_ .rdi 608) .r13,
     .store (at_ .rdi 616) .r14, .store (at_ .rdi 624) .r15,
     .mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
     .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] := rfl

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86_64.off_sep p hd he (by omega) (by omega) h) (by decide)

set_option simprocs false in
theorem saveMoves_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr))) s₀ fun s =>
      s.gpr .r15 = cx s₀ ∧ s.gpr .rbx = ad s₀ ∧ s.gpr .rbp = s₀.gpr .rdx ∧ s.gpr .r14 = dp s₀ ∧
      s.gpr .r13 = s₀.gpr .r8 ∧ (∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r14 → r ≠ .r13 →
        s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      Frame [sub s₀ 592 40] s₀.mem s.mem ∧ Saved s₀ s.mem := by
  have o0 := hp.in_ctx (a := 592) (w := 8) (by omega)
  have o1 := hp.in_ctx (a := 600) (w := 8) (by omega)
  have o2 := hp.in_ctx (a := 608) (w := 8) (by omega)
  have o3 := hp.in_ctx (a := 616) (w := 8) (by omega)
  have o4 := hp.in_ctx (a := 624) (w := 8) (by omega)
  simp only [off] at o0 o1 o2 o3 o4
  apply WP.of_runBlock
  rw [saveMoves_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.setReg, o0, o1, o2, o3, o4, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ h₅ => by simp [h₁, h₂, h₃, h₄, h₅],
    trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 592 ≤ d → d + 8 ≤ 632 → (sub s₀ 592 40).Contains (off (cx s₀) d) (64 / 8) :=
      fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 592 (Nat.le_refl _) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 600 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 608 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 616 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 624 (by omega) (by omega))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [off, Mem.readW_writeW_self64, readW64_off]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0
  else if k < 12 then m.readW (off c (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off c (32 + 4 * (k - 13))) 32

/-- The context may be read and written. -/
def CtxOk (c : Addr) (s : State) : Prop :=
  ∀ a w, a + w ≤ 1024 → InRegions (s.rd ++ s.wr) (off c a) w ∧ InRegions s.wr (off c a) w

set_option simprocs false in
theorem stW_ok {c : Addr} {k : Nat} (hk : k < 16) {s : State} (hr15 : s.gpr .r15 = c) (hc : CtxOk c s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off c (64 + 4 * k)) (wordOf s.mem c k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := (hc (64 + 4 * k) 4 (by omega)).2
  simp only [off] at o
  unfold stW stSrc wordOf
  split_ifs with h₁ h₂ h₃
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.store32, State.setReg32, State.setReg, hr15, o, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := (hc (4 * (k - 4)) 4 (by omega)).1
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.load32, State.store32, State.setReg32, State.setReg, hr15, o, i, ite_true,
      ite_false, Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.store32, State.setReg32, State.setReg, hr15, o, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := (hc (32 + 4 * (k - 13)) 4 (by omega)).1
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.load32, State.store32, State.setReg32, State.setReg, hr15, o, i, ite_true,
      ite_false, Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

theorem readW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  VG.Proof.ChaCha20.X86_64.readW_writeW_off m p v (Or.inl rfl) hd he h

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') {a : Nat}
    (ha : a + 4 ≤ 64) (hn : n ≤ 960) : m'.readW (off c a) 32 = m.readW (off c a) 32 := by
  refine hf.readW (r := ⟨off c a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  intro x h₁ h₂
  simp only [off_eq, Region.Contains] at h₁ h₂
  bv_omega

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') (hn : n ≤ 960)
    {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs <;> first | rfl | exact readW_frame_ctx hf (by omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hr15 : s.gpr .r15 = c)
    (hc : CtxOk c s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off c (64 + 4 * i)) 32 = wordOf s.mem c i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk c s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok (by omega) (by rw [g₁ _ (by decide), hr15]) hc₁) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · simp only [off_eq, Region.Contains]
        rw [show c + BitVec.ofNat 64 (64 + 4 * j) - (c + BitVec.ofNat 64 64) = BitVec.ofNat 64 (4 * j) by
          rw [BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
        omega
    · rw [m₂, wordOf_frame f₁ (by omega) (by omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW32_off _ _ _ (by omega) (by omega) (by omega)]
        exact w₁ i (by omega)

theorem consts_eq : ∀ i < 4, ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : List (BitVec 32)).getD i 0 =
    Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 40] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (64 + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ a, a + 4 ≤ 44 → m₁.readW (off (cx s₀) a) 32 = s₀.mem.readW (off (cx s₀) a) 32 := by
    intro a ha
    refine hf₁.readW (r := sub s₀ a 4) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact sub_disj s₀ (by omega) (by omega) (by omega)
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * i) = off (cx s₀) (64 + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc], hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by omega), off_eq]
  · rfl
  · rw [r₁ _ (by omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by omega), off_eq]
    congr 1
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The whole prologue -/

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rdx
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem B1_eq : save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128 =
    (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr)) ++ (initState ++ (ptr .rdi .r15 64 ++ ptr .rsi .r15 128)) := by
  simp only [List.append_assoc]

theorem B3_eq : anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128 =
    anchor .rsi 128 ++ (ptr .rdi .r15 448 ++ ptr .rsi .r15 128) := by
  simp only [List.append_assoc]

theorem prologue_eq : prologue =
    .seq (.block (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128))
    (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
    (.seq (.block (anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128))
    (.seq (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init) (.block (anchor .rdi 448))))) := rfl

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  rw [prologue_eq, B1_eq]
  -- The registers, the saved ones, the ChaCha20 state and the pointers.
  refine WP.seq (WP.block_append (WP.mono (saveMoves_ok hp)
    fun s₁ ⟨e15, ebx, ebp, e14, e13, g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_))
  have hc₁ : CtxOk (cx s₀) s₁ := fun a w h => by
    rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩
  refine WP.block_append (WP.mono (initState_ok (j := 16) (Nat.le_refl _) e15 hc₁)
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 64) (by omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by omega) s₃) fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ => ?_
  have r15₂ : s₂.gpr .r15 = cx s₀ := by rw [g₂ _ (by decide), e15]
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃ _ (by decide), r15₂]
  have rdi₄ : s₄.gpr .rdi = off (cx s₀) 64 := by rw [g₄ _ (by decide), e3, r15₂]
  have rsi₄ : s₄.gpr .rsi = off (cx s₀) 128 := by rw [e4, r15₃]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s₄.gpr r = s₁.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₄ r h₃, g₃ r h₂, g₂ r h₁]
  have rsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
    rw [gg _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have mm₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [mm₄]; exact stateAt_initState f₁ w₂
  -- The block for counter 0: the one-time key.
  refine WP.seq (block_call rdi₄ rsi₄ (sub_disj s₀ (by omega) (by omega) (by omega))
    (by rw [rsp₄]; exact hp.below8_sub (by omega)) (by rw [rsp₄]; exact hp.below8_sub (by omega))
    (covers_left _ (covers_sub hp wr₄' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨64, rfl, show 64 + 64 ≤ 1024 by omega⟩
      · exact ⟨128, rfl, show 128 + 256 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₄' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨128, rfl, show 128 + 256 ≤ 1024 by omega⟩))
    fun s₅ rd₅ wr₅ cs₅ f₅ rsi₅ blk₅ => ?_)
  rw [rsp₄] at f₅
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [cs₅ _ (by simp [calleeSaved]), rsp₄]
  -- The pointers for the Poly1305 state.
  rw [B3_eq]
  refine WP.seq (WP.block_append (WP.mono (anchor_ok .rsi (k := 128) (by omega) s₅)
    fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ => ?_))
  have r15₆ : s₆.gpr .r15 = cx s₀ := by rw [e6, rsi₅, off_sub]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by omega) s₆)
    fun s₇ ⟨e7, g₇, rd₇, wr₇, m₇⟩ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by omega) s₇) fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ => ?_
  have rdi₈ : s₈.gpr .rdi = off (cx s₀) 448 := by rw [g₈ _ (by decide), e7, r15₆]
  have rsi₈ : s₈.gpr .rsi = off (cx s₀) 128 := by rw [e8, g₇ _ (by decide), r15₆]
  have g₈' : ∀ r, r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₈.gpr r = s₅.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₈ r h₃, g₇ r h₂, g₆ r h₁]
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by rw [g₈' _ (by decide) (by decide) (by decide), rsp₅]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  have mm₈ : s₈.mem = s₅.mem := by rw [m₈, m₇, m₆]
  -- The Poly1305 state for the one-time key.
  refine WP.seq (init_call rdi₈ rsi₈ (sub_disj s₀ (by omega) (by omega) (by omega))
    (by rw [rsp₈]; exact hp.below8_sub (by omega)) (by rw [rsp₈]; exact hp.below8_sub (by omega))
    (covers_left _ (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨128, rfl, show 128 + 32 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    fun s₉ rd₉ wr₉ cs₉ f₉ rdi₉ repr₉ => ?_)
  rw [rsp₈] at f₉
  refine WP.mono (anchor_ok .rdi (k := 448) (by omega) s₉) fun s₁₀ ⟨e10, g₁₀, rd₁₀, wr₁₀, m₁₀⟩ => ?_
  -- The registers.
  have cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s₁₀.gpr r = s₁.gpr r := fun r hr h15 => by
    have h' : r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₀ r h15, cs₉ r hr, g₈' r h15 h'.2.1 h'.2.2, cs₅ r hr, gg r h'.1 h'.2.1 h'.2.2]
  -- The memory.
  have sub1 : ∀ {k n : Nat}, 64 ≤ k → k + n ≤ 1024 → Region.Sub (sub s₀ k n) (workR s₀) := by
    intro k n h₁ h₂ x hx
    simp only [off_eq, Region.Contains] at *
    bv_omega
  have fr : ∀ {k n : Nat} {m m' : Mem}, 64 ≤ k → k + n ≤ 1024 →
      Frame [sub s₀ k n, below (s₀.gpr .rsp) 8] m m' → Frame [workR s₀, stkR s₀] m m' :=
    fun h₁ h₂ hf => hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 h₁ h₂⟩
      · exact ⟨stkR s₀, by simp, below8_stk s₀⟩
  have ff : Frame [workR s₀, stkR s₀] s₀.mem s₁₀.mem := by
    rw [m₁₀]
    refine (f₁.sub fun r hr => ?_).trans ((f₂.sub fun r hr => ?_).trans (?_ : Frame _ s₂.mem s₉.mem))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 (k := 64) (n := 64) (by omega) (by omega)⟩
    · rw [← mm₄]; refine (fr (k := 128) (n := 256) (by omega) (by omega) f₅).trans ?_
      rw [← mm₈]; exact fr (k := 448) (n := 128) (by omega) (by omega) f₉
  have d_st : ∀ {k n : Nat}, 64 + 64 ≤ k → k + n ≤ 1024 → ∀ r ∈ [sub s₀ k n, below (s₀.gpr .rsp) 8],
      (⟨off (cx s₀) 64, 64⟩ : Region).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact (hp.below8_sub (by omega)).symm
  have d_sv : ∀ {k n : Nat}, k + n ≤ 592 → ∀ r ∈ [sub s₀ k n, below (s₀.gpr .rsp) 8],
      (sub s₀ 592 40).Disjoint r := by
    intro k n h₁ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact (hp.below8_sub (by omega)).symm
  have st₉ : stateAt s₉.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₉ (d_st (k := 448) (by omega) (by omega)), mm₈,
      stateAt_frame f₅ (d_st (k := 128) (by omega) (by omega)), st₄]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄'],
    by rw [wr₁₀, wr₉, wr₈'], ?_, ff.sub fun r hr => ?_⟩, ?_, ?_, ff, ?_, ?_⟩
  · rw [e10, rdi₉, off_sub]
  · rw [cs .r14 (by simp [calleeSaved]) (by decide), e14]
  · rw [cs .r13 (by simp [calleeSaved]) (by decide), e13]
  · rw [cs .r12 (by simp [calleeSaved]) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  · rw [g₁₀ _ (by decide), cs₉ _ (by simp [calleeSaved]), rsp₈]
  · rw [m₁₀]
    rw [mm₄] at f₅
    refine (((sv₁.frame f₂ ?_).frame f₅ (d_sv (k := 128) (n := 256) (by omega))).frame ?_
      (d_sv (k := 448) (n := 128) (by omega)))
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega)
    · rw [← mm₈]; exact f₉
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [cs .rbx (by simp [calleeSaved]) (by decide), ebx]
  · rw [cs .rbp (by simp [calleeSaved]) (by decide), ebp]
  · rw [m₁₀]
    have hk : bytesAt s₈.mem (off (cx s₀) 128) 32 = otk s₀ := by
      rw [mm₈, bytesAt_serialize _ _ (by omega), blk₅, st₄]; rfl
    rw [← hk]; exact repr₉
  · rw [m₁₀]; exact st₉

end VG.Proof.ChaCha20Poly1305.X86_64
