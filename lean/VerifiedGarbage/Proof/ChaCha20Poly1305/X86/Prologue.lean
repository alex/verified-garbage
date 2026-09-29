import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Calls
import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the prologue

Untrusted: everything here is checked by Lean. Saving the registers, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
Each stage is stated separately (`Pro1`, …), for the constant-time proof.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt readW_writeW_off)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Loading the context and saving the registers -/

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4))]) s₀ fun s => s = s₀.setReg .eax (CX s₀) := by
  have i₀ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hp.in_arg (i := 0) (by omega)
  have v₀ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = CX s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₀, v₀, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- The memory after the registers are saved. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (cx s₀ + BitVec.ofNat 64 592) (s₀.gpr .ebx)).writeW (cx s₀ + BitVec.ofNat 64 596)
    (s₀.gpr .esi)).writeW (cx s₀ + BitVec.ofNat 64 600) (s₀.gpr .edi)).writeW
    (cx s₀ + BitVec.ofNat 64 604) (s₀.gpr .ebp)

theorem saveMem_frame (s₀ : State) : Frame [sub s₀ 592 16] s₀.mem (saveMem s₀) := by
  have c : ∀ d, 592 ≤ d → d + 4 ≤ 608 → (sub s₀ 592 16).Contains (cx s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 592 (Nat.le_refl _) (by omega))).writeW
    (List.mem_singleton_self _) _ (c 596 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (c 600 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (c 604 (by omega) (by omega))

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ [.mov .edi (.reg .eax)])) (s₀.setReg .eax (CX s₀)) fun s =>
      s.gpr .edi = CX s₀ ∧ (∀ r, r ≠ .eax → r ≠ .edi → s.gpr r = s₀.gpr r) ∧ s.mem = saveMem s₀ ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have e0 := hp.c64 (k := 592) (by omega); have e1 := hp.c64 (k := 596) (by omega)
  have e2 := hp.c64 (k := 600) (by omega); have e3 := hp.c64 (k := 604) (by omega)
  have o0 := hp.in_ctx (a := 592) (w := 4) (by omega)
  have o1 := hp.in_ctx (a := 596) (w := 4) (by omega)
  have o2 := hp.in_ctx (a := 600) (w := 4) (by omega)
  have o3 := hp.in_ctx (a := 604) (w := 4) (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save, saved, List.map, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.store32,
    State.setReg, e0, e1, e2, e3, o0, o1, o2, o3, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h₁ h₂ => by simp [h₁, h₂], rfl, trivial⟩

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0
  else if k < 12 then m.readW (c + BitVec.ofNat 64 (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (c + BitVec.ofNat 64 (32 + 4 * (k - 13))) 32

set_option simprocs false in
theorem stW_ok {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 16) {s : State}
    (hedi : s.gpr .edi = CX s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 (64 + 4 * k)) (wordOf s.mem (cx s₀) k) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 64 + 4 * k) (w := 4) (by omega)
  have eo := hp.c64 (k := 64 + 4 * k) (by omega)
  rw [← hwr] at o
  unfold stW stSrc wordOf
  split_ifs with h₁ h₂ h₃
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.store32, State.setReg, hedi, eo, o, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := hp.in_ctx' (a := 4 * (k - 4)) (w := 4) (by omega)
    have ei := hp.c64 (k := 4 * (k - 4)) (by omega)
    rw [← hrd, ← hwr] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.load32, State.store32, State.setReg, hedi, eo, ei, o, i, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.store32, State.setReg, hedi, eo, o, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := hp.in_ctx' (a := 32 + 4 * (k - 13)) (w := 4) (by omega)
    have ei := hp.c64 (k := 32 + 4 * (k - 13)) (by omega)
    rw [← hrd, ← hwr] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.load32, State.store32, State.setReg, hedi, eo, ei, o, i, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨c + BitVec.ofNat 64 64, n⟩] m m')
    {a : Nat} (ha : a + 4 ≤ 64) (hn : n ≤ 960) :
    m'.readW (c + BitVec.ofNat 64 a) 32 = m.readW (c + BitVec.ofNat 64 a) 32 := by
  refine hf.readW (r := ⟨c + BitVec.ofNat 64 a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨c + BitVec.ofNat 64 64, n⟩] m m')
    (hn : n ≤ 960) {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs
  · rfl
  · exact readW_frame_ctx hf (by omega) hn
  · rfl
  · exact readW_frame_ctx hf (by omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (hedi : s.gpr .edi = CX s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨cx s₀ + BitVec.ofNat 64 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (cx s₀ + BitVec.ofNat 64 (64 + 4 * i)) 32 = wordOf s.mem (cx s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    refine WP.mono (stW_ok hp (k := j) (by omega) (by rw [g₁ _ (by decide), hedi]) (by rw [rd₁, hrd])
      (by rw [wr₁, hwr])) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · simp only [Region.Contains]
        rw [show cx s₀ + BitVec.ofNat 64 (64 + 4 * j) - (cx s₀ + BitVec.ofNat 64 64) =
          BitVec.ofNat 64 (4 * j) by rw [BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
        omega
    · rw [m₂, wordOf_frame f₁ (by omega) (by omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]
        exact w₁ i (by omega)

theorem consts_eq : ∀ i < 4, ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : List (BitVec 32)).getD i 0 =
    Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 16] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (cx s₀ + BitVec.ofNat 64 (64 + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ a, a + 4 ≤ 44 → m₁.readW (cx s₀ + BitVec.ofNat 64 a) 32 =
      s₀.mem.readW (cx s₀ + BitVec.ofNat 64 a) 32 := by
    intro a ha
    refine hf₁.readW (r := sub s₀ a 4) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact sub_disj s₀ (by omega) (by omega) (by omega)
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show cx s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * i) = cx s₀ + BitVec.ofNat 64 (64 + 4 * i) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by omega)]
  · rfl
  · rw [r₁ _ (by omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by omega)]
    congr 1
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl

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

/-! ## The stages -/

/-- After the registers are saved and the ChaCha20 state stored: ready to
call the block function. -/
structure Pro2 (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  ecx : s.gpr .ecx = C32 s₀ 64
  edx : s.gpr .edx = C32 s₀ 128
  saved : Saved s₀ s.mem
  frame : Frame [sub s₀ 64 64, sub s₀ 592 16] s₀.mem s.mem
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

/-- After the block function: the one-time key at `ctx + 128`. -/
structure Pro3 (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (cx s₀ + BitVec.ofNat 64 128) 32 = otk s₀

/-- Ready to call `vg_poly1305_init`. -/
structure Pro4 (s₀ s : State) : Prop extends Pro3 s₀ s where
  ecx : s.gpr .ecx = C32 s₀ 128
  edx : s.gpr .edx = C32 s₀ 448

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  poly : Repr s.mem (cx s₀ + BitVec.ofNat 64 448) (otk s₀) []
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem B2_eq : save ++ [.mov .edi (.reg .eax)] ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128 =
    (save ++ [.mov .edi (.reg .eax)]) ++ (initState ++ (ptr .ecx .edi 64 ++ ptr .edx .edi 128)) := by
  simp only [List.append_assoc]

theorem pro2_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ [.mov .edi (.reg .eax)] ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128))
      (s₀.setReg .eax (CX s₀)) (Pro2 s₀) := by
  rw [B2_eq]
  refine WP.block_append (WP.mono (save_ok hp) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (initState_ok hp (j := 16) (Nat.le_refl _) e₁ rd₁ wr₁)
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi 64 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 128 s₃) fun s₄ ⟨e₄, g₄, rd₄, wr₄, m₄⟩ => ?_
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [g₂ _ (by decide), e₁]
  have hsp : s₄.gpr .esp = E s₀ := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide)]
  refine ⟨⟨hsp, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩,
    by rw [g₄ _ (by decide), g₃ _ (by decide), edi₂], by rw [g₄ _ (by decide), e₃, edi₂],
    by rw [e₄, g₃ _ (by decide), edi₂], ?_, ?_, ?_⟩
  · rw [m₄, m₃]
    exact (m₁ ▸ saveMem_saved s₀).frame f₂ (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega))
  · rw [m₄, m₃]
    exact ((m₁ ▸ saveMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  · rw [m₄, m₃]
    exact stateAt_initState (m₁ ▸ saveMem_frame s₀) w₂

theorem pro3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Pro2 s₀ s) :
    WP isa (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) s (Pro3 s₀) := by
  refine block_call hp h.at_ h.ecx h.edx fun s' at' cs' f' blk' => ?_
  have hd : ∀ {k n : Nat}, k + n ≤ 1024 → (k + n ≤ 128 ∨ 128 + 256 ≤ k) →
      ∀ r ∈ [sub s₀ 128 256, stkR s₀], (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact (hp.stk_sub h₁).symm
  have st' : stateAt s'.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f' (hd (k := 64) (n := 64) (by omega) (by omega)), h.st]
  refine ⟨at', by rw [cs' _ (by simp [calleeSaved]), h.edi],
    h.saved.frame f' (hd (by omega) (by omega)), ?_, st', ?_⟩
  · refine (h.frame.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [bytesAt_serialize _ _ (by omega), blk', h.st]; rfl

theorem pro4_ok {s₀ : State} {s : State} (h : Pro3 s₀ s) :
    WP isa (.block (ptr .ecx .edi 128 ++ ptr .edx .edi 448)) s (Pro4 s₀) := by
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi 128 s) fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 448 s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_
  have edi₁ : s₁.gpr .edi = CX s₀ := by rw [g₁ _ (by decide), h.edi]
  have mm : s₂.mem = s.mem := by rw [m₂, m₁]
  exact ⟨⟨⟨by rw [g₂ _ (by decide), g₁ _ (by decide), h.at_.esp], by rw [rd₂, rd₁, h.at_.rd],
    by rw [wr₂, wr₁, h.at_.wr]⟩, by rw [g₂ _ (by decide), edi₁], by rw [mm]; exact h.saved,
    by rw [mm]; exact h.frame, by rw [mm]; exact h.st, by rw [mm]; exact h.key⟩,
    by rw [g₂ _ (by decide), e₁, h.edi], by rw [e₂, edi₁]⟩

theorem post_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Pro4 s₀ s) :
    WP isa (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) s (PostP s₀) := by
  refine init_call hp h.at_ h.ecx h.edx fun s' at' cs' f' repr' => ?_
  have hd : ∀ {k n : Nat}, k + n ≤ 1024 → (k + n ≤ 448 ∨ 448 + 128 ≤ k) →
      ∀ r ∈ [sub s₀ 448 128, stkR s₀], (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact (hp.stk_sub h₁).symm
  have fine : Frame [workR s₀, stkR s₀] s₀.mem s'.mem :=
    h.frame.trans (f'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine ⟨⟨by rw [cs' _ (by simp [calleeSaved]), h.edi], at'.esp, at'.rd, at'.wr,
    h.saved.frame f' (hd (by omega) (by omega)), fine.sub fun r hr => ?_⟩, fine, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rwa [h.key] at repr'
  · rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f' (hd (k := 64) (n := 64) (by omega) (by omega)), h.st]

theorem prologue_eq : prologue =
    .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.seq (.block (save ++ [.mov .edi (.reg .eax)] ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128))
    (.seq (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block)
    (.seq (.block (ptr .ecx .edi 128 ++ ptr .edx .edi 448))
      (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init)))) := rfl

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  rw [prologue_eq]
  refine WP.seq (WP.mono (load_ok hp) fun s₁ e₁ => ?_)
  subst e₁
  exact WP.seq (WP.mono (pro2_ok hp) fun s₂ h₂ => WP.seq (WP.mono (pro3_ok hp h₂) fun s₃ h₃ =>
    WP.seq (WP.mono (pro4_ok h₃) fun s₄ h₄ => post_ok hp h₄)))

end VG.Proof.ChaCha20Poly1305.X86
