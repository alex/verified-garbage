import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Common
import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20-Poly1305 on AArch64: the prologue

Untrusted: everything here is checked by Lean. Saving the registers, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_mov wp_str wp_str32 wp_ldr32)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Saving the registers -/

theorem saveMoves_eq : save ++ moves =
    [.str .x .x22 .x0 600, .str .x .x23 .x0 608, .str .x .x24 .x0 616, .str .x .x25 .x0 624,
     .str .x .x30 .x0 632, .str .x .x21 .x0 592,
     mov .x21 .x0, mov .x24 .x1, mov .x25 .x2, mov .x22 .x3, mov .x23 .x4] := rfl

/-- The registers the moves write. -/
theorem untouched_ne {r : Reg} (hr : r ∈ untouched) :
    r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x25 := by
  simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saveMoves_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves)) s₀ fun s =>
      s.gpr .x21 = cx s₀ ∧ s.gpr .x24 = ad s₀ ∧ s.gpr .x25 = s₀.gpr .x2 ∧ s.gpr .x22 = dp s₀ ∧
      s.gpr .x23 = s₀.gpr .x4 ∧ (∀ r ∈ untouched, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧
      s.wr = s₀.wr ∧ Frame [sub s₀ 592 48] s₀.mem s.mem ∧ Saved s₀ s.mem := by
  have o : ∀ d, 592 ≤ d → d + 8 ≤ 640 → InRegions s₀.wr (off (cx s₀) d) 8 :=
    fun d _ h => hp.in_ctx (by omega)
  rw [saveMoves_eq]
  refine wp_str (a := off (cx s₀) 600) (by decide) rfl (o 600 (by omega) (by omega)) fun s₁ g₁ => ?_
  refine wp_str (a := off (cx s₀) 608) (by decide) (by rw [g₁.gpr])
    (by rw [g₁.wr]; exact o 608 (by omega) (by omega)) fun s₂ g₂ => ?_
  have e₂ : s₂.gpr = s₀.gpr := by rw [g₂.gpr, g₁.gpr]
  refine wp_str (a := off (cx s₀) 616) (by decide) (by rw [e₂])
    (by rw [g₂.wr, g₁.wr]; exact o 616 (by omega) (by omega)) fun s₃ g₃ => ?_
  refine wp_str (a := off (cx s₀) 624) (by decide) (by rw [g₃.gpr, e₂])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact o 624 (by omega) (by omega)) fun s₄ g₄ => ?_
  have e₄ : s₄.gpr = s₀.gpr := by rw [g₄.gpr, g₃.gpr, e₂]
  refine wp_str (a := off (cx s₀) 632) (by decide) (by rw [e₄])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact o 632 (by omega) (by omega)) fun s₅ g₅ => ?_
  refine wp_str (a := off (cx s₀) 592) (by decide) (by rw [g₅.gpr, e₄])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact o 592 (by omega) (by omega)) fun s₆ g₆ => ?_
  have e₆ : s₆.gpr = s₀.gpr := by rw [g₆.gpr, g₅.gpr, e₄]
  refine wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ =>
    wp_mov fun s₁₁ u₁₁ => WP.block_nil ?_
  have hm : s₁₁.mem = (((((s₀.mem.writeW (off (cx s₀) 600) (s₀.gpr .x22)).writeW (off (cx s₀) 608)
      (s₀.gpr .x23)).writeW (off (cx s₀) 616) (s₀.gpr .x24)).writeW (off (cx s₀) 624)
      (s₀.gpr .x25)).writeW (off (cx s₀) 632) (s₀.gpr .x30)).writeW (off (cx s₀) 592) (s₀.gpr .x21) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem,
      g₅.gpr, e₄, g₃.gpr, e₂, g₁.gpr]
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 640 → (sub s₀ 592 48).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · have h := untouched_ne hr
    rw [u₁₁.other _ h.2.2.1, u₁₀.other _ h.2.1, u₉.other _ h.2.2.2.2, u₈.other _ h.2.2.2.1,
      u₇.other _ h.1, e₆]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 600 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 608 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 616 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 624 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 632 (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 592 (Nat.le_refl _) (by omega))
  · rw [hm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_off]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off c (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off c (32 + 4 * (k - 13))) 32

/-- The context may be read and written. -/
def CtxOk (c : Addr) (s : State) : Prop :=
  ∀ a w, a + w ≤ 1024 → InRegions (s.rd ++ s.wr) (off c a) w ∧ InRegions s.wr (off c a) w

/-- `movz` of the low half and `movk` of the high half, then a 32-bit store. -/
theorem const_word (c : BitVec 32) :
    (((((c.extractLsb' 0 16).setWidth 32).setWidth 64).setWidth 32 &&& (0xFFFF : BitVec 32) |||
      (c.extractLsb' 16 16).setWidth 32 <<< 16 : BitVec 32).setWidth 64).setWidth 32 = c := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq, BitVec.setWidth_eq]
  exact movz_movk c

theorem load_word (v : BitVec 32) : ((v.setWidth 64).setWidth 32) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem stW_ok {c : Addr} {k : Nat} (hk : k < 16) {s : State} (hx21 : s.gpr .x21 = c) (hc : CtxOk c s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off c (64 + 4 * k)) (wordOf s.mem c k) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := (hc (64 + 4 * k) 4 (by omega)).2
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_movz32 fun s₁ u₁ => wp_movk32 fun s₂ u₂ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by omega) (by rw [u₂.other _ (by decide),
      u₁.other _ (by decide), hx21]) (by rw [u₂.wr, u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, const_word], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    have i := (hc (4 * (k - 4)) 4 (by omega)).1
    refine wp_ldr32 (a := off c (4 * (k - 4))) (by omega) (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, load_word], fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩
  by_cases h₃ : k = 12
  · simp only [h₃, ite_true]
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * 12)) (by omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact h₃ ▸ o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; rfl, fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    have i := (hc (32 + 4 * (k - 13)) 4 (by omega)).1
    refine wp_ldr32 (a := off c (32 + 4 * (k - 13))) (by omega) (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, load_word], fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') {a : Nat}
    (ha : a + 4 ≤ 64) (hn : n ≤ 960) : m'.readW (off c a) 32 = m.readW (off c a) 32 := by
  refine hf.readW (r := ⟨off c a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') (hn : n ≤ 960)
    {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs <;> first | rfl | exact readW_frame_ctx hf (by omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hx21 : s.gpr .x21 = c)
    (hc : CtxOk c s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off c (64 + 4 * i)) 32 = wordOf s.mem c i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk c s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok (by omega) (by rw [g₁ _ (by decide), hx21]) hc₁) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · simp only [Region.Contains]
        rw [show c + BitVec.ofNat 64 (64 + 4 * j) - (c + BitVec.ofNat 64 64) = BitVec.ofNat 64 (4 * j) by
          rw [BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
        omega
    · rw [m₂, wordOf_frame f₁ (by omega) (by omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW32_off _ _ _ (by omega) (by omega) (by omega)]
        exact w₁ i (by omega)

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 48] s₀.mem m₁)
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
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * i) = off (cx s₀) (64 + 4 * i) from off_off _ _ _, hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by omega)]
  · rfl
  · rw [r₁ _ (by omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by omega)]
    refine congrArg (fun a => s₀.mem.readW a 32) ?_
    show cx s₀ + BitVec.ofNat 64 (32 + 4 * (i - 13)) = cx s₀ + 32 + BitVec.ofNat 64 (4 * (i - 13))
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

/-! ## The first block -/

/-- `x0 = x21 + a` and `x1 = x21 + b`. -/
theorem ptrs2_ok {a b : Nat} (ha : a < 4096) (hb : b < 4096) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm ha fun s₁ u₁ => wp_addImm hb fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the first block: the registers saved and moved, the ChaCha20
state, and the pointers for the block function. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  x0 : s.gpr .x0 = off (cx s₀) 64
  x1 : s.gpr .x1 = off (cx s₀) 128

theorem sub1 (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (workR s₀) := by
  intro x hx
  simp only [Region.Contains] at *
  bv_omega

theorem block1_eq : save ++ moves ++ initState ++ [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] =
    (save ++ moves) ++ (initState ++ [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128]) := by
  simp only [List.append_assoc]

theorem block1_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves ++ initState ++ [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128])) s₀
      (Post1 s₀) := by
  rw [block1_eq]
  refine WP.block_append (WP.mono (WP.withSp (saveMoves_ok hp))
    fun s₁ ⟨⟨e21, e24, e25, e22, e23, un₁, rd₁, wr₁, f₁, sv₁⟩, sp₁⟩ => ?_)
  have hc₁ : CtxOk (cx s₀) s₁ := fun a w h => by
    rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩
  refine WP.block_append (WP.mono (WP.withSp (initState_ok (j := 16) (Nat.le_refl _) e21 hc₁))
    fun s₂ ⟨⟨g₂, rd₂, wr₂, f₂, w₂⟩, sp₂⟩ => ?_)
  refine WP.mono (ptrs2_ok (a := 64) (b := 128) (by omega) (by omega) s₂) fun s₃ ⟨h0, h1, k₃⟩ => ?_
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (by decide), e21]
  have hm : s₃.mem = s₂.mem := funext fun x => k₃.frame x fun _ h => absurd h List.not_mem_nil
  have f₂' : Frame [sub s₀ 64 64] s₁.mem s₂.mem := f₂
  have gcs : ∀ r ∈ preserved, r ≠ .x30 → s₃.gpr r = s₂.gpr r := k₃.cs
  have fine : Frame [workR s₀] s₀.mem s₃.mem := by
    rw [hm]
    refine (f₁.sub fun r hr => ?_).trans (f₂'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by omega) (by omega)⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [gcs _ (pres .x21) (pres30 .x21), x21₂]
  · rw [gcs _ (pres .x22) (pres30 .x22), g₂ _ (by decide), e22]
  · rw [gcs _ (pres .x23) (pres30 .x23), g₂ _ (by decide), e23]
  · rw [gcs _ (pres .x24) (pres30 .x24), g₂ _ (by decide), e24]
  · rw [gcs _ (pres .x25) (pres30 .x25), g₂ _ (by decide), e25]
  · have h := untouched_preserved r hr
    rw [gcs r h.1 h.2, g₂ r (by rintro rfl; simp [untouched] at hr), un₁ r hr]
  · rw [k₃.sp, sp₂, sp₁]
  · rw [k₃.rd, rd₂, rd₁]
  · rw [k₃.wr, wr₂, wr₁]
  · rw [hm]
    exact sv₁.frame f₂' (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega))
  · exact fine.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · exact fine
  · rw [hm]; exact stateAt_initState f₁ w₂
  · rw [h0, x21₂]
  · rw [h1, x21₂]

/-! ## The whole prologue -/

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) (h₃ : k + n ≤ 592 ∨ 640 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 s₀ h₁ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by omega) (by omega) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

/-- The frame of a part that writes `ctx[k, k + n)`, in the working space. -/
theorem frame_work1 {s₀ s s' : State} {k n : Nat} (hk : Kept [sub s₀ k n] s s') (h₁ : 64 ≤ k)
    (h₂ : k + n ≤ 1024) : Frame [workR s₀] s.mem s'.mem :=
  hk.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 s₀ h₁ h₂⟩

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  unfold prologue
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (block_call h₁.x0 h₁.x1
    (sub_disj s₀ (a := 128) (n := 256) (b := 64) (m := 64) (by omega) (by omega) (by omega))
    (covers2 hp h₁.inv.wr (a := 128) (n := 256) (b := 64) (m := 64) (by omega) (by omega))
    (covers1 hp h₁.inv.wr (a := 128) (n := 256) (by omega)) fun s₂ k₂ blk₂ => ?_)
  have i₂ := h₁.inv.step1 (k := 128) (n := 256) k₂ (by omega) (by omega) (by omega)
  refine WP.seq (WP.mono (ptrs2_ok (a := 448) (b := 128) (by omega) (by omega) s₂)
    fun s₃ ⟨h0, h1, k₃⟩ => ?_)
  have i₃ := i₂.step0 k₃
  rw [i₂.x21] at h0 h1
  refine init_call h0 h1 (sub_disj s₀ (a := 448) (n := 128) (b := 128) (m := 32) (by omega) (by omega)
      (by omega))
    (covers2 hp i₃.wr (a := 448) (n := 128) (b := 128) (m := 32) (by omega) (by omega))
    (covers1 hp i₃.wr (a := 448) (n := 128) (by omega)) fun s₄ k₄ repr₄ => ?_
  have m₃ := k₃.mem_eq
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by omega)), h₁.st]
  refine ⟨i₃.step1 (k := 448) (n := 128) k₄ (by omega) (by omega) (by omega),
    h₁.fine.trans ((frame_work1 (k := 128) (n := 256) k₂ (by omega) (by omega)).trans (by
      rw [← m₃]; exact frame_work1 (k := 448) (n := 128) k₄ (by omega) (by omega))), ?_, ?_⟩
  · have hk : bytesAt s₃.mem (off (cx s₀) 128) 32 = otk s₀ := by
      rw [m₃, bytesAt_serialize _ _ (by omega), blk₂, h₁.st]; rfl
    rw [← hk]; exact repr₄
  · rw [stateAt_frame k₄.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by omega)), m₃, st₂]

end VG.Proof.ChaCha20Poly1305.AArch64
