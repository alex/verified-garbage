import VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# Argon2 H′ on x86 (32-bit): the calls, in two runs

The macros calling the BLAKE2b functions leak the same trace in two runs that
pass them the same arguments (`init_rel`, `update_rel`, `finalize_rel`):
the instructions before each call are checked by the taint analysis, and the
call is related by the callee's constant time (`RelCT.callWith`), from the
callee's precondition in both runs (`init_pre`, `update_pre`,
`finalize_pre`). `rel_taint` and `rel_wp` add what each run satisfies by
correctness.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize initCode updateCode finalizeCode)
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-! ## Two runs -/

/-- Two runs, each described by `WP`, of code the taint analysis proves
constant time from the registers `rs` public. -/
theorem rel_taint {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (τr rs) (fun s₁ s₂ h => agree_regs (hag s₁ s₂ h.1 h.2)) hc).wp
    fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- What each run satisfies, added to two runs that leak the same trace. -/
theorem rel_wp {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  (hct.wp fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A relation proved from facts of the related states. -/
theorem RelCT.of_pre {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-- The callee's public data, `esp` and its first `n` arguments, agree in
two runs that agree on `esp` and on the registers pushed. -/
theorem call_pub {rs : List Reg} (hrs : Reg.esp ∉ rs) {s₁ s₂ : State}
    (fit : 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (rd wr : List Region) :
    ((pushed rs s₁).callEntry.withRegions rd wr).gpr .esp =
      ((pushed rs s₂).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs s₁).callEntry.withRegions rd wr) i =
      arg ((pushed rs s₂).callEntry.withRegions rd wr) i := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', hsp]
  · simp only [arg_withRegions]
    exact callEntry_arg_eq hrs fit hsp hr hi

/-! ## `init` -/

theorem init_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) {n : Nat}
    (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (ha : s.gpr .eax = 0)
    (hc : s.gpr .ecx = B) :
    CallPre (initX86 b) [.eax, .ecx, .edx, .ebx]
      [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .ecx, .edx, .ebx] s).callEntry with hsE
  have a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a1 : arg sE 1 = BitVec.ofNat 32 n := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hn]
  have a2 : arg sE 2 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hc]
  have a3 : arg sE 3 = 0 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have stR : Region.Sub ⟨B.setWidth 64, 192⟩ ⟨B.setWidth 64, 832⟩ := Region.sub_prefix (by decide)
  have d20 : (below E 20).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right stR).sub_left (below_sub (by decide) h.lo)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have mb : (64 : Nat) ≤ b.maxBytes := by decide
    refine ⟨rfl, rfl, fun _ h₁ _ => by simp [Region.Contains] at h₁, ?_, ?_,
      by simp only [Proof.Blake2.bufOff, blockBytes]; have := h.fits; omega,
      by simp; have := B.isLt; omega, ?_, by simp [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by simp⟩
    · exact d20.sub_left (below_sub (by decide) (by have := h.lo; omega))
    · refine d20.sub_left ?_
      have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) (by have := h.lo; omega)
      rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
        rw [← VG.Offset.sub_add_eq]; rfl]
      exact this
    · rw [sub_toNat (by have := h.lo; omega)]; have := E.isLt; omega
  · rw [esp₂]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
        ((h.wr.trans fun a k hi => let ⟨r', hr', hc'⟩ := hi
          InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)))
  · rw [esp₂]
    exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (h.wr.trans fun a k ⟨r', hr', hc'⟩ => ⟨r', List.mem_cons_of_mem _ hr', hc'⟩)

/-- What `init` needs: the state's context, and the digest length in `edx`. -/
def InitIn (B E : BitVec 32) (n : Nat) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .edx = BitVec.ofNat 32 n

theorem init_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B E n s₁ ∧ InitIn B E n s₂) Impl.Argon2.X86.HPrime.init
      fun _ _ => True := by
  have blk : ∀ s, InitIn B E n s → WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.reg .ebx)]) s
      fun t => Ctx B E t ∧ t.gpr .edx = BitVec.ofNat 32 n ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = B :=
    fun s ⟨c, e⟩ => wp_movi fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e],
       by rw [u₂.other _ (by decide), u₁.gpr],
       by rw [u₂.gpr, u₁.other _ (by decide), c.ebx]⟩
  unfold Impl.Argon2.X86.HPrime.init
  refine RelCT.seq (rel_taint [.esp, .ebx, .edx] (fun s₁ s₂ ⟨c₁, e₁⟩ ⟨c₂, e₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [e₁, e₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := initX86 b) init_correct Proof.Blake2.X86.B.init_ct
    [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩]
    fun s₁ s₂ ⟨⟨c₁, e₁, a₁, x₁⟩, ⟨c₂, e₂, a₂, x₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [x₁, x₂]
    · rw [e₁, e₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
    [⟨B.setWidth 64, 192⟩]
  exact ⟨init_pre c₁ e₁ hn₁ hn₂ a₁ x₁, init_pre c₂ e₂ hn₁ hn₂ a₂ x₂, hsp, p₁, p₂⟩

/-! ## `update` -/

theorem update_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) (ha : s.gpr .eax = B + 192) :
    CallPre (updateX86 b) [.eax, .edi, .esi, .edx, .ecx, .ebx]
      [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s).callEntry with hsE
  have a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a3 : arg sE 3 = D := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hD]
  have a4 : (arg sE 4).toNat = L := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hL]
  have a5 : arg sE 5 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 28 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have hfit := h.fits
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    h.stk.sub_right (Region.sub_prefix (by decide))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have stk60 : ∀ {k : Nat} {r : Region}, k ≤ 60 → (below E 60).Disjoint r → (below E k).Disjoint r :=
    fun hk d => d.sub_left (below_sub hk hlo)
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 24) (by omega) hlo
    rw [show E - BitVec.ofNat 32 28 = E - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 28) (by omega) hlo
    have e : (E - BitVec.ofNat 32 28 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 28).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ (below E 60) :=
    below_sub (by decide) hlo
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, a5, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hDs.sub_right (Region.sub_prefix (by decide))
    · exact hDs.sub_right (Offset.sub_base _ (by decide))
    · exact stR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · exact hDk.sub_left calleeStk
    · omega
    · omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₂]
    refine Covers.append_left (Covers.cons (covers_ins _ hDc) (Covers.cons (covers_frame rfl _)
      Covers.nil)) (covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
  · rw [esp₂]
    exact covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))

/-- What `update` needs: the state's context, the data at `D`, of `L` bytes,
and the count in `edx:ecx`. -/
def UpdateIn (B E D : BitVec 32) (L : Nat) (lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .esi = D ∧ (s.gpr .edi).toNat = L ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi ∧
    Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr)

theorem update_rel {B E D : BitVec 32} {L : Nat} {lo hi : BitVec 32} (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) :
    RelCT isa (fun s₁ s₂ => UpdateIn B E D L lo hi s₁ ∧ UpdateIn B E D L lo hi s₂) update
      fun _ _ => True := by
  have blk : ∀ s, UpdateIn B E D L lo hi s →
      WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192)]) s
      fun t => UpdateIn B E D L lo hi t ∧ t.gpr .eax = B + 192 :=
    fun s ⟨c, e1, e2, e3, e4, cv⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e1],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e2],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e4],
       by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact cv⟩,
       by rw [u₂.gpr, u₁.gpr, c.ebx]⟩
  unfold update
  refine RelCT.seq (rel_taint [.esp, .ebx, .esi, .edi, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, d₁, l₁, x₁, y₁, _⟩ ⟨c₂, d₂, l₂, x₂, y₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [d₁, d₂]
      · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := updateX86 b) update_correct Proof.Blake2.X86.B.update_ct
    [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, d₁, l₁, x₁, y₁, v₁⟩, a₁⟩, ⟨⟨c₂, d₂, l₂, x₂, y₂, v₂⟩, a₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
    · rw [d₁, d₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨update_pre c₁ d₁ l₁ hDfit v₁ hDs hDk a₁, update_pre c₂ d₂ l₂ hDfit v₂ hDs hDk a₂, hsp, p₁, p₂⟩

/-! ## `finalize` -/

theorem finalize_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) (ha : s.gpr .eax = B + 192)
    (hi : s.gpr .esi = B + 768) :
    CallPre (finalizeX86 b) [.eax, .esi, .edx, .ecx, .ebx] [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .esi, .edx, .ecx, .ebx] := by decide
  have esp₄ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  have hfit := h.fits
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₄]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s).callEntry with hsE
  have a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a3 : arg sE 3 = B + 768 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hi]
  have a4 : arg sE 4 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₄]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 24 := by
    rw [hsE, callEntry_esp', esp₄]; rfl
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega)
  have e768 : (B + 768).setWidth 64 = B.setWidth 64 + 768 := setWidth_add (d := 768) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right (Region.sub_prefix (by decide)))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have dgR : (below E 60).Disjoint ⟨B.setWidth 64 + 768, 64⟩ := h.stk_sub (d := 768) (by decide) (Nat.le_refl _)
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below E 60) :=
    below_sub (by decide) hlo
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 20) (by omega) hlo
    rw [show E - BitVec.ofNat 32 24 = E - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 24) (by omega) hlo
    have e : (E - BitVec.ofNat 32 24 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 24).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  have b768 : (B + 768).toNat = B.toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, eA, eSp, e192, e768, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact stR.sub_left argSub
    · exact dgR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact dgR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact dgR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · omega
    · rw [b768]; omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₄]
    refine Covers.append_left (Covers.cons (covers_frame rfl _) Covers.nil)
      (covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
  · rw [esp₄]
    exact covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))

/-- What `finalize` needs: the state's context and the count in `edx:ecx`. -/
def FinalizeIn (B E lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi

theorem finalize_rel {B E lo hi : BitVec 32} :
    RelCT isa (fun s₁ s₂ => FinalizeIn B E lo hi s₁ ∧ FinalizeIn B E lo hi s₂) finalize
      fun _ _ => True := by
  have blk : ∀ s, FinalizeIn B E lo hi s → WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm 768)]) s
      fun t => FinalizeIn B E lo hi t ∧ t.gpr .eax = B + 192 ∧ t.gpr .esi = B + 768 :=
    fun s ⟨c, e3, e4⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
      WP.block_nil
      ⟨⟨c.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]),
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e4]⟩,
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, c.ebx],
       by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]⟩
  unfold finalize
  refine RelCT.seq (rel_taint [.esp, .ebx, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, x₁, y₁⟩ ⟨c₂, x₂, y₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := finalizeX86 b) finalize_correct Proof.Blake2.X86.B.finalize_ct
    [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, x₁, y₁⟩, a₁, i₁⟩, ⟨⟨c₂, x₂, y₂⟩, a₂, i₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [i₁, i₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨finalize_pre c₁ a₁ i₁, finalize_pre c₂ a₂ i₂, hsp, p₁, p₂⟩

end VG.Proof.Argon2.X86.HPrime
