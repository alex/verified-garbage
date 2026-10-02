import VerifiedGarbage.Proof.CmacAes.X86.Dbl
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys`

`L = CIPH_K(0)` is computed into the first block of the subkeys (a zero
counter block and a zero data block), then doubled there (`K1`) and into the
second block (`K2`). Only the subkeys, the scratch buffer and the 28 bytes
below `esp` change, so the stack arguments, which are reloaded from the stack,
and the return address are intact.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := arg s₀ 2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := arg s₀ 3

abbrev kR : Region := ⟨(Kb s₀).setWidth 64, 32⟩
abbrev scR : Region := ⟨(Sc s₀).setWidth 64, 2176⟩
abbrev kArgsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The regions the function writes, with the stack below it. -/
abbrev SBig : List Region := [kR s₀, scR s₀, stkR s₀]

/-- The memory after saving the registers in the scratch buffer. -/
def sSaved : Mem := Spill.saveMem s₀.mem ((Sc s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

/-- The memory before the call. -/
def sPreMem : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (sSaved s₀) ((Sc s₀).setWidth 64 + BitVec.ofNat 64 2048)) ((Kb s₀).setWidth 64)

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, kArgsR s₀]
  wr : s₀.wr = [kR s₀, scR s₀]
  sch_k : (schR s₀).Disjoint (kR s₀)
  sch_scr : (schR s₀).Disjoint (scR s₀)
  k_scr : (kR s₀).Disjoint (scR s₀)
  args_k : (kArgsR s₀).Disjoint (kR s₀)
  args_scr : (kArgsR s₀).Disjoint (scR s₀)
  ret_k : (retR s₀).Disjoint (kR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_k : (stkR s₀).Disjoint (kR s₀)
  b_scr : (stkR s₀).Disjoint (scR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 20 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysX86.pre s₀) : SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

/-! ## Addresses and regions -/

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

theorem sSaved_frame (s₀ : State) : Frame [scR s₀] s₀.mem (sSaved s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := saved_bound p hp; Offset.contains_base _ (by omega) (by omega)

section
variable {s₀ : State} (hp : SPre s₀)
include hp

theorem SPre.below_eq : below (E s₀) 28 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem SPre.argA {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem SPre.arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (kArgsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem SPre.arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨kArgsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem SPre.args_stk : (kArgsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 16⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `SBig` changes. -/
theorem SPre.arg_keep {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_k.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem SPre.sched_bytes {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) :
    Spec.Aes.bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_k.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem SPre.ret_keep {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_k
    · exact hp.ret_scr
    · exact ret_stk s₀) (by decide)

theorem SPre.cA : (Sc s₀ + BitVec.ofNat 32 2048).setWidth 64 = (Sc s₀).setWidth 64 + BitVec.ofNat 64 2048 :=
  addr_eq (by have := hp.scr_fit; omega)

end

/-- The frame of the code that changes only the subkeys, the scratch buffer
but the saved registers, and the stack below `esp`. -/
theorem sbig_of {s₀ : State} {m : Mem}
    (hf : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) m) : Frame (SBig s₀) s₀.mem m :=
  ((sSaved_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-! ## Before the call -/

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : CtrPre s (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = sPreMem s₀

theorem subkeysPre_eq : subkeysPre = .mov .eax (argOp 3) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    (.mov .ebp (.reg .eax) :: .mov .ebx (argOp 2) :: (zero4 .ebp 2048 ++ (zero4 .ebx 0 ++ ctrArgs)))) := rfl

theorem sPreMem_frame (s₀ : State) :
    Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) (sPreMem s₀) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩)

theorem spre_wp {s₀ : State} (hp : SPre s₀) : WP isa (.block subkeysPre) s₀ (SAfter s₀) := by
  have hsc := hp.scr_fit
  have hk := hp.k_fit
  have cA := hp.cA
  rw [subkeysPre_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = Sc s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = sSaved s₀ := by
    rw [u₂.mem, u₁.mem, h₁, sSaved]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have big₂ : Frame (SBig s₀) s₀.mem s₂.mem := by rw [hm₂]; exact (sSaved_frame s₀).mono (by simp)
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem]; exact hp.arg_keep big₂ (by decide)) fun s₄ u₄ => ?_
  have p₄ : s₄.gpr .ebp = Sc s₀ := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  have b₄ : s₄.gpr .ebx = Kb s₀ := u₄.gpr
  have w₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [p₄]; omega) ?_ fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  · rw [p₄, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
  have b₅ : s₅.gpr .ebx = Kb s₀ := by rw [g₅ _ (by decide), b₄]
  refine zero4_ok (b := .ebx) (d := 0) (by decide) (by rw [b₅]; omega) ?_ fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  · rw [b₅, add0, wr₅, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
  have esp₆ : s₆.gpr .esp = E s₀ := by
    rw [g₆ _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have mem₆ : s₆.mem = sPreMem s₀ := by
    rw [m₆, b₅, add0, m₅, p₄, u₄.mem, u₃.mem, hm₂]; rfl
  have big₆ : Frame (SBig s₀) s₀.mem s₆.mem := by rw [mem₆]; exact sbig_of (sPreMem_frame s₀)
  have rw₆ : s₆.rd ++ s₆.wr = s₀.rd ++ s₀.wr := by rw [rd₆, wr₆, rd₅, wr₅, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]
  rw [ctrArgs_eq]
  refine wp_arg (s₀ := s₀) esp₆ (by rw [rw₆]; exact hp.arg_in (by decide)) (hp.arg_keep big₆ (by decide))
    fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₇.other _ (by decide), esp₆])
    (by rw [u₇.rd, u₇.wr, rw₆]; exact hp.arg_in (by decide))
    (by rw [u₇.mem]; exact hp.arg_keep big₆ (by decide)) fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁₁.gpr r = s₆.gpr r := fun r ha hc hd hi => by
    rw [u₁₁.other _ hi, u₁₀.other _ hd, u₉.other _ hd, u₈.other _ hc, u₇.other _ ha]
  have p₆ : s₆.gpr .ebp = Sc s₀ := by rw [g₆ _ (by decide), g₅ _ (by decide), p₄]
  have b₆ : s₆.gpr .ebx = Kb s₀ := by rw [g₆ _ (by decide), b₅]
  have sp₁₁ : s₁₁.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₆]
  have rd₁₁ : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₁ : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, w₄]
  have mem₁₁ : s₁₁.mem = sPreMem s₀ := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, mem₆]
  have hb : below (s₁₁.gpr .esp) 28 = stkR s₀ := by rw [sp₁₁]; exact hp.below_eq
  refine ⟨⟨?_, ?_, ?_, ?_, u₁₁.gpr, ?_, hp.rounds, by rw [sp₁₁]; exact hp.esp28, ?_,
    hp.sch_k.sub_right (Region.sub_prefix (by decide)), hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    ?_, ?_, (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_, by omega, by omega,
    ?_, ?_, ?_⟩, sp₁₁, rd₁₁, wr₁₁, mem₁₁⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact arg_ofNat s₀ 1
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), p₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₆]
  · rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [cA]
    exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [rd₁₁, wr₁₁, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₁₁, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₁₁, sPreMem]; exact Proof.Cmac.zero4_bytes _ _

/-! ## The call, the doubling and the restore -/

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++ (.mov .eax (argOp 3) ::
    (saved.map fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ [])) := rfl

theorem subkeys_wp {s₀ : State} (h0 : subkeysX86.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ subkeysX86.post s₀ s' := by
  have hp := SPre.of h0
  have hk := hp.k_fit
  have hsc := hp.scr_fit
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cA := hp.cA
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨(Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨(Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => by
      obtain ⟨r, hr, hc⟩ := cK d n h a k hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold subkeys
  refine WP.seq (WP.mono (spre_wp hp) fun s₁ a => ?_)
  refine WP.seq (WP.mono (ctr_call v a.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = stkR s₀ := by rw [a.esp]; exact hp.below_eq
  -- The memory after the call.
  have f₂ : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sPreMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA, a.mem] at fr
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have fr₂ := (sPreMem_frame s₀).trans f₂
  have kC : (⟨(Kb s₀).setWidth 64, 16⟩ : Region).Disjoint ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have zC : Spec.Aes.bytesAt (sPreMem s₀) ((Sc s₀).setWidth 64 + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [sPreMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  have L : Spec.Aes.bytesAt s₂.mem ((Kb s₀).setWidth 64) 16 = ciph s₀ (Spec.Cmac.zeros 16) := by
    have out := h₂.out
    rw [hp.sched_bytes (by rw [a.mem]; exact sbig_of (sPreMem_frame s₀)), cA, a.mem, zC] at out
    exact out
  have b₂ : s₂.gpr .ebx = Kb s₀ := by rw [h₂.saved .ebx (by simp [calleeSaved]), a.pre.ebx]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, a.rd, a.wr]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, a.wr]
  -- The doubling.
  rw [subkeysPost_eq]
  refine dbl_wp b₂ (by omega) (by omega) (by rw [rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₂]; exact cK 0 16 (by decide)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have b₃ : s₃.gpr .ebx = Kb s₀ := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b₂]
  refine dbl_wp b₃ (by omega) (by omega) (by rw [rd₃, wr₃, rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₃, wr₂]; exact cK 16 16 (by decide)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have f₄ : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) s₄.mem := by
    refine fr₂.trans (((dblMem_frame _ _ _ _).sub fun r hr => ?_).trans ((dblMem_frame _ _ _ _).sub fun r hr => ?_))
      |> fun h => by rw [m₄, m₃]; exact h
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact ⟨kR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨kR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have big₄ := sbig_of f₄
  have esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h₂.saved .esp (by simp [calleeSaved]), a.esp]
  have rdwr₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]
  -- The restore.
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rdwr₄]; exact hp.arg_in (by decide)) (hp.arg_keep big₄ (by decide))
    fun s₅ u₅ => ?_
  have sl : ∀ r d, (r, d) ∈ saved → s₄.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := saved_bound _ hrd
    rw [f₄.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide)]
    exact saveMem_slot _ _ _ hrd
  have hsc' : (arg s₀ 3).toNat + 2176 ≤ 2 ^ 32 := hsc
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₅.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₅.gpr, u₅.mem]; exact sl p.1 p.2 hp') fun s₆ r₆ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₅.gpr, u₅.rd, u₅.wr, rdwr₄, hp.rd, hp.wr]
    exact ⟨scR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₆.abi (by decide) (by decide) (by rw [u₅.other _ (by decide), esp₄]), ?_⟩, ?_⟩
  · rw [r₆.mem, u₅.mem]; exact hp.ret_keep big₄
  · show Spec.Aes.bytesAt s₆.mem ((Kb s₀).setWidth 64) 32 = _
    have b₃' : Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem ((Kb s₀).setWidth 64) 16) := by
      have := dblMem_bytes s₂.mem ((Kb s₀).setWidth 64) 0 0
      rw [add0] at this; rw [m₃, this]
    have lo : Spec.Aes.bytesAt s₄.mem ((Kb s₀).setWidth 64) 16 = Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16 := by
      rw [m₄]
      exact Proof.Cmac.bytesAt_frame16 (dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega)).symm
    have hi : Spec.Aes.bytesAt s₄.mem ((Kb s₀).setWidth 64 + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16) := by
      have := dblMem_bytes s₃.mem ((Kb s₀).setWidth 64) 0 16
      rw [add0] at this; rw [m₄, this]
    rw [r₆.mem, u₅.mem, Proof.Cmac.bytesAt_32, lo, hi, b₃', L]
    rfl

end VG.Proof.CmacAes.X86
