import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_finish`

The code saves the registers, copies the chaining value to `out`, computes the
number of bytes held back, and calls `vg_cmac_aes_finalize` with the state as
its key and `out` as its state: its result is the MAC of the message the state
represents (`repr_finish`). The code before the call is constant time by the
taint analysis, and the call by its own proof (`fin_rel`), its arguments
pinned by `HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86 VG.WriteBytes
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.CmacAes.X86 (wp_arg saveMem_congr toNat_rounds)
open VG.Proof.Cmac.Stream (held held_le)

section
variable (s₀ : State)

abbrev hSt : BitVec 32 := arg s₀ 0
abbrev hR : Nat := (arg s₀ 1).toNat
abbrev hO : BitVec 32 := arg s₀ 4
abbrev hSc : BitVec 32 := arg s₀ 5
abbrev hE : BitVec 32 := s₀.gpr .esp
abbrev hstR : Region := ⟨(hSt s₀).setWidth 64, 304⟩
abbrev hoR : Region := ⟨(hO s₀).setWidth 64, 16⟩
abbrev hscR : Region := ⟨(hSc s₀).setWidth 64, 2304⟩
abbrev haR : Region := ⟨argAddr s₀ 0, 24⟩
/-- The bytes held back. -/
abbrev hH : Nat := held (countX86 s₀).toNat

/-- Where the function writes: the state, `out`, the scratch buffer and the stack. -/
abbrev HBig : List Region := [hstR s₀, hoR s₀, hscR s₀, below (hE s₀) 56]

end

/-- The precondition, by name. -/
structure HPre (s₀ : State) : Prop where
  rd : s₀.rd = [haR s₀]
  wr : s₀.wr = [hstR s₀, hoR s₀, hscR s₀]
  st_o : (hstR s₀).Disjoint (hoR s₀)
  st_s : (hstR s₀).Disjoint (hscR s₀)
  o_s : (hoR s₀).Disjoint (hscR s₀)
  a_st : (haR s₀).Disjoint (hstR s₀)
  a_o : (haR s₀).Disjoint (hoR s₀)
  a_s : (haR s₀).Disjoint (hscR s₀)
  ret_st : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hstR s₀)
  ret_o : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hoR s₀)
  ret_s : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hscR s₀)
  b_st' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (hstR s₀)
  b_o' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (hoR s₀)
  b_s' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (hscR s₀)
  fSt : (hSt s₀).toNat + 304 ≤ 2 ^ 32
  fO : (hO s₀).toNat + 16 ≤ 2 ^ 32
  fS : (hSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp56 : 56 ≤ (hE s₀).toNat
  espfit : (hE s₀).toNat + 28 ≤ 2 ^ 32
  rounds : hR s₀ = 10 ∨ hR s₀ = 12 ∨ hR s₀ = 14

theorem HPre.of {s₀ : State} (h : finishX86.pre s₀) : HPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

namespace HPre
variable {s₀ : State} (hp : HPre s₀)
include hp

theorem b_st : (below (hE s₀) 56).Disjoint (hstR s₀) := by rw [below_eq hp.esp56]; exact hp.b_st'
theorem b_o : (below (hE s₀) 56).Disjoint (hoR s₀) := by rw [below_eq hp.esp56]; exact hp.b_o'
theorem b_s : (below (hE s₀) 56).Disjoint (hscR s₀) := by rw [below_eq hp.esp56]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 6 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨haR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `HBig` changes. -/
theorem keep {m : Mem} (hf : Frame (HBig s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_o.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp56).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 6 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_o hp.a_o
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end HPre

theorem HPre.savedMem_big {s₀ : State} (_hp : HPre s₀) : Frame (HBig s₀) s₀.mem (savedMem s₀ (hSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨hscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the call -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (save ++ ([.mov .esi (argOp 0), .alu .add .esi (.imm 272),
    .mov .edi (argOp 4), .mov .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure HS₁ (s₀ s : State) : Prop where
  esi : s.gpr .esi = hSt s₀ + BitVec.ofNat 32 272
  edi : s.gpr .edi = hO s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 16
  esp : s.gpr .esp = hE s₀
  mem : s.mem = savedMem s₀ (hSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : HPre s₀) : WP isa (.block finSave) s₀ (HS₁ s₀) := by
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := hSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = savedMem s₀ (hSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 4 (by decide)) fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  exact ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.gpr], u₆.gpr,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']⟩

/-- The memory after the saves and the copy of the chaining value. -/
def hMem (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
    (Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)

theorem hMem_frame {s₀ : State} (hp : HPre s₀) : Frame (HBig s₀) s₀.mem (hMem s₀) :=
  hp.savedMem_big.trans ((writeBytes_frame _ _ _ (by
    rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, fun _ h => h⟩)

/-- What the code before the call leaves. -/
structure HMid (s₀ s : State) : Prop where
  args : FArgs s (hSt s₀) (hO s₀) (hSt s₀ + BitVec.ofNat 32 288) (hSc s₀) (hH s₀) (hR s₀)
  esp : s.gpr .esp = hE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = hMem s₀

theorem finPre_wp {s₀ : State} (hp : HPre s₀) : WP isa finPre s₀ (HMid s₀) := by
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have hh₂ : hH s₀ ≤ 16 := held_le _
  have fS₂ : (hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  unfold finPre
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  have p272 : ((hSt s₀ + BitVec.ofNat 32 272).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    add_setWidth (by omega)
  have c272 : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 272).setWidth 64, 16⟩ (hstR s₀) := by
    rw [p272]; exact Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono (copy_wp (L := 16) (by decide) h₁.esi h₁.edi h₁.ecx
    (fun _ => by rw [add_toNat (by omega)]; omega) (fun _ => by omega)
    (fun _ => by
      rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨hstR s₀, by simp, 272, p272, by simp⟩)
    (fun _ => by
      rw [h₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩)
    (fun _ => hp.st_o.sub_left c272)) fun s₂ h₂ => ?_)
  obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
  have hm₂ : s₂.mem = hMem s₀ := by rw [m₂, h₁.mem, p272]; rfl
  have esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h₁.esp]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, h₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, h₁.wr]
  have av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep (hMem_frame hp) hi
  refine WP.seq (held_ok (r := .esi) (by decide) (by decide) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 2 (by decide)) (av 3 (by decide))
    fun s₃ esi₃ g₃ m₃ rd₃ wr₃ => ?_)
  have esp₃ : s₃.gpr .esp = hE s₀ := by rw [g₃ _ (by decide) (by decide), esp₂]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, rd₂', wr₂']
  have av₃ : ∀ i < 6, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by rw [m₃]; exact av i hi
  unfold finArgs
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rw₃]; exact hp.arg_in (by decide)) (av₃ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide)) (by rw [u₄.mem]; exact av₃ 1 (by decide))
    fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem]; exact av₃ 4 (by decide)) fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), esp₃])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact av₃ 5 (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have esp₉ : s₉.gpr .esp = hE s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂']
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂']
  have m₉ : s₉.mem = hMem s₀ := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, hm₂]
  have hh := held_le (countX86 s₀).toNat
  have p288 : ((hSt s₀ + BitVec.ofNat 32 288).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    add_setWidth (by omega)
  have cP : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 288).setWidth 64, hH s₀⟩ (hstR s₀) := by
    rw [p288]; exact Offset.sub_base _ (by omega)
  refine ⟨?_, esp₉, rd₉, wr₉, m₉⟩
  exact
  { eax := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr]
    ecx := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr]; exact arg_ofNat s₀ 1
    edx := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    ebx := by
      rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
    esi := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
    edi := u₉.gpr
    rounds := hp.rounds
    len := hh
    esp := by rw [esp₉]; exact e56
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left cP
    ps := (hp.st_s.sub_left cP).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₉]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bP := by rw [esp₉]; exact hp.b_st.sub_right cP
    bSt := by rw [esp₉]; exact hp.b_o
    bS := by rw [esp₉]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fSt := fO
    fP := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₉, wr₉, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hstR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hstR s₀, by simp, 288, p288, by simp; omega⟩
    writes := by
      rw [wr₉, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishX86.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishX86.post s₀ s' := by
  have hp := HPre.of h0
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have hh₂ : hH s₀ ≤ 16 := held_le _
  have fS₂ : (hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  unfold finish
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call h₁.args) fun s₂ h₂ => ?_)
  have f₂ : Frame [hoR s₀, ⟨(hSc s₀).setWidth 64, 2176⟩, below (hE s₀) 56] s₁.mem s₂.mem := by
    have := h₂.frame; rw [h₁.esp] at this; exact this
  have F₂ : Frame (HBig s₀) s₀.mem s₂.mem := (h₁.mem ▸ hMem_frame hp).trans (f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₂.mem.readW ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have sub : Region.Sub ⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (hscR s₀) := Offset.sub_base _ (by omega)
    have c := Region.contains_self ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₂.readW c (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · exact hp.b_s.symm.sub_left sub) (by decide),
      h₁.mem, hMem, (writeBytes_frame _ _ _ (R := hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).readW c (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact hp.o_s.symm.sub_left sub) (by decide)]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 5) (Sc := hSc s₀) (by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hp.arg_in (by decide)) (hp.keep F₂ (by decide)) fS (by
      rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₃ ⟨hcs, m₃⟩ => ?_
  refine ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [m₃]
    refine F₂.readW (r := ⟨(hE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_o
    · exact hp.ret_s
    · exact ret_below e56
  · intro key msg hr hRk hc hlen
    show Spec.Aes.bytesAt s₃.mem ((hO s₀).setWidth 64) 16 = _
    rw [m₃]
    have hn : (countX86 s₀).toNat = msg.length := by
      rw [hc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen
    -- The state, unchanged before the call.
    have F₁ : Frame [⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩, hoR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem, hMem]
      exact ((savedMem_frame _ _).mono (by simp)).trans ((writeBytes_frame _ _ _ (R := hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).mono (by simp))
    have fSt' : ∀ {d n : Nat}, d + n ≤ 304 →
        Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      refine Proof.Cmac.bytesAt_frame F₁ (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by decide))
      · exact hp.st_o.sub_left (Offset.sub_base _ hd)
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := (Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr
    have hR' : hR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
    have hRb : 16 * (hR s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
    have hsch : Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64) (16 * (hR s₀ + 1)) = Spec.Aes.expandKey key := by
      have := fSt' (d := 0) (n := 16 * (hR s₀ + 1)) (by omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith (hR s₀) (Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64) (16 * (hR s₀ + 1))) =
        Spec.Cmac.aes key := by rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + 240) 32 =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 240) 32 := fSt' (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem ((hO s₀).setWidth 64) 16 =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 272) 16 := by
      rw [h₁.mem, hMem]
      have := bytesAt_writeBytes_self (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
        (xs := Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)
        (by rw [Proof.Cmac.bytesAt_length]; decide)
      rw [Proof.Cmac.bytesAt_length] at this
      rw [this]
      exact Proof.Cmac.bytesAt_frame (savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)
    have e₃ : Spec.Aes.bytesAt s₁.mem ((hSt s₀ + BitVec.ofNat 32 288).setWidth 64) (hH s₀) =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 288) (held msg.length) := by
      rw [add_setWidth (by omega), ← hn]; exact fSt' (by have := held_le (countX86 s₀).toNat; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish hr
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hH, hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

/-- What the call leaves. -/
structure HAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = hE s₀
  wr : s.wr = s₀.wr
  frame : Frame (HBig s₀) s₀.mem s.mem

theorem fin_after {s₀ s : State} (hp : HPre s₀) (h : HMid s₀ s) :
    WP isa (call6 "vg_cmac_aes_finalize" Impl.CmacAes.X86.finalize) s (HAft s₀) :=
  WP.mono (fin_call h.args) fun s' h' => by
    have fr := h'.frame
    rw [h.esp] at fr
    refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.wr, h.wr],
      (h.mem ▸ hMem_frame hp).trans (fr.sub fun r hr => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem finish_rel {s₀ s₀' : State} (h0 : finishX86.pre s₀) (h0' : finishX86.pre s₀')
    (hq : finishX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  have hp := HPre.of h0
  have hp' := HPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : hSt s₀ = hSt s₀' := qa 0 (by decide)
  have e1 : hR s₀ = hR s₀' := by rw [hR, hR, qa 1 (by decide)]
  have eH : hH s₀ = hH s₀' := by rw [hH, hH, countX86, countX86, qa 2 (by decide), qa 3 (by decide)]
  have e4 : hO s₀ = hO s₀' := qa 4 (by decide)
  have e5 : hSc s₀ = hSc s₀' := qa 5 (by decide)
  have ag : ∀ {a b : State}, Pt 6 s₀ a → Pt 6 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 6)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := finPre) (by taint_decide)).wp (F₁ := HMid s₀) (F₂ := HMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((fin_rel (E := hE s₀) (Q := fun a b => HMid s₀ a ∧ HMid s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, eH, e4, e5]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := HAft s₀) (F₂ := HAft s₀') fun _ _ h => ⟨fin_after hp h.1, fin_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun a b => HAft s₀ a ∧ HAft s₀' b) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => ag ⟨h.1.esp, h.1.wr, fun _ hi => hp.keep h.1.frame hi⟩
      ⟨h.2.esp, h.2.wr, fun _ hi => hp'.keep h.2.frame hi⟩) (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finish_ct : ConstantTime isa finishX86.pre finishX86.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86
