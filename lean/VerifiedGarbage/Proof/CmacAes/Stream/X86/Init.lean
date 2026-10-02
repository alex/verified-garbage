import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_init`

Untrusted: everything here is checked by Lean. The code saves the
registers in the scratch buffer, expands the key into the state, derives
the subkeys after the schedule, zeroes the chaining value and restores the
registers: the state then represents the empty message. The code between
the calls is constant time by the taint analysis (from `esp` and the stack
arguments), and the calls by their own proofs (`ek_rel`, `sub_rel`), their
arguments pinned by `IMid₁` and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_addi wp_shr)
open VG.Proof.CmacAes.X86 (wp_arg zero4_ok saveMem_congr)

section
variable (s₀ : State)

abbrev iSt : BitVec 32 := arg s₀ 0
abbrev iKp : BitVec 32 := arg s₀ 1
abbrev iKL : Nat := (arg s₀ 2).toNat
abbrev iSc : BitVec 32 := arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev istR : Region := ⟨(iSt s₀).setWidth 64, 304⟩
abbrev ikR : Region := ⟨(iKp s₀).setWidth 64, iKL s₀⟩
abbrev iscR : Region := ⟨(iSc s₀).setWidth 64, 2304⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev IBig : List Region := [istR s₀, iscR s₀, below (iE s₀) 48]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikR s₀, iaR s₀]
  wr : s₀.wr = [istR s₀, iscR s₀]
  st_k : (istR s₀).Disjoint (ikR s₀)
  st_s : (istR s₀).Disjoint (iscR s₀)
  k_s : (ikR s₀).Disjoint (iscR s₀)
  a_st : (iaR s₀).Disjoint (istR s₀)
  a_s : (iaR s₀).Disjoint (iscR s₀)
  ret_st : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (istR s₀)
  ret_s : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (iscR s₀)
  b_st' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (istR s₀)
  b_k' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (ikR s₀)
  b_s' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (iscR s₀)
  fSt : (iSt s₀).toNat + 304 ≤ 2 ^ 32
  fK : (iKp s₀).toNat + iKL s₀ ≤ 2 ^ 32
  fS : (iSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp48 : 48 ≤ (iE s₀).toNat
  espfit : (iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : iKL s₀ = 16 ∨ iKL s₀ = 24 ∨ iKL s₀ = 32

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace IPre
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem b_st : (below (iE s₀) 48).Disjoint (istR s₀) := by rw [below_eq hp.esp48]; exact hp.b_st'
theorem b_k : (below (iE s₀) 48).Disjoint (ikR s₀) := by rw [below_eq hp.esp48]; exact hp.b_k'
theorem b_s : (below (iE s₀) 48).Disjoint (iscR s₀) := by rw [below_eq hp.esp48]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨iaR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp48).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end IPre

theorem IPre.savedMem_big {s₀ : State} (_hp : IPre s₀) : Frame (IBig s₀) s₀.mem (savedMem s₀ (iSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the first call -/

theorem initPre_eq : initPre = .mov .eax (argOp 3) :: (save ++ ([.mov .eax (argOp 1), .mov .ecx (argOp 2),
    .mov .edx (argOp 0), .mov .ebx (argOp 3)] : List Instr)) := rfl

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : EArgs s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀)
  esp : s.gpr .esp = iE s₀
  mem : s.mem = savedMem s₀ (iSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa (.block initPre) s₀ (IMid₁ s₀) := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e48 := hp.esp48
  rw [initPre_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := iSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = savedMem s₀ (iSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = iE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 1 (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 2 (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 0 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have esp₆ : s₆.gpr .esp = iE s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']
  have b20 : Region.Sub (below (iE s₀) 20) (below (iE s₀) 48) := below_sub (by decide) e48
  refine ⟨?_, esp₆, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], rd₆, wr₆⟩
  exact
  { eax := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    ecx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact arg_ofNat s₀ 2
    edx := by rw [u₆.other _ (by decide), u₅.gpr]
    ebx := u₆.gpr
    klen := hp.klen
    esp := by rw [esp₆]; omega
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₆]; exact hp.b_k.sub_left b20
    bW := by rw [esp₆]; exact (hp.b_st.sub_left b20).sub_right (Region.sub_prefix (by decide))
    bS := by rw [esp₆]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := hp.fK
    fW := by omega
    fS := by omega
    reads := by
      rw [rd₆, wr₆, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ikR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₆, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After a call -/

/-- What is known after each call. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (IBig s₀) s₀.mem s.mem

theorem IAft.pt {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem IMid₁.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₁ s₀ s)
    (h' : EPost s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.savedMem_big.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨istR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) hp.esp48⟩

theorem ek_after {s₀ s : State} (hp : IPre s₀) (h : IMid₁ s₀ s) :
    WP isa (call4 "vg_aes_expand_key" Impl.Aes.X86.expandKey) s (IAft s₀) :=
  WP.mono (ek_call h.args) fun _ h' => h.after hp h'

/-! ## Between the calls -/

theorem rounds32 {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 32 KL >>> 2 + 6 = BitVec.ofNat 32 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ s : State) : Prop where
  args : SArgs s (iSt s₀) (iSt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 4 + 6)
  aft : IAft s₀ s

theorem initMid_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initMid) s fun s' => IMid₂ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e48 := hp.esp48
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.keep h.frame hi
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact av 2 (by decide))
    fun s₂ u₂ => ?_
  refine wp_shr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have kSt : Region.Sub ⟨(iSt s₀ + BitVec.ofNat 32 240).setWidth 64, 32⟩ (istR s₀) := by
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  have hR : iKL s₀ / 4 + 6 = 10 ∨ iKL s₀ / 4 + 6 = 12 ∨ iKL s₀ / 4 + 6 = 14 := by
    rcases hp.klen with h | h | h <;> rw [h] <;> decide
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        arg_ofNat s₀ 2]
      exact rounds32 hp.klen
    edx := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; rfl
    ebx := u₇.gpr
    rounds := hR
    esp := by rw [esp₇]; exact e48
    wk := by
      rw [add_setWidth (by omega)]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    bW := by rw [esp₇]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact hp.b_st.sub_right kSt
    bS := by rw [esp₇]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fK := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 240, add_setWidth (by omega), by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₂.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₂ s₀ s)
    (h' : SPost s (iSt s₀) (iSt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 4 + 6) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fSt := hp.fSt
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨istR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 48, by simp, fun _ h => h⟩

theorem sub_after {s₀ s : State} (hp : IPre s₀) (h : IMid₂ s₀ s) :
    WP isa (call4 "vg_cmac_aes_subkeys" Impl.CmacAes.X86.subkeys) s (IAft s₀) :=
  WP.mono (sub_call h.args) fun _ h' => h.after hp h'

/-! ## After the calls -/

theorem initPost_eq : initPost = .mov .edx (argOp 0) :: (Impl.CmacAes.X86.zero4 .edx 272 ++ restore 3) := rfl

/-- The chaining value zeroed, and the registers restored from their slots. -/
theorem initPost_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s)
    (hs : ∀ r d, (r, d) ∈ saved → s.mem.readW ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r) :
    WP isa (.block initPost) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = Proof.Cmac.zero4 s.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 272) := by
  have fS : (arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  rw [initPost_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (hp.keep h.frame (by decide))
    fun s₁ u₁ => ?_
  refine zero4_ok (by decide) (by rw [u₁.gpr]; omega) (by
      rw [u₁.wr, h.wr, hp.wr, u₁.gpr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, 272, rfl, by simp⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  have hz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem, u₁.gpr]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (restore_wp (s₀ := s₀) (i := 3) (Sc := iSc s₀) (by rw [g₂ _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by
      rw [hz.readW (r := ⟨argAddr s₀ 3, 4⟩) (Region.contains_self _ _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact (hp.a_st.sub_left (arg_sub hp.fit (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
      exact hp.keep h.frame (by decide))
    fS (by
      rw [rd₂, wr₂, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    fun r d hrd => ?_) fun s' ⟨hcs, hm⟩ => ⟨hcs, by rw [hm, m₂, u₁.mem, u₁.gpr]⟩
  have hb := saved_bound _ hrd
  rw [hz.readW (r := ⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Offset.sub_base _ (by omega)))
    (by decide)]
  exact hs r d hrd

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fS : (arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have e48 := hp.esp48
  unfold init
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.seq (WP.mono (initMid_wp hp a₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call h₃.args) fun s₄ h₄ => ?_)
  have a₄ := h₃.after hp h₄
  have f₂ : Frame [⟨(iSt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩, below (iE s₀) 48] s₁.mem s₂.mem := by
    have := h₂.frame
    rw [h₁.esp] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 48, by simp, below_sub (by decide) e48⟩
  have f₄ : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩,
      below (iE s₀) 48] s₂.mem s₄.mem := by
    have := h₄.frame; rw [h₃.aft.esp, m₃, add_setWidth (by omega)] at this; exact this
  -- The saved registers.
  have dSlot : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → ∀ r ∈ [⟨(iSt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩,
      below (iE s₀) 48, ⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩],
      (⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
    have sub : Region.Sub ⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (iscR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have slots : ∀ r d, (r, d) ∈ saved →
      s₄.mem.readW ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have c := Region.contains_self ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₄.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₂.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide), h₁.mem]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (initPost_wp hp a₄ slots) fun s₅ ⟨hcs, m₅⟩ => ?_
  have fz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have F₅ : Frame (IBig s₀) s₀.mem s₅.mem := a₄.frame.trans (fz.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨hcs, F₅.readW (r := ⟨(iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_s
    · exact ret_below e48
  · show Spec.Cmac.Repr s₅.mem ((iSt s₀).setWidth 64) (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) []
    rw [Proof.Cmac.Stream.repr_iff]
    have hlen : (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)).length = iKL s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have hkey : Spec.Aes.bytesAt s₁.mem ((iKp s₀).setWidth 64) (iKL s₀) =
        Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀) := by
      rw [h₁.mem]
      exact Proof.Cmac.bytesAt_frame (savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base _ (by decide))) (by have := hp.fK; omega)
    have dz : ∀ {d n : Nat}, d + n ≤ 272 →
        ∀ r ∈ [(⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩ : Region)],
          (⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := fun {d n} hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 →
        Spec.Aes.bytesAt s₅.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₂.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dz (by omega)) (by omega), Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right (Offset.sub_base _ (by omega))).symm) (by omega)]
    have hRb : 16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega
    have hsch : Spec.Aes.bytesAt s₂.mem ((iSt s₀).setWidth 64) (16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) := by rw [h₂.out, hkey]
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
          Spec.Aes.bytesAt s₄.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 :=
        Proof.Cmac.bytesAt_frame fz (dz (d := 240) (n := 32) (by omega)) (by decide)
      rw [show (iSt s₀).setWidth 64 + 240 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 240 from rfl, e]
      have o := h₄.out
      rw [add_setWidth (by omega), m₃, show iKL s₀ / 4 + 6 = Spec.Aes.rounds (iKL s₀ / 4) from rfl, hsch] at o
      rw [o]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅]; exact (Proof.Cmac.zero4_bytes _ _).trans rfl

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀') (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : iSt s₀ = iSt s₀' := qa 0 (by decide)
  have e1 : iKp s₀ = iKp s₀' := qa 1 (by decide)
  have e2 : iKL s₀ = iKL s₀' := by rw [iKL, iKL, qa 2 (by decide)]
  have e3 : iSc s₀ = iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := IMid₁ s₀) (F₂ := IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((ek_rel (E := iE s₀) (P := fun a b => IMid₁ s₀ a ∧ IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨ek_after hp h.1, ek_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid) (by taint_decide)).wp
    (F₁ := fun s => IMid₂ s₀ s) (F₂ := fun s => IMid₂ s₀' s)
    fun _ _ h => ⟨WP.mono (initMid_wp hp h.1) fun _ h => h.1, WP.mono (initMid_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have sk := ((sub_rel (E := iE s₀) (P := fun a b => IMid₂ s₀ a ∧ IMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨sub_after hp h.1, sub_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initPost) (by taint_decide)
  exact a.seq (e.seq (m.seq (sk.seq p)))

theorem init_ct : ConstantTime isa initX86.pre initX86.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86
