import VerifiedGarbage.Proof.CmacAes.AArch64.Update

/-!
# AES-CMAC on AArch64: the loop of `vg_cmac_aes_update`

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`x22` the next block, `x23` the blocks left), only the state and the first
2064 bytes of the scratch buffer have changed since the registers were saved,
and the state is the chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .x0
abbrev R : Nat := (s₀.gpr .x1).toNat
abbrev St : Addr := s₀.gpr .x2
abbrev Dp : Addr := s₀.gpr .x3
abbrev N : Nat := (s₀.gpr .x4).toNat
abbrev S : Addr := s₀.gpr .x5

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev stR : Region := ⟨St s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 16 (N s₀)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_wrap : (St s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateAArch64.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = St s₀
  x22 : s.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (St s₀) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    (⟨b + BitVec.ofNat 64 2064, 56⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 2064, 56⟩] s.mem (savedMem s) := by
  simp only [savedMem, saved, List.foldl]
  exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide)))

theorem advance_ok (s : State) :
    ∃ s', runBlock isa advance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 16 ∧ s'.gpr .x23 = s.gpr .x23 - 1 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [advance, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁, h₂]

theorem x1_ofNat (s₀ : State) : s₀.gpr .x1 = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## Memory outside the writable regions -/

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (W s₀) (16 * (R s₀ + 1)) = Spec.Aes.bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [stR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

end

/-! ## One block -/

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.chainMem s.mem (S s₀ + BitVec.ofNat 64 2048) (St s₀) (Dp s₀ + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, stR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega
  have hdw := hp.data_wrap
  have cSt0 : (stR s₀).Contains (St s₀) 8 := by
    simpa using Offset.contains_base (St s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  have cSt8 : (stR s₀).Contains (St s₀ + BitVec.ofNat 64 8) 8 := Offset.contains_base _ (by decide) (by decide)
  have cQ0 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  have cQ8 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have cC0 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048) 8 := Offset.contains_base _ (by decide) (by decide)
  have cC8 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    chainIn_ok s (C := S s₀ + BitVec.ofNat 64 2048) (P := St s₀) (Q := Dp s₀ + BitVec.ofNat 64 (16 * k))
      (by rw [h.x24]) h.x21 h.x22
      (by rw [hRegs]; exact in_rw (by simp) cSt0) (by rw [hRegs]; exact in_rw (by simp) cSt8)
      (by rw [hRegs]; exact in_rw (by simp) cQ0) (by rw [hRegs]; exact in_rw (by simp) cQ8)
      (by rw [hW]; exact in_rw (by simp) cC0) (by rw [hW]; exact in_rw (by simp) cC8)
      (by rw [hW]; exact in_rw (by simp) cSt0) (by rw [hW]; exact in_rw (by simp) cSt8)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have cDis : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
    Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  have pre : CallPre s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀) :=
    { x0 := by rw [x0₁, h.x19]
      x1 := by rw [x1₁, h.x20, x1_ofNat]
      x2 := x2₁
      x3 := x3₁
      x4 := x4₁
      x5 := by rw [x5₁, h.x24]
      rounds := hp.rounds
      wc := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
      wd := hp.sch_st
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
      cs := cDis
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hW]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₁]; exact Proof.Cmac.chainMem_state _ _ _ _ }
  exact ⟨pre, cs₁, sp₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) :
    WP isa (body v.callee) s fun s' => LInv s₀ (k + 1) s' := by
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega
  have hdw := hp.data_wrap
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v pre) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, x22₃, x23₃, keep₃, sp₃, mem₃, rd₃, wr₃⟩ := advance_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₃.gpr r = s.gpr r := by
    rw [keep₃ r h22 h23, h₂.saved r hr h30, cs₁ r hr]
  have x22₂ : s₂.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [h₂.saved .x22 (by simp [preserved]) (by decide), cs₁ .x22 (by simp [preserved]), h.x22]
  have x23₂ : s₂.gpr .x23 = BitVec.ofNat 64 (N s₀ - k) := by
    rw [h₂.saved .x23 (by simp [preserved]) (by decide), cs₁ .x23 (by simp [preserved]), h.x23]
  have hN := (s₀.gpr .x4).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact Proof.Cmac.chainMem_frame _ _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, Proof.Cmac.chainMem_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20]
  · rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21]
  · rw [x22₃, x22₂, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [x23₃, x23₂, dec]
  · rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24]
  · intro r hr h19 h20 h21 h22 h23 h24 h30
    rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]
  · rw [sp₃, h₂.sp, sp₁, h.sp]
  · rw [rd₃, h₂.rd, rd₁, h.rd]
  · rw [wr₃, h₂.wr, wr₁, h.wr]
  · rw [mem₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · rw [mem₃, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

end VG.Proof.CmacAes.AArch64
