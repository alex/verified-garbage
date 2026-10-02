import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Save
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): slot 12 points to the next block, slot 13 holds the blocks
left, only the state, the block's slots and slots 12–13 have changed since
the registers were saved, and the state is the chaining value after the
first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

theorem bswap64_eq (x : BitVec 64) : bswap64 x = byteRev64 x := rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .rdi
abbrev St : Addr := s₀.gpr .rsi
abbrev Dp : Addr := s₀.gpr .rdx
abbrev N : Nat := (s₀.gpr .rcx).toNat
abbrev S : Addr := s₀.gpr .r8

abbrev schR : Region := ⟨W s₀, 384⟩
abbrev stR : Region := ⟨St s₀, 8⟩
abbrev dataR : Region := ⟨Dp s₀, 8 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 640⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 8 (N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region := [stR s₀, ⟨S s₀, 48⟩, ⟨S s₀ + BitVec.ofNat 64 96, 16⟩]

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
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (stR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  st_wrap : (St s₀).toNat + 8 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 8 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 640 ≤ 2 ^ 64

theorem UPre.of {s₀ : State} (h : updateX86_64.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = S s₀
  rbp : s.gpr .rbp = St s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW (S s₀ + BitVec.ofNat 64 96) 64 = Dp s₀ + BitVec.ofNat 64 (8 * k)
  left : s.mem.readW (S s₀ + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 (N s₀ - k)
  frame : Frame (chg s₀) (savedMem s₀ (S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem (St s₀) 8 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 8) ((blks s₀).take k)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## The blocks of straight-line code -/

theorem prologue_ok (s : State)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa updPre s = some s' ∧
      s'.gpr .r15 = s.gpr .r8 ∧ s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rcx == 0) ∧
      s'.mem = ((savedMem s (s.gpr .r8)).writeW (s.gpr .r8 + BitVec.ofNat 64 96) (s.gpr .rdx)).writeW
        (s.gpr .r8 + BitVec.ofNat 64 104) (s.gpr .rcx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := save_ok s .r8 fun d h₁ h₂ => hw d h₁ (by omega)
  have hw' : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s₁.wr (s₁.gpr .r8 + BitVec.ofNat 64 d) 8 := by
    rw [g₁, wr₁]; exact hw
  refine ⟨_, by
    rw [updPre, runBlock_append, h₁, Option.bind_some]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      hw' 96 (by decide) (by decide), hw' 104 (by decide) (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, 
    mem_arithFlags, rd_arithFlags, wr_arithFlags, ite_true, ite_false,
    BitVec.and_self, g₁, m₁, rd₁, wr₁]

theorem chainIn_ok (s : State) {P Q : Addr} (hp : s.gpr .rbp = P)
    (hq : s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 = Q)
    (r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa chainIn s = some s' ∧
      s'.gpr .rax = byteRev64 (s.mem.readW P 64 ^^^ s.mem.readW Q 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [chainIn, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hp, hq, BitVec.add_zero, r96, rp, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, bswap64_eq]
  · simp [gpr_setReg, h₁, h₂]

theorem chainOut_ok (s : State) {P : Addr} (hp : s.gpr .rbp = P)
    (wp : InRegions s.wr P 8) (w96 : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 96) 8)
    (w104 : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 104) 8)
    (sep96 : Mem.Sep (s.gpr .r15 + BitVec.ofNat 64 96) 8 P 8)
    (sep104 : Mem.Sep (s.gpr .r15 + BitVec.ofNat 64 104) 8 P 8) :
    ∃ s', runBlock isa chainOut s = some s' ∧
      s'.zf = some ((s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rax, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = (((s.mem.writeW P (byteRev64 (s.gpr .rax))).writeW (s.gpr .r15 + BitVec.ofNat 64 96)
        (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 + BitVec.ofNat 64 8)).writeW
        (s.gpr .r15 + BitVec.ofNat 64 104) (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 - 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8 := by
    obtain ⟨r, hr, hc⟩ := w96; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have r104 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 104) 8 := by
    obtain ⟨r, hr, hc⟩ := w104; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have h96 : (s.mem.writeW P (byteRev64 (s.gpr .rax))).readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 =
      s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 := Mem.readW_writeW_sep sep96 (by decide)
  have h104 : ((s.mem.writeW P (byteRev64 (s.gpr .rax))).writeW (s.gpr .r15 + BitVec.ofNat 64 96)
      (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 + BitVec.ofNat 64 8)).readW
        (s.gpr .r15 + BitVec.ofNat 64 104) 64 = s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 := by
    rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_sep sep104 (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [chainOut, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, ite_false, hp, BitVec.add_zero, r96, r104, wp, w96, w104, h96, h104, bswap64_eq,
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2]

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (8 * k), 8⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

/-- Everything that changes, from the entry state on. -/
theorem UPre.big {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    Frame [stR s₀, scrR s₀] s₀.mem m :=
  ((savedMem_frame s₀ (S s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩).trans
  (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)

theorem UPre.sched {hp : UPre s₀} {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    Spec.TripleDes.scheduleAt m (W s₀) = Spec.TripleDes.scheduleAt s₀.mem (W s₀) :=
  scheduleAt_frame (UPre.big hf) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr

theorem UPre.data {hp : UPre s₀} {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {k : Nat}
    (hk : k < N s₀) :
    Spec.Aes.bytesAt m (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  bytesAt_frame (UPre.big hf) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.data_sub hk)
    · exact hp.data_scr.sub_left (UPre.data_sub hk)) (by decide)

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {hp : UPre s₀} {s : State} (h14 : s.gpr .r14 = W s₀) (h15 : s.gpr .r15 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨schR s₀, by rw [hrd, hp.rd]; simp, by rw [h14], Nat.le_refl _, by show 384 < 2 ^ 64; decide⟩
  scr := ⟨scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
  disj := by
    rw [h14, h15]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem rbp_succ (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa updBody s fun s' => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hsw := hp.scr_wrap
  have hdw := hp.data_wrap
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, stR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8 := by
    rw [rdwr, h.r15]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  obtain ⟨s₁, h₁, ax₁, k₁, m₁, rd₁, wr₁⟩ := chainIn_ok s (P := St s₀)
    (Q := Dp s₀ + BitVec.ofNat 64 (8 * k)) h.rbp (by rw [h.r15, h.dp]) r96
    (by rw [rdwr]; exact in_rw (r := stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [rdwr]; exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  refine WP.seq (WP.of_runBlock ⟨s₁, h₁, ?_⟩)
  have r14₁ : s₁.gpr .r14 = W s₀ := by rw [k₁ _ (by decide) (by decide), h.r14]
  have r15₁ : s₁.gpr .r15 = S s₀ := by rw [k₁ _ (by decide) (by decide), h.r15]
  have bp : BlockPre s₁ := UPre.block (hp := hp) r14₁ r15₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  refine WP.seq (WP.mono (block_ok bp) fun s₂ ⟨same₂, r14₂, ax₂⟩ => ?_)
  have xR₁ : xR s₁ = ⟨S s₀, 48⟩ := by rw [xR, r15₁]
  have f₂ : Frame [⟨S s₀, 48⟩] s.mem s₂.mem := by rw [← m₁, ← xR₁]; exact same₂.frame
  have r15₂ : s₂.gpr .r15 = S s₀ := by rw [same₂.r15, r15₁]
  have slot₂ : ∀ d, 48 ≤ d → d + 8 ≤ 640 →
      s₂.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨S s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, dataR s₀, stR s₀, scrR s₀] := by
    rw [same₂.rd, same₂.wr, rd₁, wr₁, rdwr]
  have wr₂ : s₂.wr = [stR s₀, scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have sep : Mem.Sep (S s₀ + BitVec.ofNat 64 104) 8 (St s₀) 8 :=
    (hp.st_scr.symm.sub_left (UPre.scr_sub (d := 104) (n := 8) (by decide))).sep (Region.contains_self _ _)
      (Region.contains_self _ _)
  have sep96 : Mem.Sep (S s₀ + BitVec.ofNat 64 96) 8 (St s₀) 8 :=
    (hp.st_scr.symm.sub_left (UPre.scr_sub (d := 96) (n := 8) (by decide))).sep (Region.contains_self _ _)
      (Region.contains_self _ _)
  have rbp₂ : s₂.gpr .rbp = St s₀ := by rw [same₂.rbp, k₁ _ (by decide) (by decide), h.rbp]
  obtain ⟨s₃, h₃, zf₃, k₃, m₃, rd₃, wr₃⟩ := chainOut_ok s₂ (P := St s₀) rbp₂
    (by rw [wr₂]; exact in_rw (r := stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [wr₂, r15₂]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (by rw [wr₂, r15₂]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (by rw [r15₂]; exact sep96) (by rw [r15₂]; exact sep)
  rw [r15₂] at m₃ zf₃
  rw [slot₂ 96 (by decide) (by decide), slot₂ 104 (by decide) (by decide), h.dp, h.left] at m₃
  rw [slot₂ 104 (by decide) (by decide), h.left] at zf₃
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) :=
    ofNat_sub_one (by omega) (by omega)
  rw [dec] at m₃ zf₃
  -- The state's new value.
  have big : Frame [stR s₀, scrR s₀] s₀.mem s.mem := UPre.big h.frame
  have hS : sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (W s₀) := by
    rw [sch, r14₁, m₁]; exact UPre.sched (hp := hp) h.frame
  have hD := UPre.data (hp := hp) h.frame hk
  refine WP.of_runBlock ⟨s₃, h₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k₃ _ (by decide), r14₂, r14₁]
  · rw [k₃ _ (by decide), r15₂]
  · rw [k₃ _ (by decide), rbp₂]
  · rw [k₃ _ (by decide), same₂.rsp, k₁ _ (by decide) (by decide), h.rsp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · rw [m₃, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, rbp_succ]
  · rw [m₃, Mem.readW_writeW_self64]
  · have c96 : (⟨S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (S s₀ + BitVec.ofNat 64 96) (64 / 8) := by
      have := Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    have c104 : (⟨S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (S s₀ + BitVec.ofNat 64 104) (64 / 8) := by
      rw [show S s₀ + BitVec.ofNat 64 104 = S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₃]
    exact (((h.frame.trans (f₂.mono fun r hr => by simp at hr; simp [hr])).writeW (r := stR s₀) (by simp) _
      (by simpa using Region.contains_self (St s₀) 8)).writeW (r := ⟨S s₀ + BitVec.ofNat 64 96, 16⟩)
        (by simp) _ c96).writeW (r := ⟨S s₀ + BitVec.ofNat 64 96, 16⟩) (by simp) _ c104
  · have c96 : (⟨S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (S s₀ + BitVec.ofNat 64 96) (64 / 8) := by
      have := Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    have c104 : (⟨S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (S s₀ + BitVec.ofNat 64 104) (64 / 8) := by
      rw [show S s₀ + BitVec.ofNat 64 104 = S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₃, bytesAt_frame (rs := [⟨S s₀ + BitVec.ofNat 64 96, 16⟩])
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _ c104)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (d := 96) (n := 16) (by decide))) (by decide),
      ← le8_readW, Mem.readW_writeW_self64, ax₂, ax₁, ← tdesWith_le8, hS, le8_xor, le8_readW, le8_readW,
      h.state, hD, take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [zf₃, ofNat_beq_zero (by omega)]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop updBody .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [X86_64.eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem rcx_ofNat (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block updPre) s₀ fun s₁ => LInv s₀ 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hsw := hp.scr_wrap
  obtain ⟨s₁, run₁, r15₁, r14₁, rbp₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  have f96 : Frame [⟨S s₀ + BitVec.ofNat 64 96, 16⟩] (savedMem s₀ (S s₀)) s₁.mem := by
    have c0 : (⟨S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (S s₀ + BitVec.ofNat 64 96) 8 := by
      have := Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    rw [mem₁]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ ?_
    rw [show S s₀ + BitVec.ofNat 64 104 = S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base (S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ⟨r14₁, r15₁, rbp₁, rsp₁, rd₁, wr₁, ?_, ?_,
    f96.mono fun r hr => by simp at hr; simp [hr], ?_⟩, ?_⟩
  · rw [mem₁, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; simp
  · rw [mem₁, Mem.readW_writeW_self64, rcx_ofNat]; rfl
  · rw [bytesAt_frame (f96 : Frame _ (savedMem s₀ (S s₀)) s₁.mem) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))) (by decide),
      bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))) (by decide)]
    rfl
  · rw [zf₁, rcx_ofNat, ofNat_beq_zero hN]

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop updBody .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 96) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀ (S s₀)).readW (S s₀ + BitVec.ofNat 64 d) 64 := by
  have hsw := hp.scr_wrap
  refine hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.st_scr.sub_right (UPre.scr_sub (by omega))).symm
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hsw := hp.scr_wrap
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, b, c, d, e, f, g, rsp₃, mem₃⟩ := restore_ok s₂ h₂.r15 fun d _ h₂' => by
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, run₃, ⟨restored (slot_read hp h₂.frame) ⟨b, c, d, e, f, g⟩
    (by rw [rsp₃, h₂.rsp]), ?_⟩, ?_⟩
  · rw [mem₃]
    refine (UPre.big h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
  · show Spec.Aes.bytesAt s₃.mem (St s₀) 8 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateX86_64.pre s₀) :
    WP isa update s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.X86_64
