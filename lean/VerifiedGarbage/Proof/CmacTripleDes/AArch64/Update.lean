import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): `x2` points to the next block, `x3` holds the blocks left,
only the state and the block's slots have changed, and the state is the
chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes VG.Proof.Cmac

theorem rev64_eq (x : BitVec 64) : rev64 x = byteRev64 x := rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .x0
abbrev St : Addr := s₀.gpr .x1
abbrev Dp : Addr := s₀.gpr .x2
abbrev N : Nat := (s₀.gpr .x3).toNat
abbrev S : Addr := s₀.gpr .x4

abbrev schR : Region := ⟨W s₀, 384⟩
abbrev stR : Region := ⟨St s₀, 8⟩
abbrev dataR : Region := ⟨Dp s₀, 8 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 640⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 8 (N s₀)

/-- What changes. -/
abbrev chg : List Region := [stR s₀, ⟨S s₀, 48⟩]

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
  st_wrap : (St s₀).toNat + 8 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 8 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 640 ≤ 2 ^ 64

theorem UPre.of {s₀ : State} (h : updateAArch64.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W s₀
  x15 : s.gpr .x15 = S s₀
  x1 : s.gpr .x1 = St s₀
  x2 : s.gpr .x2 = Dp s₀ + BitVec.ofNat 64 (8 * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (chg s₀) s₀.mem s.mem
  state : Spec.Aes.bytesAt s.mem (St s₀) 8 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 8) ((blks s₀).take k)

/-! ## The blocks of straight-line code -/

theorem chainIn_ok (s : State) {P Q : Addr} (hp : s.gpr .x1 = P) (hq : s.gpr .x2 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa chainIn s = some s' ∧
      s'.gpr .x5 = byteRev64 (s.mem.readW P 64 ^^^ s.mem.readW Q 64) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rp' : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8 := by rw [add_ofNat_zero, hp]; exact rp
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64)
  have rq' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hq]; exact rq
  refine ⟨_, by
    rw [chainIn, runBlock_cons, exec_ldr_x (by decide) rp', runStep_some, runBlock_cons, exec_ldr_x (by decide) rq',
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil],
    ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [s₁, State.read, gpr_write, mem_write, ite_true, ite_false,
      BitVec.setWidth_eq, rev64_eq, add_ofNat_zero, hp, hq]
  · simp [s₁, gpr_write, h₁, h₂]

theorem chainOut_ok (s : State) {P : Addr} (hp : s.gpr .x1 = P) (wp : InRegions s.wr P 8) :
    ∃ s', runBlock isa chainOut s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧ s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x5] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW P (byteRev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have wp' : InRegions s₁.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hp]; exact wp
  refine ⟨_, by
    rw [chainOut, runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) wp',
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
  · simp [s₁, gpr_write, State.read]
  · simp [s₁, gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₁, gpr_write, hr.1, hr.2.1, hr.2.2]
  · simp (config := {decide := true}) only [s₁, mem_write, State.read, gpr_write, ite_true, ite_false,
      BitVec.setWidth_eq, rev64_eq, hp, add_ofNat_zero]

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (8 * k), 8⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.sched {hp : UPre s₀} {m : Mem} (hf : Frame (chg s₀) s₀.mem m) :
    Spec.TripleDes.scheduleAt m (W s₀) = Spec.TripleDes.scheduleAt s₀.mem (W s₀) :=
  scheduleAt_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.data {hp : UPre s₀} {m : Mem} (hf : Frame (chg s₀) s₀.mem m) {k : Nat}
    (hk : k < N s₀) :
    Spec.Aes.bytesAt m (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.data_sub hk)
    · exact (hp.data_scr.sub_right (Region.sub_prefix (by decide))).sub_left (UPre.data_sub hk))
    (by decide)

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {hp : UPre s₀} {s : State} (h14 : s.gpr .x14 = W s₀) (h15 : s.gpr .x15 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨schR s₀, by rw [hrd, hwr, hp.rd]; simp, by rw [h14], Nat.le_refl _, by show 384 < 2 ^ 64; decide⟩
  scr := ⟨scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
  disj := by
    rw [h14, h15]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem x2_succ (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa updBody s (LInv s₀ (k + 1)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hdw := hp.data_wrap
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, stR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₁, h₁, ax₁, k₁, sp₁, m₁, rd₁, wr₁⟩ := chainIn_ok s (P := St s₀)
    (Q := Dp s₀ + BitVec.ofNat 64 (8 * k)) h.x1 h.x2
    (by rw [rdwr]; exact in_rw (r := stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [rdwr]; exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  refine WP.seq (WP.of_runBlock ⟨s₁, h₁, ?_⟩)
  have x14₁ : s₁.gpr .x14 = W s₀ := by rw [k₁ _ (by decide) (by decide), h.x14]
  have x15₁ : s₁.gpr .x15 = S s₀ := by rw [k₁ _ (by decide) (by decide), h.x15]
  have bp : BlockPre s₁ := UPre.block (hp := hp) x14₁ x15₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  refine WP.seq (WP.mono (block_ok bp) fun s₂ ⟨same₂, x14₂, ax₂⟩ => ?_)
  have xR₁ : xR s₁ = ⟨S s₀, 48⟩ := by rw [xR, x15₁]
  have f₂ : Frame [⟨S s₀, 48⟩] s.mem s₂.mem := by rw [← m₁, ← xR₁]; exact same₂.frame
  have wr₂ : s₂.wr = [stR s₀, scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have x1₂ : s₂.gpr .x1 = St s₀ := by
    rw [same₂.keep .x1 (by simp [outer]), k₁ _ (by decide) (by decide), h.x1]
  obtain ⟨s₃, h₃, x2₃, x3₃, k₃, m₃, sp₃, rd₃, wr₃⟩ := chainOut_ok s₂ (P := St s₀) x1₂
    (by rw [wr₂]; exact in_rw (r := stR s₀) (by simp) (Region.contains_self _ _))
  have hS : sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (W s₀) := by
    rw [sch, x14₁, m₁]; exact UPre.sched (hp := hp) h.frame
  have hD := UPre.data (hp := hp) h.frame hk
  refine WP.of_runBlock ⟨s₃, h₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [k₃ _ (by decide), x14₂, x14₁]
  · rw [k₃ _ (by decide), same₂.x15, x15₁]
  · rw [k₃ _ (by decide), x1₂]
  · rw [x2₃, same₂.keep .x2 (by simp [outer]), k₁ _ (by decide) (by decide), h.x2, x2_succ]
  · rw [x3₃, same₂.keep .x3 (by simp [outer]), k₁ _ (by decide) (by decide), h.x3,
      show BitVec.ofNat 64 1 = 1 from rfl, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [sp₃, same₂.sp, sp₁, h.sp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · rw [m₃]
    exact (h.frame.trans (f₂.mono fun r hr => by simp at hr; simp [hr])).writeW (r := stR s₀) (by simp) _
      (by simpa using Region.contains_self (St s₀) 8)
  · rw [m₃, ← le8_readW, Mem.readW_writeW_self64, ax₂, ax₁, ← tdesWith_le8, hS, le8_xor, le8_readW, le8_readW,
      h.state, hD, take_succ_blks s₀ hk, chain_append, chain_single]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop updBody (.nonzero .x .x3)) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .nonzero .x .x3) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have ev := eval_nonzero (r := .x3) (x := N s₀ - (k + 1)) (by omega) h'.x3
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem x3_ofNat (s₀ : State) : s₀.gpr .x3 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem prologue_wp {s₀ : State} :
    WP isa (.block [mov .x14 .x0, mov .x15 .x4]) s₀ (LInv s₀ 0) := by
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp only [gpr_write]; rw [x3_ofNat]; rfl, rfl, rfl, rfl, Frame.refl _ _,
    by simp only [mem_write, List.take_zero]; rfl⟩

theorem update_wp {s₀ : State} (h0 : updateAArch64.pre s₀) :
    WP isa update s₀ fun s' => updateAArch64.post s₀ s' := by
  have hp := UPre.of h0
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  refine WP.seq (WP.mono prologue_wp fun s₁ h₁ => ?_)
  have fin : ∀ s, LInv s₀ (N s₀) s → updateAArch64.post s₀ s := fun s h => by
    show Spec.Aes.bytesAt s.mem (St s₀) 8 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]
  have ev := eval_zero (r := .x3) (x := N s₀) hN (by rw [h₁.x3]; rfl)
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil (fin _ ?_)) (fun h => by cases h)
    rw [hn]; exact h₁
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact WP.mono (loop_ok hp (by omega) h₁) fin

end VG.Proof.CmacTripleDes.AArch64
