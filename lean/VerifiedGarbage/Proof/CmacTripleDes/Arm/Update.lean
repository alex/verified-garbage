import VerifiedGarbage.Proof.CmacTripleDes.Arm.Save
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): words 28–30 of the scratch buffer hold the state pointer,
the next block and the blocks left, only the state, the block's words and
those three have changed since the registers were saved, and the state is
the chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldrSp wp_ldr
  wp_str wp_rev saveMem saveList_ok cmp0 ofNat_beq_zero)

theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

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

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev St : BitVec 32 := s₀.gpr .r1
abbrev Dp : BitVec 32 := s₀.gpr .r2
abbrev N : Nat := (s₀.gpr .r3).toNat
abbrev S : BitVec 32 := stackArg s₀ 0

abbrev schR : Region := ⟨State.addr (W s₀), 384⟩
abbrev stR : Region := ⟨State.addr (St s₀), 8⟩
abbrev dataR : Region := ⟨State.addr (Dp s₀), 8 * N s₀⟩
abbrev scrR : Region := ⟨State.addr (S s₀), 640⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 4⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (State.addr (W s₀))

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (Dp s₀)) 8 (N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region :=
  [stR s₀, ⟨State.addr (S s₀), 52⟩, ⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  sch_fit : (W s₀).toNat + 384 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 8 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 8 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = W s₀
  r10 : s.gpr .r10 = S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 112) 32 = St s₀
  dp : s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 116) 32 = Dp s₀ + BitVec.ofNat 32 (8 * k)
  left : s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 120) 32 = BitVec.ofNat 32 (N s₀ - k)
  frame : Frame (chg s₀) (savedMem s₀ (S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 8 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 8) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (S s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem UPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem UPre.sched {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    Spec.TripleDes.scheduleAt m (State.addr (W s₀)) = Spec.TripleDes.scheduleAt s₀.mem (State.addr (W s₀)) := by
  rw [scheduleAt_frame hf fun r hr => ?_]
  · exact scheduleAt_frame (savedMem_frame s₀ (S s₀)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))

theorem UPre.data {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k)) 8 := by
  have hsub : Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k), 8⟩ (dataR s₀) :=
    Offset.sub_base _ (by omega)
  rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]
  · exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_st.sub_left hsub
    · exact (hp.data_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {s : State} (h9 : s.gpr .r9 = W s₀) (h10 : s.gpr .r10 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨384, by rw [hrd, hwr, hp.rd, h9]; simp, Nat.le_refl _, by rw [h9]; exact hp.sch_fit⟩
  scr := ⟨640, by rw [hwr, hp.wr, h10]; simp, by decide, by rw [h10]; exact hp.scr_fit⟩
  disj := by
    rw [h9, h10]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-- The two words at `a` XORed, as a big-endian integer. -/
theorem rev_xor_append (a₀ a₁ b₀ b₁ : BitVec 32) :
    rev (a₀ ^^^ b₀) ++ rev (a₁ ^^^ b₁) = byteRev64 ((a₁ ++ a₀) ^^^ (b₁ ++ b₀)) := by
  rw [rev_eq, rev_eq, byteRev32_append, BitVec.xor_append]

theorem add0 (a : BitVec 32) : a + BitVec.ofNat 32 0 = a := BitVec.add_zero a

theorem readW_writeW_far (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  MdStream.Arm.readW_writeW_save m B v hd he h

theorem readW_writeW_far' (m : Mem) (a : Addr) (w : BitVec 32) :
    (m.writeW (a + BitVec.ofNat 64 4) w).readW a 32 = m.readW a 32 := by
  have := readW_writeW_far m a w (d := 0) (e := 4) (by decide) (by decide) (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

theorem readW_lo_of_hi (m : Mem) (a : Addr) (v w : BitVec 32) :
    ((m.writeW a v).writeW (a + BitVec.ofNat 64 4) w).readW a 32 = v := by
  have := readW_writeW_far' (m.writeW a v) a w
  rw [this, Mem.readW_writeW_self32]

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa updBody s fun s' => LInv s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hN : N s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  have hsf := hp.scr_fit
  have hdf := hp.data_fit
  have htf := hp.st_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have stA : State.addr (St s₀ + BitVec.ofNat 32 4) = State.addr (St s₀) + BitVec.ofNat 64 4 := addr_add (by omega)
  have dA : State.addr (Dp s₀ + BitVec.ofNat 32 (8 * k)) = State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k) :=
    addr_add (by omega)
  have dA4 : State.addr (Dp s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4) =
      State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 4 := by
    rw [Straight.add_ofNat_ofNat, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s.rd ++ s.wr) (State.addr (St s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have dIn : ∀ d, d + 4 ≤ 8 →
      InRegions (s.rd ++ s.wr) (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr, Offset.add_add]
      exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  -- `chainIn`.
  refine WP.seq (?_ : WP isa (.block chainIn) s _)
  simp only [chainIn]
  refine wp_ldr (by decide) (by rw [h.r10, hp.scrAddr (by decide)]) (scrIn 112 (by decide)) fun s₁ u₁ => ?_
  refine wp_ldr (by decide) (by rw [u₁.other _ (by decide), h.r10, hp.scrAddr (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact scrIn 116 (by decide)) fun s₂ u₂ => ?_
  have r4₂ : s₂.gpr .r4 = St s₀ := by rw [u₂.other _ (by decide), u₁.gpr, h.st]
  have r5₂ : s₂.gpr .r5 = Dp s₀ + BitVec.ofNat 32 (8 * k) := by rw [u₂.gpr, u₁.mem, h.dp]
  refine wp_ldr (by decide) (by rw [r4₂, add0])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (by rw [u₃.other _ (by decide), r4₂, stA])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_ldr (by decide) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r5₂, add0, dA])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa using dIn 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_ldr (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r5₂,
      dA4])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact dIn 4 (by decide))
    fun s₆ u₆ => ?_
  refine wp_eor (op2_reg _ _) fun s₇ u₇ => wp_eor (op2_reg _ _) fun s₈ u₈ => wp_rev fun s₉ u₉ =>
    wp_rev fun s₁₀ u₁₀ => WP.block_nil ?_
  -- What `chainIn` leaves.
  have g₁₀ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3, .r4, .r5] → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other _ hr.2.1, u₉.other _ hr.1, u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.2.1,
      u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2.2.2.2,
      u₁.other _ hr.2.2.2.2.1]
  have m₁₀ : s₁₀.mem = s.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₁₀ : s₁₀.rd = s.rd := by
    rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₁₀ : s₁₀.sp = s.sp := by
    rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have ax₁₀ : s₁₀.gpr .r0 ++ s₁₀.gpr .r1 = byteRev64 (s.mem.readW (State.addr (St s₀)) 64 ^^^
      s.mem.readW (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k)) 64) := by
    rw [u₁₀.gpr, u₁₀.other .r0 (by decide), u₉.gpr, u₉.other .r1 (by decide), u₈.gpr, u₈.other .r0 (by decide),
      u₇.gpr, u₇.other .r1 (by decide), u₇.other .r3 (by decide), u₆.gpr, u₆.other .r0 (by decide),
      u₆.other .r1 (by decide), u₆.other .r2 (by decide), u₅.gpr, u₅.other .r0 (by decide),
      u₅.other .r1 (by decide), u₄.gpr, u₄.other .r0 (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, readW64_split, readW64_split s.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (8 * k)),
      rev_xor_append]
  refine WP.seq (WP.mono (block_ok (UPre.block hp (by rw [g₁₀ _ (by decide), h.r9])
    (by rw [g₁₀ _ (by decide), h.r10]) (by rw [rd₁₀, h.rd]) (by rw [wr₁₀, h.wr]))) fun s₁₁ ⟨same, r9₁₁, ax₁₁⟩ => ?_)
  -- The slots past the block's words are unchanged.
  have r10₁₁ : s₁₁.gpr .r10 = S s₀ := by rw [same.r10, g₁₀ _ (by decide), h.r10]
  have xR₁₀ : xR s₁₀ = ⟨State.addr (S s₀), 52⟩ := by rw [xR, g₁₀ _ (by decide), h.r10]
  have f₁₁ : Frame [⟨State.addr (S s₀), 52⟩] s.mem s₁₁.mem := by rw [← m₁₀, ← xR₁₀]; exact same.frame
  have slot : ∀ d, 52 ≤ d → d + 4 ≤ 640 →
      s₁₁.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => f₁₁.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₁₁ : s₁₁.rd ++ s₁₁.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [same.rd, same.wr, rd₁₀, wr₁₀, rdwr]
  have wr₁₁ : s₁₁.wr = [stR s₀, scrR s₀] := by rw [same.wr, wr₁₀, h.wr, hp.wr]
  simp only [chainOut]
  refine wp_ldr (by decide) (by rw [r10₁₁, hp.scrAddr (by decide)])
    (by rw [rdwr₁₁]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₁ v₁ => ?_
  refine wp_ldr (by decide) (by rw [v₁.other _ (by decide), r10₁₁, hp.scrAddr (by decide)])
    (by rw [v₁.rd, v₁.wr, rdwr₁₁]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₂ v₂ => ?_
  refine wp_ldr (by decide) (by rw [v₂.other _ (by decide), v₁.other _ (by decide), r10₁₁, hp.scrAddr (by decide)])
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, rdwr₁₁]
        exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₃ v₃ => ?_
  have r4₃ : t₃.gpr .r4 = St s₀ := by
    rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, slot 112 (by decide) (by decide), h.st]
  have r5₃ : t₃.gpr .r5 = Dp s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, slot 116 (by decide) (by decide), h.dp]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [v₃.gpr, v₂.mem, v₁.mem, slot 120 (by decide) (by decide), h.left]
  refine wp_rev fun t₄ v₄ => wp_rev fun t₅ v₅ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions t₅.wr (State.addr (St s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₁₁]
    exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [v₅.other _ (by decide), v₄.other _ (by decide), r4₃, add0])
    (by simpa using stW 0 (by decide)) fun t₆ w₆ => ?_
  refine wp_str (by decide) (by rw [w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r4₃, stA])
    (by rw [w₆.wr]; exact stW 4 (by decide)) fun t₇ w₇ => ?_
  refine wp_add (op2_imm (by decide)) fun t₈ v₈ => wp_sub (op2_imm (by decide)) fun t₉ v₉ => ?_
  have g₉ : ∀ r, r ∉ [Reg.r0, .r1, .r4, .r5, .r6] → t₉.gpr r = s₁₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₉.other _ hr.2.2.2.2, v₈.other _ hr.2.2.2.1, w₇.gpr, w₆.gpr, v₅.other _ hr.2.1, v₄.other _ hr.1,
      v₃.other _ hr.2.2.2.2, v₂.other _ hr.2.2.2.1, v₁.other _ hr.2.2.1]
  have r10₉ : t₉.gpr .r10 = S s₀ := by rw [g₉ _ (by decide), r10₁₁]
  have wr₉ : t₉.wr = [stR s₀, scrR s₀] := by
    rw [v₉.wr, v₈.wr, w₇.wr, w₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₁₁]
  have scrW : ∀ d, d + 4 ≤ 640 → InRegions t₉.wr (State.addr (S s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [wr₉]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [r10₉, hp.scrAddr (by decide)]) (scrW 112 (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_str (by decide) (by rw [w₁₀.gpr, r10₉, hp.scrAddr (by decide)]) (by rw [w₁₀.wr]; exact scrW 116 (by decide))
    fun t₁₁ w₁₁ => ?_
  refine wp_str (by decide) (by rw [w₁₁.gpr, w₁₀.gpr, r10₉, hp.scrAddr (by decide)])
    (by rw [w₁₁.wr, w₁₀.wr]; exact scrW 120 (by decide)) fun t₁₂ w₁₂ =>
      wp_cmp (op2_imm (by decide)) fun t₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  -- The registers stored.
  have r4₉ : t₉.gpr .r4 = St s₀ := by
    rw [v₉.other _ (by decide), v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), r4₃]
  have r5₉ : t₉.gpr .r5 = Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [v₉.other _ (by decide), v₈.gpr, w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r5₃,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Straight.add_ofNat_ofNat, show 8 * k + 8 = 8 * (k + 1) by omega]
  have r6₈ : t₈.gpr .r6 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r6₃]
  have dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) :=
    ofNat_sub_one (by omega) (by omega)
  have r6₉ : t₉.gpr .r6 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by rw [v₉.gpr, r6₈, dec]
  -- The memory.
  have m₉ : t₉.mem = (s₁₁.mem.writeW (State.addr (St s₀)) (rev (s₁₁.gpr .r0))).writeW
      (State.addr (St s₀) + BitVec.ofNat 64 4) (rev (s₁₁.gpr .r1)) := by
    rw [v₉.mem, v₈.mem, w₇.mem, w₆.mem, w₆.gpr, v₅.gpr, v₅.other .r0 (by decide), v₄.gpr, v₅.mem, v₄.mem,
      v₄.other .r1 (by decide), v₃.other .r0 (by decide), v₃.other .r1 (by decide), v₂.other .r0 (by decide),
      v₂.other .r1 (by decide), v₁.other .r0 (by decide), v₁.other .r1 (by decide), v₃.mem, v₂.mem, v₁.mem]
  have m₁₂ : t₁₂.mem = ((t₉.mem.writeW (State.addr (S s₀) + BitVec.ofNat 64 112) (St s₀)).writeW (State.addr (S s₀) + BitVec.ofNat 64 116)
      (Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)))).writeW (State.addr (S s₀) + BitVec.ofNat 64 120)
      (BitVec.ofNat 32 (N s₀ - (k + 1))) := by
    rw [w₁₂.mem, w₁₁.mem, w₁₀.mem, w₁₁.gpr, w₁₀.gpr, r4₉, r5₉, r6₉]
  have g₁₃ : t₁₃.gpr = t₉.gpr := by rw [f₁₃.gpr, w₁₂.gpr, w₁₁.gpr, w₁₀.gpr]
  have mem₁₃ : t₁₃.mem = t₁₂.mem := f₁₃.mem
  -- The state.
  have hS : sch s₁₀ = Spec.TripleDes.scheduleAt s₀.mem (State.addr (W s₀)) := by
    rw [sch, g₁₀ _ (by decide), h.r9, m₁₀]; exact UPre.sched hp h.frame
  have hD := UPre.data hp h.frame hk
  have stSep : ∀ d, 112 ≤ d → d + 4 ≤ 124 → (stR s₀).Disjoint ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩ := fun d h₁ h₂ =>
    hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  have stFrame : Spec.Aes.bytesAt t₁₂.mem (State.addr (St s₀)) 8 = Spec.Aes.bytesAt t₉.mem (State.addr (St s₀)) 8 := by
    rw [m₁₂]
    refine bytesAt_frame (rs := [⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩]) ?_ (fun r hr => ?_) (by decide)
    · have c : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
          (⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (S s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
        rw [show State.addr (S s₀) + BitVec.ofNat 64 d = State.addr (S s₀) + BitVec.ofNat 64 112 + BitVec.ofNat 64 (d - 112) from
          (Offset.add_add_eq _ (by omega)).symm]
        exact Offset.contains_base _ (by omega) (by omega)
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 116 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (c 120 (by decide) (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g₁₃, g₉ _ (by decide), r9₁₁, g₁₀ _ (by decide), h.r9]
  · rw [g₁₃, r10₉]
  · rw [f₁₃.sp, w₁₂.sp, w₁₁.sp, w₁₀.sp, v₉.sp, v₈.sp, w₇.sp, w₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, same.sp,
      sp₁₀, h.sp]
  · rw [f₁₃.rd, w₁₂.rd, w₁₁.rd, w₁₀.rd, v₉.rd, v₈.rd, w₇.rd, w₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, same.rd,
      rd₁₀, h.rd]
  · rw [f₁₃.wr, w₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉, ← hp.wr, ← h.wr]
  · rw [mem₁₃, m₁₂, readW_writeW_far _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, m₉]
    have c4 : (stR s₀).Contains (State.addr (St s₀) + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base _ (by decide) (by omega)
    have c0 : (stR s₀).Contains (State.addr (St s₀)) (32 / 8) := by
      simpa using Offset.contains_base (State.addr (St s₀)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    have cs : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
        (⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (S s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
      rw [show State.addr (S s₀) + BitVec.ofNat 64 d = State.addr (S s₀) + BitVec.ofNat 64 112 + BitVec.ofNat 64 (d - 112) from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact (((((h.frame.trans (f₁₁.mono fun r hr => by simp at hr; simp [hr])).writeW (r := stR s₀) (by simp) _
      c0).writeW (r := stR s₀) (by simp) _ c4).writeW (by simp) _ (cs 112 (by decide) (by decide))).writeW
      (by simp) _ (cs 116 (by decide) (by decide))).writeW (by simp) _ (cs 120 (by decide) (by decide))
  · rw [mem₁₃, stFrame, m₉, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, rev_eq, rev_eq,
      byteRev32_append, ax₁₁, ax₁₀, hS, ← tdesWith_le8, le8_xor, le8_readW, le8_readW, h.state, hD,
      take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [z₁₃, show t₁₂.gpr .r6 = t₉.gpr .r6 by rw [w₁₂.gpr, w₁₁.gpr, w₁₀.gpr], r6₉]
    exact cmp0 (by omega)

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop updBody .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', z'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [eval_ne, z']; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem UPre.arg_in {s₀ : State} (hp : UPre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]; exact in_rw (r := argsR s₀) (by simp) (Region.contains_self _ _)

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block updPre) s₀ fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  have hN : N s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  rw [show updPre = .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([mov .r10 .r12, mov .r9 .r0, .str .r1 .r10 112, .str .r2 .r10 116, .str .r3 .r10 120,
      .cmp .r3 (.imm 0)] : List Instr)) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  have hm₂ : s₂.mem = savedMem s₀ (S s₀) := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  simp only [mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have r10₄ : s₄.gpr .r10 = S s₀ := by rw [u₄.other _ (by decide), u₃.gpr, g₂, h12]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂, u₁.wr]
  refine wp_str (by decide) (by rw [r10₄, hp.scrAddr (by decide)]) (by rw [wr₄]; exact hp.inScr (by decide) (by decide))
    fun s₅ w₅ => ?_
  refine wp_str (by decide) (by rw [w₅.gpr, r10₄, hp.scrAddr (by decide)])
    (by rw [w₅.wr, wr₄]; exact hp.inScr (by decide) (by decide)) fun s₆ w₆ => ?_
  refine wp_str (by decide) (by rw [w₆.gpr, w₅.gpr, r10₄, hp.scrAddr (by decide)])
    (by rw [w₆.wr, w₅.wr, wr₄]; exact hp.inScr (by decide) (by decide)) fun s₇ w₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  have g₈ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s₈.gpr r = s₀.gpr r := fun r h9 h10 h12' => by
    rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, u₄.other _ h9, u₃.other _ h10, g₂, u₁.other _ h12']
  have r1₄ : s₄.gpr .r1 = St s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have r2₄ : s₄.gpr .r2 = Dp s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have r3₄ : s₄.gpr .r3 = s₀.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have m₈ : s₈.mem = (((savedMem s₀ (S s₀)).writeW (State.addr (S s₀) + BitVec.ofNat 64 112) (St s₀)).writeW
      (State.addr (S s₀) + BitVec.ofNat 64 116) (Dp s₀)).writeW (State.addr (S s₀) + BitVec.ofNat 64 120)
      (s₀.gpr .r3) := by
    rw [f₈.mem, w₇.mem, w₆.mem, w₅.mem, u₄.mem, u₃.mem, hm₂, w₆.gpr, w₅.gpr, r1₄, r2₄, r3₄]
  have cs : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
      (⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (S s₀) + BitVec.ofNat 64 d)
        (32 / 8) := fun d h₁ h₂ => by
    rw [show State.addr (S s₀) + BitVec.ofNat 64 d = State.addr (S s₀) + BitVec.ofNat 64 112 +
      BitVec.ofNat 64 (d - 112) from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have fr₈ : Frame [⟨State.addr (S s₀) + BitVec.ofNat 64 112, 12⟩] (savedMem s₀ (S s₀)) s₈.mem := by
    rw [m₈]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 116 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cs 120 (by decide) (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, r10₄]
  · rw [f₈.sp, w₇.sp, w₆.sp, w₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₈.rd, w₇.rd, w₆.rd, w₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₈.wr, w₇.wr, w₆.wr, w₅.wr, wr₄]
  · rw [m₈, readW_writeW_far _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m₈, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, add0]
  · rw [m₈, Mem.readW_writeW_self32, Nat.sub_zero]; simp [N]
  · exact fr₈.mono fun r hr => by simp at hr; simp [hr]
  · rw [List.take_zero, show Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 8) [] =
      Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 8 from rfl]
    rw [bytesAt_frame fr₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
    exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [z₈, show s₇.gpr .r3 = s₀.gpr .r3 by rw [w₇.gpr, w₆.gpr, w₅.gpr, r3₄]]
    have : s₀.gpr .r3 = BitVec.ofNat 32 (N s₀) := by simp [N]
    rw [this]; exact cmp0 hN

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop updBody .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by show some s₁.z = _; rw [hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  refine WP.mono (restore_ok h₂.r10 (by omega) fun d h₁ h₂' => ?_) fun s' ⟨hl, sp', m', _, _⟩ => ⟨?_, ?_⟩
  · rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  · refine restored (S := S s₀) (fun d h₁ h₂' => ?_) hl (by rw [sp', h₂.sp])
    refine h₂.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (d := d) (e := 112) (by omega) (by omega) (by omega)
  · show Spec.Aes.bytesAt s'.mem (State.addr (St s₀)) 8 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [m', h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.Arm
