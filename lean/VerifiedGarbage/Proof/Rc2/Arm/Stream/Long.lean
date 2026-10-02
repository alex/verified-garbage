import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common

/-! # Streaming RC2-CBC on ARMv7: the copies before CBC

With `out_len ≠ 0`: `lr` saved at `scratch + 512`, the pending bytes and the
first `out_len - pending_len` bytes of data to `out`, the rest of the data to
`ctx + 136`, and the arguments of the CBC function (`Mid`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.WriteBytes VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_str wp_ldrSp
  sub_ofNat ofNat_shr)

theorem toNat_add32 {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-- The state before the call of the CBC function, from the entry state `s`. -/
structure Mid (s t : State) : Prop where
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = s.gpr .r0 + 128
  r2 : t.gpr .r2 = stackArg s 0
  r3 : t.gpr .r3 = BitVec.ofNat 32 ((stackArg s 1).toNat / 8)
  r12 : t.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  /-- Memory changed only in `out`, the pending block and the saved `lr`. -/
  frame : Frame [⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩,
    ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 136, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem t.mem
  lr : t.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  out : Spec.Rc2.bytesAt t.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
    Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 136) (s.gpr .r1).toNat ++
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) ((stackArg s 1).toNat - (s.gpr .r1).toNat)
  pend : Spec.Rc2.bytesAt t.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 136)
      (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8) =
    Spec.Rc2.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((stackArg s 1).toNat - (s.gpr .r1).toNat))
      (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8)

/-- The code before the call, followed by `tail`. -/
def longWith (tail : Prog isa) : Prog isa :=
  .seq (.block toOut) (.seq (copy .r0 136 .lr 0 .r1) (.seq (.block middle) (.seq (copy .r2 0 .lr 0 .r1)
    (.seq (.block toPending) (.seq (copy .r2 0 .lr 136 .r3) (.seq (.block cbcArgs) tail))))))

theorem long_eq (d : Spec.Rc2.Direction) : long d = longWith (.seq (cbcCall d) (.block restoreLr)) := rfl

theorem long_ok' (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Keep s t) {tail : Prog isa} {Q : State → Prop}
    (hQ : ∀ t', Mid s t' → WP isa tail t' Q) :
    WP isa (longWith tail) t Q := by
  obtain ⟨_, spfit, hrd, hwr, ctxData, ctxOut, ctxScr, ctxArgs, dataOut, dataScr, outScr, outArgs,
    scrArgs, _, _, _, _, _, fitC, fitD, fitO, fitS, hp, hN⟩ := hs
  have r1v : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := ofNat_toNat32 _
  have r3v : s.gpr .r3 = BitVec.ofNat 32 (s.gpr .r3).toNat := ofNat_toNat32 _
  have olv : stackArg s 1 = BitVec.ofNat 32 (stackArg s 1).toNat := ofNat_toNat32 _
  have hNlt := (s.gpr .r3).isLt
  have hOLlt := (stackArg s 1).isLt
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  generalize hC : s.gpr .r0 = C at *
  generalize hDt : s.gpr .r2 = Dt at *
  generalize hO : stackArg s 0 = O at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  generalize hP : (s.gpr .r1).toNat = P at *
  generalize hNN : (s.gpr .r3).toNat = N at *
  generalize hOL : (stackArg s 1).toNat = OL at *
  have h8 : 8 ≤ OL := by omega
  have hPO : P ≤ OL := by omega
  have hON : OL - P ≤ N := by omega
  have hR : N - (OL - P) = (P + N) % 8 := by omega
  have hRlt : (P + N) % 8 < 8 := Nat.mod_lt _ (by decide)
  have rdwr {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have scrW (i n : Nat) (h : i + n ≤ 576) : InRegions s.wr (State.addr S + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega)⟩
  have ctxIn : (⟨State.addr C, 144⟩ : Region) ∈ s.rd ++ s.wr := by rw [hwr]; simp
  have outIn : (⟨State.addr O, OL⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have dataIn : (⟨State.addr Dt, N⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ctxInW : (⟨State.addr C, 144⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  -- The regions the code writes before the call.
  have argsSep : ∀ r ∈ [(⟨State.addr O, OL⟩ : Region), ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact outArgs.symm
    · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
    · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))
  -- Saving `lr`, and `out`.
  rw [longWith, show toOut = [.ldrSp .r12 8, .str .lr .r12 512, .ldrSp .lr 0] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [ht.sp]; rfl)
    (by rw [ht.rd, ht.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_)
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, ht.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega))
    (by rw [v₁.wr, ht.wr]; exact scrW 512 4 (by decide)) fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, ht.mem, v₁.other _ (by decide), ht.reg _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  refine wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [v₂.sp, v₁.sp, ht.sp]; rfl)
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, ht.rd, ht.wr]; exact argR 0 (by decide)) fun u₃ v₃ => WP.block_nil ?_
  have lr₃ : u₃.gpr .lr = O := by rw [v₃.gpr, stackArg_frame f₂ spfit argsSep (by decide)]; exact hO
  have g₃ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .lr) : u₃.gpr r = s.gpr r := by
    rw [v₃.other _ h₂, v₂.gpr, v₁.other _ h₁, ht.reg _ h₁]
  have rd₃ : u₃.rd = s.rd := by rw [v₃.rd, v₂.rd, v₁.rd, ht.rd]
  have wr₃ : u₃.wr = s.wr := by rw [v₃.wr, v₂.wr, v₁.wr, ht.wr]
  have sp₃ : u₃.sp = s.sp := by rw [v₃.sp, v₂.sp, v₁.sp, ht.sp]
  rw [← v₃.mem] at m₂ f₂
  -- The pending bytes to `out`.
  refine WP.seq (WP.mono (copy_ok (s := u₃) (src := .r0) (dst := .lr) (cnt := .r1) (so := 136) (dd := 0)
    (L := P) (A := State.addr C + BitVec.ofNat 64 136) (B := State.addr O)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ _ (by decide) (by decide), r1v]) (by omega)
    (by rw [g₃ _ (by decide) (by decide), hC]; omega) (by rw [lr₃]; omega)
    (by rw [g₃ _ (by decide) (by decide), hC]) (by rw [lr₃]; exact add0 _)
    (fun _ => by rw [rd₃, wr₃]; exact cov1 ctxIn (by omega))
    (fun _ => by rw [wr₃, ← add0 (State.addr O)]; exact cov1 outIn (by omega))
    (fun _ => (ctxOut.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hPO))) ?_)
  intro u₄ c₄
  have f₄ : Frame [⟨State.addr O, P⟩] u₃.mem u₄.mem := by
    rw [c₄.mem]; exact writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have o₄ : Spec.Rc2.bytesAt u₄.mem (State.addr O) P =
      Spec.Rc2.bytesAt s.mem (State.addr C + BitVec.ofNat 64 136) P := by
    rw [c₄.mem, bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega), m₂,
      bytesAt_writeW _ (by omega) ((ctxScr.sub_left (Offset.sub_base _ (by omega))).sub_right
        (Offset.sub_base _ (by decide)))]
  have F₄ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₄.mem :=
    f₂.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hPO⟩)
  -- `r12 = p`, `r0 = ctx`, `r1 = out_len - p`, `r3 = len - r1`.
  rw [show middle = [.ldrSp .r12 0, .dp .sub .r12 .lr (.reg .r12), .dp .sub .r0 .r0 (.reg .r12), .ldrSp .r1 4,
    .dp .sub .r1 .r1 (.reg .r12), .dp .sub .r3 .r3 (.reg .r1)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [c₄.sp, sp₃]; rfl)
    (by rw [c₄.rd, c₄.wr, rd₃, wr₃]; exact argR 0 (by decide)) fun w₁ y₁ => ?_)
  refine wp_sub (op2_reg _ _) fun w₂ y₂ => wp_sub (op2_reg _ _) fun w₃ y₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [y₃.sp, y₂.sp, y₁.sp, c₄.sp, sp₃]; rfl)
    (by rw [y₃.rd, y₃.wr, y₂.rd, y₂.wr, y₁.rd, y₁.wr, c₄.rd, c₄.wr, rd₃, wr₃]; exact argR 1 (by decide))
    fun w₄ y₄ => wp_sub (op2_reg _ _) fun w₅ y₅ => wp_sub (op2_reg _ _) fun w₆ y₆ => WP.block_nil ?_
  have r12₁ : w₁.gpr .r12 = O := by rw [y₁.gpr, stackArg_frame F₄ spfit argsSep (by decide)]; exact hO
  have lr₄ : u₄.gpr .lr = O + BitVec.ofNat 32 P := by rw [c₄.dstv, lr₃]
  have r0₄ : u₄.gpr .r0 = C + BitVec.ofNat 32 P := by rw [c₄.srcv, g₃ _ (by decide) (by decide), hC]
  have r12₂ : w₂.gpr .r12 = BitVec.ofNat 32 P := by
    rw [y₂.gpr, y₁.other _ (by decide), r12₁, lr₄, Offset.add_sub_cancel_left]
  have r0₃ : w₃.gpr .r0 = C := by
    rw [y₃.gpr, y₂.other _ (by decide), y₁.other _ (by decide), r0₄, r12₂, BitVec.add_sub_cancel]
  have mem₃ : w₃.mem = u₄.mem := by rw [y₃.mem, y₂.mem, y₁.mem]
  have r1₄ : w₄.gpr .r1 = BitVec.ofNat 32 OL := by
    rw [y₄.gpr, mem₃, stackArg_frame F₄ spfit argsSep (by decide), olv]
  have r1₅ : w₅.gpr .r1 = BitVec.ofNat 32 (OL - P) := by
    rw [y₅.gpr, r1₄, y₄.other _ (by decide), y₃.other _ (by decide), r12₂, sub_ofNat hPO]
  have r3₆ : w₆.gpr .r3 = BitVec.ofNat 32 ((P + N) % 8) := by
    rw [y₆.gpr, y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide), y₂.other _ (by decide),
      y₁.other _ (by decide), c₄.keep _ (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide), r3v, r1₅, sub_ofNat hON, hR]
  have g₆ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .lr) (h₃ : r ≠ .r0) (h₄ : r ≠ .r1) (h₅ : r ≠ .r3) :
      w₆.gpr r = s.gpr r := by
    rw [y₆.other _ h₅, y₅.other _ h₄, y₄.other _ h₄, y₃.other _ h₃, y₂.other _ h₁, y₁.other _ h₁,
      c₄.keep _ h₃ h₂ h₄ h₁, g₃ _ h₁ h₂]
  have lr₆ : w₆.gpr .lr = O + BitVec.ofNat 32 P := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), y₃.other _ (by decide),
      y₂.other _ (by decide), y₁.other _ (by decide), lr₄]
  have mem₆ : w₆.mem = u₄.mem := by rw [y₆.mem, y₅.mem, y₄.mem, mem₃]
  have rd₆ : w₆.rd = s.rd := by rw [y₆.rd, y₅.rd, y₄.rd, y₃.rd, y₂.rd, y₁.rd, c₄.rd, rd₃]
  have wr₆ : w₆.wr = s.wr := by rw [y₆.wr, y₅.wr, y₄.wr, y₃.wr, y₂.wr, y₁.wr, c₄.wr, wr₃]
  have sp₆ : w₆.sp = s.sp := by rw [y₆.sp, y₅.sp, y₄.sp, y₃.sp, y₂.sp, y₁.sp, c₄.sp, sp₃]
  have r0₆ : w₆.gpr .r0 = C := by
    rw [y₆.other _ (by decide), y₅.other _ (by decide), y₄.other _ (by decide), r0₃]
  have r1₆ : w₆.gpr .r1 = BitVec.ofNat 32 (OL - P) := by rw [y₆.other _ (by decide), r1₅]
  have eOP : State.addr (O + BitVec.ofNat 32 P) = State.addr O + BitVec.ofNat 64 P := addr_add (by omega)
  -- The first `out_len - p` bytes of data to `out + p`.
  refine WP.seq (WP.mono (copy_ok (s := w₆) (src := .r2) (dst := .lr) (cnt := .r1) (so := 0) (dd := 0)
    (L := OL - P) (A := State.addr Dt) (B := State.addr O + BitVec.ofNat 64 P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r1₆ (by omega)
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]; omega)
    (by rw [lr₆, toNat_add32 (by omega)]; omega)
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]; exact add0 _)
    (by rw [lr₆, eOP]; exact add0 _)
    (fun _ => by rw [rd₆, wr₆, ← add0 (State.addr Dt)]; exact cov1 dataIn (by omega))
    (fun _ => by rw [wr₆]; exact cov1 outIn (by omega))
    (fun _ => (dataOut.sub_left (Region.sub_prefix hON)).sub_right (Offset.sub_base _ (by omega)))) ?_)
  intro u₅ c₅
  have c5m : u₅.mem = writeBytes u₄.mem (State.addr O + BitVec.ofNat 64 P)
      (Spec.Rc2.bytesAt u₄.mem (State.addr Dt) (OL - P)) := by rw [← mem₆]; exact c₅.mem
  have f₅ : Frame [⟨State.addr O + BitVec.ofNat 64 P, OL - P⟩] u₄.mem u₅.mem := by
    rw [c5m]; exact writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have o₅ : Spec.Rc2.bytesAt u₅.mem (State.addr O + BitVec.ofNat 64 P) (OL - P) =
      Spec.Rc2.bytesAt s.mem (State.addr Dt) (OL - P) := by
    rw [c5m, bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega),
      Proof.Rc2.bytesAt_frame F₄ _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dataOut.sub_left (Region.sub_prefix hON)
        · exact ctxData.symm.sub_left (Region.sub_prefix hON) |>.sub_right (Offset.sub_base _ (by decide))
        · exact dataScr.sub_left (Region.sub_prefix hON) |>.sub_right (Offset.sub_base _ (by decide)))]
  have F₅ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₅.mem :=
    F₄.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩)
  -- The rest to `ctx + 136`.
  rw [show toPending = [.mov .lr (.reg .r0)] from rfl]
  refine WP.seq (wp_mov (op2_reg _ _) fun u₆ v₆ => WP.block_nil ?_)
  have r2₆ : u₆.gpr .r2 = Dt + BitVec.ofNat 32 (OL - P) := by
    rw [v₆.other _ (by decide), c₅.srcv, g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hDt]
  have r0₅ : u₅.gpr .r0 = C := by rw [c₅.keep _ (by decide) (by decide) (by decide) (by decide), r0₆]
  have lr₆' : u₆.gpr .lr = C := by rw [v₆.gpr, r0₅]
  have r3₆' : u₆.gpr .r3 = BitVec.ofNat 32 ((P + N) % 8) := by
    rw [v₆.other _ (by decide), c₅.keep _ (by decide) (by decide) (by decide) (by decide), r3₆]
  -- The data after the first `out_len - p` bytes, at an address that wraps only if nothing is left.
  have eA (hR0 : 0 < (P + N) % 8) :
      State.addr (Dt + BitVec.ofNat 32 (OL - P)) = State.addr Dt + BitVec.ofNat 64 (OL - P) :=
    addr_add (by omega)
  have bA (m : Mem) : Spec.Rc2.bytesAt m (State.addr (Dt + BitVec.ofNat 32 (OL - P))) ((P + N) % 8) =
      Spec.Rc2.bytesAt m (State.addr Dt + BitVec.ofNat 64 (OL - P)) ((P + N) % 8) := by
    rcases Nat.eq_zero_or_pos ((P + N) % 8) with h0 | h0
    · rw [h0]; rfl
    · rw [eA h0]
  have dSub : Region.Sub ⟨State.addr Dt + BitVec.ofNat 64 (OL - P), (P + N) % 8⟩ ⟨State.addr Dt, N⟩ :=
    Offset.sub_base _ (by omega)
  have pSub : Region.Sub ⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩ ⟨State.addr C, 144⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono (copy_ok (s := u₆) (src := .r2) (dst := .lr) (cnt := .r3) (so := 0) (dd := 136)
    (L := (P + N) % 8) (A := State.addr (Dt + BitVec.ofNat 32 (OL - P))) (B := State.addr C + BitVec.ofNat 64 136)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r3₆' (by omega)
    (by
      rw [r2₆]
      rcases Nat.eq_zero_or_pos ((P + N) % 8) with h0 | h0
      · rw [h0]; have := (Dt + BitVec.ofNat 32 (OL - P)).isLt; omega
      · rw [toNat_add32 (by omega)]; omega)
    (by rw [lr₆']; omega) (by rw [r2₆]; exact add0 _) (by rw [lr₆'])
    (fun h0 => by
      rw [v₆.rd, v₆.wr, c₅.rd, c₅.wr, rd₆, wr₆, eA h0]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, dataIn, OL - P, rfl, by simp only; omega⟩)
    (fun _ => by rw [v₆.wr, c₅.wr, wr₆]; exact cov1 ctxInW (by omega))
    (fun h0 => by rw [eA h0]; exact (ctxData.symm.sub_left dSub).sub_right pSub)) ?_)
  intro u₇ c₇
  have c7m : u₇.mem = writeBytes u₅.mem (State.addr C + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt u₅.mem (State.addr (Dt + BitVec.ofNat 32 (OL - P))) ((P + N) % 8)) := by
    rw [← v₆.mem]; exact c₇.mem
  have f₇ : Frame [⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩] u₅.mem u₇.mem := by
    rw [c7m]; exact writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  have F₇ : Frame [⟨State.addr O, OL⟩, ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩] s.mem u₇.mem :=
    F₅.trans (f₇.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩)
  have p₇ : Spec.Rc2.bytesAt u₇.mem (State.addr C + BitVec.ofNat 64 136) ((P + N) % 8) =
      Spec.Rc2.bytesAt s.mem (State.addr Dt + BitVec.ofNat 64 (OL - P)) ((P + N) % 8) := by
    rw [c7m, bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega), bA,
      Proof.Rc2.bytesAt_frame F₅ _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dataOut.sub_left dSub
        · exact (ctxData.symm.sub_left dSub).sub_right (Offset.sub_base _ (by decide))
        · exact (dataScr.sub_left dSub).sub_right (Offset.sub_base _ (by decide)))]
  have r0₇ : u₇.gpr .r0 = C := by
    rw [c₇.keep _ (by decide) (by decide) (by decide) (by decide), v₆.other _ (by decide), r0₅]
  have rd₇ : u₇.rd = s.rd := by rw [c₇.rd, v₆.rd, c₅.rd, rd₆]
  have wr₇ : u₇.wr = s.wr := by rw [c₇.wr, v₆.wr, c₅.wr, wr₆]
  have sp₇ : u₇.sp = s.sp := by rw [c₇.sp, v₆.sp, c₅.sp, sp₆]
  have g₇ (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) : u₇.gpr r = s.gpr r := by
    obtain ⟨h0, h1, h2, h3, h12⟩ := preserved_ne hr hl
    rw [c₇.keep _ h2 hl h3 h12, v₆.other _ hl, c₅.keep _ h2 hl h1 h12, g₆ _ h12 hl h0 h1 h3]
  -- The arguments of the CBC function.
  rw [show cbcArgs = [.dp .add .r1 .r0 (.imm 128), .ldrSp .r2 0, .ldrSp .r3 4,
    .mov .r3 (.shifted .r3 .lsr 3), .ldrSp .r12 8] from rfl]
  refine WP.seq (wp_add (op2_imm (by decide)) fun x₁ z₁ => ?_)
  refine wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [z₁.sp, sp₇]; rfl)
    (by rw [z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 0 (by decide)) fun x₂ z₂ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [z₂.sp, z₁.sp, sp₇]; rfl)
    (by rw [z₂.rd, z₂.wr, z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 1 (by decide)) fun x₃ z₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun x₄ z₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [z₄.sp, z₃.sp, z₂.sp, z₁.sp, sp₇]; rfl)
    (by rw [z₄.rd, z₄.wr, z₃.rd, z₃.wr, z₂.rd, z₂.wr, z₁.rd, z₁.wr, rd₇, wr₇]; exact argR 2 (by decide))
    fun x₅ z₅ => WP.block_nil ?_
  have memx : x₅.mem = u₇.mem := by rw [z₅.mem, z₄.mem, z₃.mem, z₂.mem, z₁.mem]
  have mem₄ : x₄.mem = u₇.mem := by rw [z₄.mem, z₃.mem, z₂.mem, z₁.mem]
  have mem₂ : x₂.mem = u₇.mem := by rw [z₂.mem, z₁.mem]
  have mem₁ : x₁.mem = u₇.mem := z₁.mem
  apply hQ x₅
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.other _ (by decide),
      z₁.other _ (by decide), r0₇, hC]
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.other _ (by decide),
      z₁.gpr, r0₇, hC]
  · rw [z₅.other _ (by decide), z₄.other _ (by decide), z₃.other _ (by decide), z₂.gpr, mem₁,
      stackArg_frame F₇ spfit argsSep (by decide), hO]
  · rw [z₅.other _ (by decide), z₄.gpr, z₃.gpr, mem₂, stackArg_frame F₇ spfit argsSep (by decide), olv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hOLlt, ofNat_shr hOLlt]
  · rw [z₅.gpr, mem₄, stackArg_frame F₇ spfit argsSep (by decide), hS]
  · intro r hr hl
    obtain ⟨_, h1, h2, h3, h12⟩ := preserved_ne hr hl
    rw [z₅.other _ h12, z₄.other _ h3, z₃.other _ h3, z₂.other _ h2, z₁.other _ h1, g₇ r hr hl]
  · rw [z₅.sp, z₄.sp, z₃.sp, z₂.sp, z₁.sp, sp₇]
  · rw [z₅.rd, z₄.rd, z₃.rd, z₂.rd, z₁.rd, rd₇]
  · rw [z₅.wr, z₄.wr, z₃.wr, z₂.wr, z₁.wr, wr₇]
  · rw [memx, hO, hOL, hC, hS]; exact F₇
  · -- The saved `lr`.
    have a4 : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
    rw [memx, hS, hLR,
      f₇.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (ctxScr.symm.sub_left a4).sub_right pSub) (by decide),
      f₅.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (outScr.symm.sub_left a4).sub_right (Offset.sub_base _ (by omega))) (by decide),
      f₄.readW (r := ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (outScr.symm.sub_left a4).sub_right (Region.sub_prefix hPO)) (by decide),
      m₂, Mem.readW_writeW_self32]
  · -- `out`: the pending bytes, then the data.
    rw [memx, hO, hOL, hC, hP, hDt, show OL = P + (OL - P) by omega, Proof.Rc2.bytesAt_add,
      Nat.add_sub_cancel_left]
    have outSub : ∀ r ∈ [(⟨State.addr C + BitVec.ofNat 64 136, (P + N) % 8⟩ : Region)],
        (Region.mk (State.addr O) OL).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ctxOut.symm.sub_right pSub
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [Proof.Rc2.bytesAt_frame f₇ _ _ (by omega) (fun r hr => (outSub r hr).sub_left (Region.sub_prefix hPO)),
        Proof.Rc2.bytesAt_frame f₅ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)), o₄]
    · rw [Proof.Rc2.bytesAt_frame f₇ _ _ (by omega)
          (fun r hr => (outSub r hr).sub_left (Offset.sub_base _ (by omega))), o₅]
  · rw [memx, hC, hP, hNN, hDt, hOL]; exact p₇

theorem long_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Keep s t) {Q : State → Prop}
    (hQ : ∀ t', Mid s t' → WP isa (.seq (cbcCall d) (.block restoreLr)) t' Q) :
    WP isa (long d) t Q := by
  rw [long_eq]; exact long_ok' d s hs hnz t ht hQ

end VG.Proof.Rc2.Arm.Stream
