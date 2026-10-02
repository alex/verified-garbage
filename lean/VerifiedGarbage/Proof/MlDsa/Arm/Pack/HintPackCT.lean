import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintCT

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the lengths,
`ω`, the stack pointer and the hint, which the contract lets the function
leak) leak the same trace (`RelCT`), phase by phase: the load of `len` and the
frame's reload of `r5` access only the stack (`RelCT.spBlock`); zeroing `y` is
proved by the taint analysis; the loops by `memTaint`, from the states
narrowed to the hint and `y` (`RelCT.narrow`), on which both runs agree once
`y` is zeroed. What each run is at each point comes from the correctness proof
(`RelCT.wp`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

theorem pre_of {s : State} (h : (hintBitPackContract Arm.abi 8).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : PPre s₁
  hp₂ : PPre s₂
  sp : s₁.sp = s₂.sp
  leak : (List.range (s₁.gpr .r1).toNat).map (fun i => (coeffAt s₁.mem (State.addr (pH s₁)) i).toNat) =
    (List.range (s₂.gpr .r1).toNat).map (fun i => (coeffAt s₂.mem (State.addr (pH s₂)) i).toNat)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  arg : stackArg s₁ 0 = stackArg s₂ 0

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem hR_eq : hR s₁ = hR s₂ := by simp only [hR, pH, h.r0, h.r1]

theorem yR_eq : yR s₁ = yR s₂ := by simp only [yR, pY, pLen, pL, h.r3, h.arg]

/-- The hint and the zeroed `y`: the memory both runs agree on. -/
theorem memEq {a b : State} (ha : ZP s₁ a) (hb : ZP s₂ b) : Hint.MemEq ([hR s₁] ++ [yR s₁]) a.mem b.mem := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp₁
  intro x ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · -- The hint: as on entry.
    have e₁ := zp_frame hp₁ ha x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₁.b_h x hc' hc
      · exact hp₁.d_hy x hc hc')
    rw [hR_eq h] at hc
    have e₂ := zp_frame hp₂ hb x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₂.b_h x hc' hc
      · exact hp₂.d_hy x hc hc')
    rw [e₁, e₂]
    rw [← hR_eq h] at hc
    have hl := h.leak
    rw [show State.addr (pH s₂) = State.addr (pH s₁) by simp only [pH, h.r0], ← h.r1] at hl
    exact bytes_of_words hl hc
  · -- `y`: zeros.
    have hlt : (x - State.addr (pY s₁)).toNat < pLen s₁ := by simp only [Region.Contains] at hc; omega
    have ea : x = State.addr (pY s₁) + BitVec.ofNat 64 (x - State.addr (pY s₁)).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have e₁ : (bytesAt a.mem (State.addr (pY s₁)) (pLen s₁)).getD (x - State.addr (pY s₁)).toNat 0 =
        (List.replicate (pLen s₁) (0 : Byte)).getD (x - State.addr (pY s₁)).toNat 0 := by rw [ha.2.2.2.2.1]
    have e₂ : (bytesAt b.mem (State.addr (pY s₂)) (pLen s₂)).getD (x - State.addr (pY s₁)).toNat 0 =
        (List.replicate (pLen s₂) (0 : Byte)).getD (x - State.addr (pY s₁)).toNat 0 := by rw [hb.2.2.2.2.1]
    rw [bytesAt_getD _ _ hlt, ← ea] at e₁
    rw [show pY s₂ = pY s₁ by simp only [pY, h.r3], show pLen s₂ = pLen s₁ by simp only [pLen, pL, h.arg],
      bytesAt_getD _ _ hlt, ← ea] at e₂
    rw [e₁, e₂]

/-- The loops, from the states narrowed to the hint and `y`. -/
theorem main_ct : RelCT isa (fun a b => ZP s₁ a ∧ ZP s₂ b) hbpMain fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [hR s₁]) (fun _ => [yR s₁]) (fun a b ⟨ha, hb⟩ => ?_) (fun a b ⟨ha, hb⟩ => ?_) ?_
  · have hra : hR s₁ ∈ a.rd := by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd]
    have hwa : yR s₁ ∈ a.wr := by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr]
    have hrb : hR s₁ ∈ b.rd := by rw [hb.2.2.2.2.2.2.1, hR_eq h]; simp [RegUpd.rd_setReg, hp₂.rd]
    have hwb : yR s₁ ∈ b.wr := by rw [hb.2.2.2.2.2.2.2.1, yR_eq h]; simp [RegUpd.wr_setReg, hp₂.wr]
    exact ⟨covers_of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hra
        · exact List.mem_append_right _ hwa,
      covers_of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwa,
      covers_of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hrb
        · exact List.mem_append_right _ hwb,
      covers_of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwb⟩
  · obtain ⟨a0, a1, a2, a3, az, -⟩ := id ha
    obtain ⟨b0, b1, b2, b3, bz, -⟩ := id hb
    obtain ⟨t₁, u₁, e₁, -⟩ := main_ok hp₁ (mainPre_of hp₁ ha (rd := [hR s₁]) (wr := [yR s₁])
      (List.mem_singleton_self _) (List.mem_singleton_self _)) a0 a1 a2 a3 az
    obtain ⟨t₂, u₂, e₂, -⟩ := main_ok hp₂ (mainPre_of hp₂ hb (rd := [hR s₁]) (wr := [yR s₁])
      (by rw [hR_eq h]; exact List.mem_singleton_self _) (by rw [yR_eq h]; exact List.mem_singleton_self _))
      b0 b1 b2 b3 bz
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, memEq h (a := a) (b := b) ha hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [State.withRegions_gpr, ha.1, hb.1, pH, h.r0]
    · simp only [State.withRegions_gpr, ha.2.1, hb.2.1, pk, pLen, pL, pω, pW, h.r2, h.arg]
    · simp only [State.withRegions_gpr, ha.2.2.1, hb.2.2.1, pW, h.r2]
    · simp only [State.withRegions_gpr, ha.2.2.2.1, hb.2.2.2.1, pY, h.r3]

/-- The body of the frame. -/
theorem body_ct : RelCT isa (fun a b => a = P1 s₁ ∧ b = P1 s₂) hintBitPackBody fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold hintBitPackBody
  refine RelCT.seq (R := fun a b => ZP s₁ a ∧ ZP s₂ b) (relct_wp ?_ fun a b ⟨ea, eb⟩ =>
    ⟨by rw [ea]; exact zeroP_ok hp₁, by rw [eb]; exact zeroP_ok hp₂⟩) ?_
  · refine RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r2, .r3, .r12])
      (fun a b ⟨ea, eb⟩ => Taint.agree_ofRegs fun r hr => ?_) (by taint_decide)
    subst ea eb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r2]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r3]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, pL, h.arg]; rfl
  refine RelCT.seq (R := fun (a b : State) => a.sp = (P1 s₁).sp ∧ b.sp = (P1 s₂).sp)
    (relct_wp (main_ct h) fun a b hab => ⟨?_, ?_⟩) ?_
  · have ha := hab.1
    obtain ⟨a0, a1, a2, a3, az, -, -, -, asp⟩ := id ha
    refine WP.mono (main_ok hp₁ ?_ a0 a1 a2 a3 az) fun s' hs => hs.2.2.2.2.trans asp
    have := mainPre_of hp₁ ha (rd := a.rd) (wr := a.wr) (by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd])
      (by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr])
    rwa [State.withRegions_self] at this
  · have hb := hab.2
    obtain ⟨b0, b1, b2, b3, bz, -, -, -, bsp⟩ := id hb
    refine WP.mono (main_ok hp₂ ?_ b0 b1 b2 b3 bz) fun s' hs => hs.2.2.2.2.trans bsp
    have := mainPre_of hp₂ hb (rd := b.rd) (wr := b.wr) (by rw [hb.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₂.rd])
      (by rw [hb.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₂.wr])
    rwa [State.withRegions_self] at this
  · exact Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by
      rw [ea, eb]; simp only [P1, pushed_sp, RegUpd.sp_setReg, h.sp]

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) Impl.MlDsa.Arm.Pack.hintBitPack fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine RelCT.seq (R := fun a b => a = s₁.setReg .r12 (pL s₁) ∧ b = s₂.setReg .r12 (pL s₂))
    (relct_wp (Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by rw [ea, eb, h.sp]) fun a b ⟨ea, eb⟩ =>
      ⟨by rw [ea]; exact entry_ok (by rw [hp₁.rd]; exact ⟨argR s₁, by simp, Region.contains_self _ _⟩),
       by rw [eb]; exact entry_ok (by rw [hp₂.rd]; exact ⟨argR s₂, by simp, Region.contains_self _ _⟩)⟩) ?_
  refine RelCT.frame (fun a b ⟨ea, eb⟩ => by rw [ea, eb]; simp only [RegUpd.sp_setReg, h.sp]) ?_
  refine RelCT.mono (body_ct h) (fun a b ⟨x, y, ⟨ex, ey⟩, px, py⟩ => ?_) fun _ _ h => h
  subst ex ey
  exact ⟨(push_pushed' px).1, (push_pushed' py).1⟩

end

/-! ## Verified -/

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := by
  simp [coeffAt, Mem.readW, Mem.read]

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_zero l]

theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, coeffAt_zero, Function.comp_def, filter_false, sum_zero]

theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ t < 256 * k, coeffAt m p t = coeffAt m' p t) : hintAt m p k = hintAt m' p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  congr 1; funext j
  have hj : j.val < 256 := j.isLt
  rw [h _ (by omega)]

/-- The memory of the satisfying state: `len = 84` on the stack. -/
def satMem : Mem := fun a => if a = 0x8000 then 84 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1024 | .r2 => 80 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0x1000, 4096⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 84⟩]

theorem satArg : stackArg satState 0 = 84 := by decide +kernel

theorem satHint : hintOnes (hintAt satMem 0x1000 4) = 0 := by
  rw [hintAt_congr (m' := fun _ => 0) fun t ht => ?_, hintOnes_zero]
  rw [coeffAt_eq, coeffAt_eq]
  refine Mem.readW_congr fun b hb => ?_
  simp only [satMem]
  rw [ite_neg' fun e => by bv_omega]

theorem hintBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.hintBitPack (hintBitPackContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h4, h5, hlr, hsp, hy⟩ := correct hp
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h4
      · exact h5
      rotate_right
      · exact hlr
      all_goals exact Exec.gpr (noWrite (by decide +kernel)) he
    · sig_post [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      exact hy
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, ha⟩ := hpub
    exact (all_ct ⟨hp₁, hp₂, hsp, hl, h0, h1, h2, h3, ha⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      rotate_right
      · rw [satArg, show (BitVec.setWidth 32 (BitVec.setWidth 64 (84 : BitVec 32))).toNat -
          (BitVec.setWidth 32 (BitVec.setWidth 64 (80 : BitVec 32))).toNat = 4 by decide,
          show BitVec.setWidth 64 (4096 : BitVec 32) = 0x1000 by decide, satHint]
        exact Nat.zero_le _
      all_goals decide +kernel

end VG.Proof.MlDsa.Arm.Pack.Hint
