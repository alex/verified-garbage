import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackMain
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintCT

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the lengths,
`ω`, the stack pointer and `y`, which the contract lets the function leak)
leak the same trace (`RelCT`), phase by phase: the load of `hlen` and the
return, with the reloads of the saved registers, access only the stack
(`RelCT.spBlock`); zeroing `h` is proved by the taint analysis; the
polynomials by `memTaint`, from the states narrowed to `y` and `h`
(`RelCT.narrow`), on which both runs agree once `h` is zeroed; and the bytes
after the last index likewise, from the states narrowed to `y`, which the
index, the same in both runs (that of the spec, from the same `y`), then
reads. What each run is at each point comes from the correctness proof
(`RelCT.wp`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

theorem pre_of {s : State} (h : (hintBitUnpackContract Arm.abi 16).pre s) : UPre s := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (coeffAddr p _) ht, ← coeffAt_eq, hz _ (by omega)]
  simp

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : UPre s₁
  hp₂ : UPre s₂
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (State.addr (uY s₁)) (uLen s₁)) = leakBytes (bytesAt s₂.mem (State.addr (uY s₂)) (uLen s₂))
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  arg : stackArg s₁ 0 = stackArg s₂ 0

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem yR_eq : uyR s₁ = uyR s₂ := by simp only [uyR, uY, uLen, uL, h.r0, h.r1]

theorem hR_eq : uhR s₁ = uhR s₂ := by simp only [uhR, uH, uHL, h.r3, h.arg]

theorem bytes_eq : bytesAt s₁.mem (State.addr (uY s₁)) (uLen s₁) = bytesAt s₂.mem (State.addr (uY s₂)) (uLen s₂) :=
  map_toNat_inj h.leak

theorem huS_eq : huS s₁ (uk s₁) = huS s₂ (uk s₂) := by
  unfold huS uYs
  rw [bytes_eq h]
  simp only [uk, uLen, uL, uω, uW, h.r1, h.r2]

/-- A byte of `y`, the same in both runs. -/
theorem yByte_eq {a b : State} (ha : ∀ t < uLen s₁, a.mem (State.addr (uY s₁) + BitVec.ofNat 64 t) =
      s₁.mem (State.addr (uY s₁) + BitVec.ofNat 64 t))
    (hb : ∀ t < uLen s₂, b.mem (State.addr (uY s₂) + BitVec.ofNat 64 t) = s₂.mem (State.addr (uY s₂) + BitVec.ofNat 64 t))
    {x : Addr} (hx : (uyR s₁).Contains x 1) : a.mem x = b.mem x := by
  have hlt : (x - State.addr (uY s₁)).toNat < uLen s₁ := by simp only [Region.Contains] at hx; omega
  have ea : x = State.addr (uY s₁) + BitVec.ofNat 64 (x - State.addr (uY s₁)).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have eY : uY s₂ = uY s₁ := by simp only [uY, h.r0]
  have eL : uLen s₂ = uLen s₁ := by simp only [uLen, uL, h.r1]
  have e := congrArg (·.getD (x - State.addr (uY s₁)).toNat 0) (bytes_eq h)
  rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ (show _ < uLen s₂ by rw [eL]; exact hlt), eY, ← ea] at e
  have h1 : a.mem x = s₁.mem x := by have := ha _ hlt; rwa [← ea] at this
  have h2 : b.mem x = s₂.mem x := by have := hb _ (by rw [eL]; exact hlt); rwa [eY, ← ea] at this
  rw [h1, h2]; exact e

/-- The polynomials, from the states narrowed to `y` and `h`. -/
theorem main_ct : RelCT isa (fun a b => UZ s₁ a ∧ UZ s₂ b) hbuMain fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [uyR s₁]) (fun _ => [uhR s₁]) (fun a b ⟨ha, hb⟩ => ?_)
    (fun a b ⟨ha, hb⟩ => ?_) ?_
  · have hra := uz_rd hp₁ ha
    have hwa := uz_wr hp₁ ha
    have hrb : uyR s₁ ∈ b.rd := by rw [yR_eq h]; exact uz_rd hp₂ hb
    have hwb : uhR s₁ ∈ b.wr := by rw [hR_eq h]; exact uz_wr hp₂ hb
    exact ⟨Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hra
        · exact List.mem_append_right _ hwa,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwa,
      Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hrb
        · exact List.mem_append_right _ hwb,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwb⟩
  · obtain ⟨a0, a1, a2, a3, a6, az, -⟩ := id ha
    obtain ⟨b0, b1, b2, b3, b6, bz, -⟩ := id hb
    obtain ⟨t₁, u₁, e₁, -⟩ := main_ok hp₁ (mainPre_of hp₁ ha (rd := [uyR s₁]) (wr := [uhR s₁])
      (List.mem_singleton_self _) (List.mem_singleton_self _)) a0 a1 a2 a3 a6 az
    obtain ⟨t₂, u₂, e₂, -⟩ := main_ok hp₂ (mainPre_of hp₂ hb (rd := [uyR s₁]) (wr := [uhR s₁])
      (by rw [yR_eq h]; exact List.mem_singleton_self _) (by rw [hR_eq h]; exact List.mem_singleton_self _))
      b0 b1 b2 b3 b6 bz
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2, .r3, .r6])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, fun x ⟨r, hr, hc⟩ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simp only [State.withRegions_gpr, ha.1, hb.1, uY, h.r0]
      · simp only [State.withRegions_gpr, ha.2.1, hb.2.1]
      · simp only [State.withRegions_gpr, ha.2.2.1, hb.2.2.1, uW, h.r2]
      · simp only [State.withRegions_gpr, ha.2.2.2.1, hb.2.2.2.1, uH, h.r3]
      · simp only [State.withRegions_gpr, ha.2.2.2.2.1, hb.2.2.2.2.1, uk, uLen, uL, uω, uW, h.r1, h.r2]
    · simp only [State.withRegions_rd, State.withRegions_wr, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact yByte_eq h (uz_y h.hp₁ ha (Frame.refl _ _)) (uz_y h.hp₂ hb (Frame.refl _ _)) hc
      · show a.mem x = b.mem x
        rw [byte_of_zero_words (N := (uHL s₁).toNat) (fun t ht => ha.2.2.2.2.2.1 t (by rw [hp₁.hlen] at ht; exact ht)) hc,
          byte_of_zero_words (N := (uHL s₂).toNat) (fun t ht => hb.2.2.2.2.2.1 t (by rw [hp₂.hlen] at ht; exact ht))
            (show (uhR s₂).Contains x 1 by rw [← hR_eq h]; exact hc)]

omit h in
/-- The loop over the trailing bytes runs from the states after the
polynomials, narrowed to `rd` and `wr` (and from the actual one): whichever
way the checks went. -/
theorem trail_run {s₀ : State} (hp : UPre s₀) {a : State} (hm : UM s₀ a) {rd wr : List Region}
    (hr : uyR s₀ ∈ rd) : WP isa hbuTrail (a.withRegions rd wr) fun _ => True := by
  obtain ⟨hY, hc⟩ := um_trail hp hm (wr := wr) hr
  obtain ⟨-, -, -, hst⟩ := hm
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    exact WP.mono (trail_fail hp hc hst) fun _ _ => trivial
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    exact WP.mono (trail_ok hp hY hst.2.1 hc hst.1) fun _ _ => trivial

omit h in
theorem trail_sp {s₀ : State} (hp : UPre s₀) {a : State} (hm : UM s₀ a) :
    WP isa hbuTrail a fun s' => s'.sp = (P1 s₀).sp := by
  obtain ⟨sa, hz, hc, hst⟩ := hm
  have hA := mainPre_of hp hz (rd := sa.rd) (wr := sa.wr) (uz_rd hp hz) (uz_wr hp hz)
  rw [State.withRegions_self] at hA
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    exact WP.mono (trail_fail hp hc hst) fun s' h' => h'.1.sp.trans hz.2.2.2.2.2.2.2.2.2
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    exact WP.mono (trail_ok hp hA.toYPre hst.2.1 hc hst.1) fun s' h' => h'.1.sp.trans hz.2.2.2.2.2.2.2.2.2

/-- The bytes after the last index, from the states narrowed to `y`. -/
theorem trail_ct : RelCT isa (fun a b => UM s₁ a ∧ UM s₂ b) hbuTrail fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [uyR s₁]) (fun _ => []) (fun a b ⟨ha, hb⟩ => ?_)
    (fun a b ⟨ha, hb⟩ => ?_) ?_
  · obtain ⟨sa, hza, hca, -⟩ := ha
    obtain ⟨sb, hzb, hcb, -⟩ := hb
    have hra : uyR s₁ ∈ a.rd := by rw [hca.rd]; exact uz_rd hp₁ hza
    have hrb : uyR s₁ ∈ b.rd := by rw [hcb.rd, yR_eq h]; exact uz_rd hp₂ hzb
    refine ⟨fun x n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun _ _ ⟨_, hr, _⟩ => (nomatch hr),
      fun x n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun _ _ ⟨_, hr, _⟩ => (nomatch hr)⟩
    · simp only [List.append_nil, List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hra
    · simp only [List.append_nil, List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hrb
  · obtain ⟨t₁, u₁, e₁, -⟩ := trail_run hp₁ ha (rd := [uyR s₁]) (wr := []) (List.mem_singleton_self _)
    obtain ⟨t₂, u₂, e₂, -⟩ := trail_run hp₂ hb (rd := [uyR s₁]) (wr := [])
      (by rw [yR_eq h]; exact List.mem_singleton_self _)
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    obtain ⟨sa, hza, hca, hsa⟩ := ha
    obtain ⟨sb, hzb, hcb, hsb⟩ := hb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, fun x ⟨r, hr, hc⟩ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [State.withRegions_gpr, hca.r0, hcb.r0, uY, h.r0]
      · simp only [State.withRegions_gpr]
        rw [huS_eq h] at hsa
        revert hsa hsb
        cases huS s₂ (uk s₂) with
        | none => exact fun h₁ h₂ => h₁.trans h₂.symm
        | some st => obtain ⟨hA', idx⟩ := st; exact fun h₁ h₂ => h₁.1.trans h₂.1.symm
      · simp only [State.withRegions_gpr, hca.r2, hcb.r2, uW, h.r2]
    · simp only [State.withRegions_rd, State.withRegions_wr, List.append_nil, List.mem_singleton] at hr; subst hr
      exact yByte_eq h (uz_y hp₁ hza hca.frame) (uz_y hp₂ hzb hcb.frame) hc

/-- The body of the frame. -/
theorem body_ct : RelCT isa (fun a b => a = P1 s₁ ∧ b = P1 s₂) hintBitUnpackBody fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold hintBitUnpackBody
  refine RelCT.seq (R := fun a b => UZ s₁ a ∧ UZ s₂ b) (relct_wp ?_ fun a b ⟨ea, eb⟩ =>
    ⟨by rw [ea]; exact zeroP_ok hp₁, by rw [eb]; exact zeroP_ok hp₂⟩) ?_
  · refine RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r1, .r2, .r3, .r12])
      (fun a b ⟨ea, eb⟩ => Taint.agree_ofRegs fun r hr => ?_) (by taint_decide)
    subst ea eb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r1]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r2]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r3]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, uHL, h.arg]; rfl
  refine RelCT.seq (R := fun a b => UM s₁ a ∧ UM s₂ b) (relct_wp (main_ct h) fun a b hab =>
    ⟨mainP_ok hp₁ hab.1, mainP_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => a.sp = (P1 s₁).sp ∧ b.sp = (P1 s₂).sp)
    (relct_wp (trail_ct h) fun a b hab => ⟨trail_sp hp₁ hab.1, trail_sp hp₂ hab.2⟩) ?_
  exact Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by
    rw [ea, eb]; simp only [P1, pushed_sp, RegUpd.sp_setReg, h.sp]

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) Impl.MlDsa.Arm.Pack.hintBitUnpack fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold Impl.MlDsa.Arm.Pack.hintBitUnpack
  refine RelCT.seq (R := fun a b => a = s₁.setReg .r12 (uHL s₁) ∧ b = s₂.setReg .r12 (uHL s₂))
    (relct_wp (Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by rw [ea, eb, h.sp]) fun a b ⟨ea, eb⟩ =>
      ⟨by rw [ea]; exact entry_ok (by rw [hp₁.rd]; exact ⟨uargR s₁, by simp, Region.contains_self _ _⟩),
       by rw [eb]; exact entry_ok (by rw [hp₂.rd]; exact ⟨uargR s₂, by simp, Region.contains_self _ _⟩)⟩) ?_
  refine RelCT.frame (fun a b ⟨ea, eb⟩ => by rw [ea, eb]; simp only [RegUpd.sp_setReg, h.sp]) ?_
  refine RelCT.mono (body_ct h) (fun a b ⟨x, y, ⟨ex, ey⟩, px, py⟩ => ?_) fun _ _ h => h
  subst ex ey
  exact ⟨(push_pushed' px).1, (push_pushed' py).1⟩

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

/-- The memory of the satisfying state: `hlen = 1024` on the stack. -/
def unpackSatMem : Mem := fun a => if a = 0x8001 then 4 else 0

/-- A state satisfying the precondition. -/
def unpackSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 84 | .r2 => 80 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := unpackSatMem
  rd := [⟨0x1000, 84⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.hintBitUnpack (hintBitUnpackContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := Unpack.pre_of hs
    obtain ⟨t, s', he, h4, h5, h6, h7, hlr, hsp, hr⟩ := Unpack.correct hp
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      rotate_right
      · exact hlr
      all_goals exact Exec.gpr (noWrite (by decide +kernel)) he
    · sig_post [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [VG.Proof.MlKem.Arm.setWidth_append32]
      exact hr
  · have hp₁ := Unpack.pre_of h₁
    have hp₂ := Unpack.pre_of h₂
    sig_pub [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, ha⟩ := hpub
    exact (Unpack.all_ct ⟨hp₁, hp₂, hsp, hl, h0, h1, h2, h3, ha⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨unpackSatState, ?_⟩
    sig_sat_check [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Pack.Hint
