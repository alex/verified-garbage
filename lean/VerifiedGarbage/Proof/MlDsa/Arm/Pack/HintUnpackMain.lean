import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackLoops

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, correct

Untrusted: everything here is checked by Lean. The whole function: the load
of `hlen`, the frame, and in it zeroing `h`, the loops
(`HintUnpackLoops.lean`), the return value and the reloads of the saved
registers; the result is `HintBitUnpack` (Algorithm 21) through its fold form
(`hintBitUnpack_eq`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state the body runs from. -/
abbrev P1 (s₀ : State) : State := pushed [.r4, .r5, .r6, .r7] (s₀.setReg .r12 (uHL s₀))

/-- The state after zeroing `h`. -/
def UZ (s₀ a : State) : Prop :=
  a.gpr .r0 = uY s₀ ∧ a.gpr .r1 = 0 ∧ a.gpr .r2 = uW s₀ ∧ a.gpr .r3 = uH s₀ ∧
    a.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧ (∀ t < 256 * uk s₀, coeffAt a.mem (State.addr (uH s₀)) t = 0) ∧
    Frame [uhR s₀] (P1 s₀).mem a.mem ∧ a.rd = (P1 s₀).rd ∧ a.wr = (P1 s₀).wr ∧ a.sp = (P1 s₀).sp

/-- The state after the polynomials, in the run from `sa`. -/
def UM (s₀ a : State) : Prop :=
  ∃ sa, UZ s₀ sa ∧ UCom s₀ sa a ∧ SRel s₀ (huS s₀ (uk s₀)) a

/-- The result. -/
def UPost (s₀ : State) (m : Mem) (r : BitVec 32) : Prop :=
  match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)) with
  | some hint => r = 1 ∧ HintIs m (State.addr (uH s₀)) (uk s₀) hint
  | none => r = 0

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem hsp16 : 4 * [Reg.r4, Reg.r5, Reg.r6, Reg.r7].length ≤ (s₀.setReg .r12 (uHL s₀)).sp.toNat := hp.sp

theorem hfr : frameR (s₀.setReg .r12 (uHL s₀)) [.r4, .r5, .r6, .r7] = ⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩ :=
  frameR_eq [.r4, .r5, .r6, .r7] (s := s₀.setReg .r12 (uHL s₀)) hp.sp

theorem zeroP_ok : WP isa hbuZero (P1 s₀) (UZ s₀) :=
  zero_ok hp rfl rfl rfl rfl rfl (by simp [RegUpd.wr_setReg, hp.wr])

/-- The body changes memory only in the frame and `h`. -/
theorem uz_frame {a : State} (hz : UZ s₀ a) :
    Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩, uhR s₀] s₀.mem a.mem := by
  have hpf := pushed_frame [.r4, .r5, .r6, .r7] (hsp16 hp)
  rw [hfr hp] at hpf
  exact (hpf.mono (by simp)).trans (hz.2.2.2.2.2.2.1.mono (by simp))

/-- The bytes of `y`, after zeroing `h`, and after the loops. -/
theorem uz_y {a : State} (hz : UZ s₀ a) {m : Mem} (hm : Frame [uhR s₀] a.mem m) :
    ∀ t < uLen s₀, m (State.addr (uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) := by
  intro t ht
  have fY := hp.fitY
  have hc : (uyR s₀).Contains (State.addr (uY s₀) + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [hm _ fun r hr hc' => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.d_yh _ hc hc',
    uz_frame hp hz _ fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.b_y _ hc' hc
      · exact hp.d_yh _ hc hc']

theorem mainPre_of {a : State} (hz : UZ s₀ a) {rd wr : List Region} (hr : uyR s₀ ∈ rd) (hw : uhR s₀ ∈ wr) :
    MainPre s₀ (a.withRegions rd wr) := ⟨⟨hr, uz_y hp hz (Frame.refl _ _)⟩, hw⟩

theorem uz_rd {a : State} (hz : UZ s₀ a) : uyR s₀ ∈ a.rd := by
  rw [hz.2.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp.rd]

theorem uz_wr {a : State} (hz : UZ s₀ a) : uhR s₀ ∈ a.wr := by
  rw [hz.2.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp.wr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem mainP_ok {a : State} (hz : UZ s₀ a) : WP isa hbuMain a (UM s₀) := by
  obtain ⟨a0, a1, a2, a3, a6, az, -⟩ := id hz
  have := mainPre_of hp hz (rd := a.rd) (wr := a.wr) (uz_rd hp hz) (uz_wr hp hz)
  rw [State.withRegions_self] at this
  exact WP.mono (main_ok hp this a0 a1 a2 a3 a6 az) fun s' ⟨hc, hs⟩ => ⟨a, hz, hc, hs⟩

/-- The start of the loop over the trailing bytes, narrowed to `y`. -/
theorem um_trail {a : State} (hm : UM s₀ a) {rd wr : List Region} (hr : uyR s₀ ∈ rd) :
    YPre s₀ (a.withRegions rd wr) ∧ UCom s₀ (a.withRegions rd wr) (a.withRegions rd wr) := by
  obtain ⟨sa, hz, hc, -⟩ := hm
  exact ⟨⟨hr, uz_y hp hz hc.frame⟩, hc.r0, hc.r2, rfl, rfl, rfl, Frame.refl _ _⟩

end

theorem ret_blk {s : State} (i5 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4)
    (i6 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (i7 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4) :
    WP isa (.block hbuRet) s fun s' => s'.gpr .r0 = 1 - ((s.gpr .r2 - s.gpr .r1) >>> 31) ∧
      s'.gpr .r5 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  run_block [hbuRet, i5, i6, i7]
  exact ⟨rfl, trivial⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {s₀ : State} {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) :
    HintIs m (State.addr (uH s₀)) (uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

theorem ret_val (ω x : Nat) (hω : ω ≤ 80) (hx : x < 2 ^ 31) :
    (1 : BitVec 32) - ((BitVec.ofNat 32 ω - BitVec.ofNat 32 x) >>> 31) = if ω < x then 0 else 1 := by
  rw [ltBit_val (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  split <;> rfl

theorem fail_val {s₀ : State} (hp : UPre s₀) : (1 : BitVec 32) - ((uW s₀ - 256) >>> 31) = 0 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  have e := ret_val (uω s₀) 256 hω80 (by decide)
  rw [ite_pos' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

/-- The body of the frame: the result, the reloads of `r5`–`r7`, and the word
the pop reloads into `r4`. -/
theorem body_ok {s₀ : State} (hp : UPre s₀) :
    WP isa hintBitUnpackBody (P1 s₀) fun s₂ => s₂.sp = (P1 s₀).sp ∧ s₂.gpr .r5 = s₀.gpr .r5 ∧
      s₂.gpr .r6 = s₀.gpr .r6 ∧ s₂.gpr .r7 = s₀.gpr .r7 ∧ s₂.mem.readW (State.addr s₂.sp) 32 = s₀.gpr .r4 ∧
      UPost s₀ s₂.mem (s₂.gpr .r0) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  have hsp := hsp16 hp
  unfold hintBitUnpackBody
  refine WP.seq (WP.mono (zeroP_ok hp) fun sa hz => ?_)
  refine WP.seq (WP.mono (mainP_ok hp hz) fun sb hm => ?_)
  obtain ⟨sa', hz', hcb, hst⟩ := id hm
  have hA := mainPre_of hp hz' (rd := sa'.rd) (wr := sa'.wr) (uz_rd hp hz') (uz_wr hp hz')
  rw [State.withRegions_self] at hA
  -- What the trailing bytes and the return leave, whichever way the checks went.
  suffices h : WP isa hbuTrail sb fun sc => UCom s₀ sa' sc ∧ UPost s₀ sc.mem (1 - ((sc.gpr .r2 - sc.gpr .r1) >>> 31)) by
    refine WP.seq (WP.mono h fun sc ⟨hcc, hpc⟩ => ?_)
    have hfc : Frame [uhR s₀] (P1 s₀).mem sc.mem := hz'.2.2.2.2.2.2.1.trans hcc.frame
    have hdh : ∀ r ∈ [uhR s₀], (frameR (s₀.setReg .r12 (uHL s₀)) [.r4, .r5, .r6, .r7]).Disjoint r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hfr hp]; exact hp.b_h
    have hsc : sc.sp = (P1 s₀).sp := by rw [hcc.sp, hz'.2.2.2.2.2.2.2.2.2]
    have hin : ∀ i < 4, InRegions (sc.rd ++ sc.wr) (State.addr (sc.sp + BitVec.ofNat 32 (4 * i))) 4 := fun i hi => by
      rw [hcc.wr, hz'.2.2.2.2.2.2.2.2.1, pushed_wr, hsc]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains [.r4, .r5, .r6, .r7] hsp hi⟩
    refine WP.mono (ret_blk (hin 1 (by decide)) (hin 2 (by decide)) (hin 3 (by decide)))
      fun sd ⟨r0d, r5d, r6d, r7d, md, spd⟩ => ⟨by rw [spd, hsc], ?_, ?_, ?_, ?_, by rw [md, r0d]; exact hpc⟩
    · rw [r5d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 1) (by decide)]; rfl
    · rw [r6d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 2) (by decide)]; rfl
    · rw [r7d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 3) (by decide)]; rfl
    · rw [md, spd, hsc, show State.addr (P1 s₀).sp = State.addr ((P1 s₀).sp + BitVec.ofNat 32 (4 * 0)) by simp,
        frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 0) (by decide)]; rfl
  unfold UPost
  rw [hintBitUnpack_eq]
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    have hst : sb.gpr .r1 = 256 := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = none from hS]
    refine WP.mono (trail_fail hp hcb hst) fun sc ⟨hcc, _, r1c⟩ => ⟨hcc, ?_⟩
    show _ = 0
    rw [hcc.r2, r1c]
    exact fail_val hp
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = some (hA', idx) from hS]
    refine WP.mono (trail_ok hp hA.toYPre hidx hcb h1) fun sc ⟨hcc, mc, hr⟩ => ⟨hcc, ?_⟩
    dsimp only
    revert hr
    cases optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      intro r1c
      show _ = 0
      rw [hcc.r2, r1c]
      exact fail_val hp
    | some _ =>
      intro r1c
      refine ⟨?_, by rw [mc]; exact harr_hintIs hh⟩
      rw [hcc.r2, r1c, ← eω, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self]
      rfl

/-- The whole function: the result, and the registers it saves and restores
(the others it never writes). -/
theorem correct {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitUnpack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧
      s'.gpr .r6 = s₀.gpr .r6 ∧ s'.gpr .r7 = s₀.gpr .r7 ∧ s'.gpr .lr = s₀.gpr .lr ∧ s'.sp = s₀.sp ∧
      UPost s₀ s'.mem (s'.gpr .r0) := by
  unfold Impl.MlDsa.Arm.Pack.hintBitUnpack
  refine WP.seq (WP.mono (entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨uargR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.frame (rs := [.r4, .r5, .r6, .r7]) (r := .r4) rfl (hsp16 hp) (by decide)
    (WP.mono (WP.gpr (body_ok hp) (r := .lr) (noWrite (by decide +kernel))) fun s₂ ⟨⟨hsp, h5, h6, h7, h4, hr⟩, hlr⟩ => ?_)
  refine ⟨?_, by rw [popped_gpr (by decide), h5], by rw [popped_gpr (by decide), h6], by rw [popped_gpr (by decide), h7],
    by rw [popped_gpr (by decide), hlr]; rfl, ?_, by rw [popped_mem, popped_gpr (by decide)]; exact hr⟩
  · simp only [popped, State.setReg, ite_true]; exact h4
  · simp only [popped_sp, hsp, P1, pushed_sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack
