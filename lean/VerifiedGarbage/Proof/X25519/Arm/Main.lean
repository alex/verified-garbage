import VerifiedGarbage.Proof.X25519.Arm.Bits
import VerifiedGarbage.TCB.Arm.Target

/-!
# X25519 on 32-bit ARM: the whole function

Untrusted: everything here is checked by Lean. `vg_x25519` writes
`X25519(k, u)` to `out` (`x25519_correct`), restoring the callee-saved
registers.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes toFe ladderAfter ladderAfter_swap_le)
open Fin.CommRing

/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it.
`vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`. -/
def x25519Arm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let sc : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pt : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 4096⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) 32 =
    VG.Spec.X25519.x25519 (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem XPre.of {s : State} (h : x25519Arm.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section
variable {b : BitVec 32}

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 sw) {v : Nat → Fe} (hS : SlotsOk s.mem (State.addr b) LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem (State.addr b) LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have hr2 : Rest [.r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e9 : s2.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [u2.gpr]; show s1.gpr .r9 - s1.gpr .r10 = _
    rw [u1.gpr, u1.other _ (by decide), h10]
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (qs := LQ) (v := v) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e9 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e9]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

theorem restore_ok {s : State} (hc : Ctx b s) {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  have h0 : ∀ i < 8, savedReg i ≠ .r0 := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

theorem FA_saved (i : Nat) (hi : i < 8) :
    Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ (FA b) :=
  Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m (State.addr b) qs v)
    (hq : (qs.all fun q => q + 64 ≤ BITS) = true)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] m m') : SlotsOk m' (State.addr b) qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1280 := rfl
  have e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  exact ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, by rw [FS, V, val16_congr e]; exact (hS q hq').2⟩

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 32⟩ r) : bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

theorem x25519_correct {s : State} (hp : XPre s) :
    WP isa x25519 s fun s' => abiPreserved s s' ∧ x25519Arm.post s s' := by
  have hfit := hp.f3
  have hB : BITS = 1280 := rfl
  have hsc_in : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, h12, h1, hsv1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 h1 hp.f1 (by rw [hr1.rd, hr1.wr]; exact hsc_in) hp.sc_ws)
    fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h10, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h10 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide) (by decide) hc5 hS5)
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : Stp (s.gpr .r3) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have h12' : s6.gpr .r12 = s.gpr .r0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), h12]
  have hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  have hc6 : Ctx (s.gpr .r3) s6 := hc5.of_rest hr6 (by decide)
  refine WP.append (freeze_ok hc6 (hS6 X2 (by decide)).1 h12' (by rw [hwr6, hp.wr]; simp) hp.f0
    hp.out_ws.symm) fun s7 ⟨hbytes, hr7, hf7⟩ => ?_
  have hc7 : Ctx (s.gpr .r3) s7 := hc6.of_rest hr7 (by decide)
  -- The saved registers.
  have hsv7 : Saved (State.addr (s.gpr .r3)) s.gpr s7.mem := by
    refine ((hsv1.frame hf2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)).frame
      hst6.frame fun r hr i hi => by rw [List.mem_singleton.mp hr]; exact FA_saved i hi).frame hf7 fun r hr i hi => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact FA_saved i hi
    · exact (hp.out_ws.symm.sub_left (Offset.sub_base _ (by omega))).symm.symm
  refine WP.mono (restore_ok hc7 hsv7) fun s8 ⟨hg8, hr8, hm8⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg8 0 (by decide)
    · exact hg8 1 (by decide)
    · exact hg8 2 (by decide)
    · exact hg8 3 (by decide)
    · exact hg8 4 (by decide)
    · exact hg8 5 (by decide)
    · exact hg8 6 (by decide)
    · exact hg8 7 (by decide)
    · rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide),
        hr1.gpr _ (by decide)]
  · rw [hr8.sp, hr7.sp, hst6.rest.sp, hr2.sp, hr1.sp]
  · -- The result.
    show bytesAt s8.mem _ 32 = _
    rw [hm8, hbytes, VG.Proof.X25519.x25519_eq]
    -- The scalar and the u-coordinate, as read by `bits` and `setup`.
    have hk : bytesAt s1.mem (State.addr (s.gpr .r1)) 32 = bytesAt s.mem (State.addr (s.gpr .r1)) 32 :=
      bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
    rw [hk] at hS3 h10 hS4 hS5 hS6
    have e6 : FS s6.mem (State.addr (s.gpr .r3)) X2 = _ := (hS6 X2 (by decide)).2
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
    change VG.Spec.X25519.encodeUCoordinate (FS s6.mem (State.addr (s.gpr .r3)) X2) = _
    rw [e6]
    simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_eq, cswap_fst,
      uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end VG.Proof.X25519.Arm
