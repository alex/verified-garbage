import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifySetup
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain

/-! Untrusted: verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 64⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 64) (bytesAt s.mem (s.gpr .x2) 64))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    bytesAt s.mem (s.gpr .x0) 32 = bytesAt t.mem (t.gpr .x0) 32 ∧
    bytesAt s.mem (s.gpr .x1) 64 = bytesAt t.mem (t.gpr .x1) 64 ∧
    bytesAt s.mem (s.gpr .x2) 64 = bytesAt t.mem (t.gpr .x2) 64

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  saved : Saved (s.gpr .x3) s.gpr t.mem
  frame : Frame [⟨s.gpr .x3, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], t.gpr r = s.gpr r

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hn⟩ := hs
  have hws : (⟨s.gpr .x3, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok asc (ka.wr ▸ hws)) fun b ⟨gb, rb, wb, spb, mb, svb⟩ => ?_
  have bs : b.gpr .x2 = s.gpr .x3 := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.wr]; exact hws))
    fun c ⟨cs, gc, rc, wc, spc, mc, cp, cr, cc⟩ => ?_
  have fm : Frame [⟨s.gpr .x3, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.mem] at f
    exact f
  have sv : Saved (s.gpr .x3) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.gpr
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.rd)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.wr)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.gpr .x0 (by decide)]
    · rw [cr, gb, ka.gpr .x1 (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .x1) 32) d = off (s.gpr .x1) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi; exact farScr hpk hi (by decide)
    · intro i hi; exact farScr hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact farScr hsig (by omega) (by decide)
    · intro i hi; exact farScr hchallenge hi (by decide)
  refine ⟨hc, sv, fm, spc.trans (spb.trans ka.sp), fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rw [gc _ (by decide), gb, ka.gpr _ (by decide)]

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  apply WP.withPreservedV (hc := by decide +kernel)
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ev, ke⟩ => ?_
  have er : e.gpr .x2 = s.gpr .x3 := es.trans (kd.scratch hc.scratch).x0
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.wr, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.mem]; exact svd)) fun t ⟨tr, kt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.x19, 0) (by decide)
    · exact tr (.x20, 8) (by decide)
    · exact tr (.x21, 16) (by decide)
    · exact tr (.x22, 24) (by decide)
    · exact tr (.x23, 32) (by decide)
    · exact tr (.x24, 40) (by decide)
    all_goals
      rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide) (by decide) (by decide)]
      exact hc0.regs _ (by decide)
  · exact kt.sp.trans (ke.sp.trans (kd.sp.trans hc0.sp))
  · change t.gpr .x0 = _
    rw [kt.gpr _ (by decide), ev, dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.AArch64
