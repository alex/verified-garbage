import VerifiedGarbage.Proof.Ed25519.X86_64.VerifySetup
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain

/-! Untrusted: verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 64⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 64) (bytesAt s.mem (s.gpr .rdx) 64))
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧
    bytesAt s.mem (s.gpr .rdi) 32 = bytesAt t.mem (t.gpr .rdi) 32 ∧
    bytesAt s.mem (s.gpr .rsi) 64 = bytesAt t.mem (t.gpr .rsi) 64 ∧
    bytesAt s.mem (s.gpr .rdx) 64 = bytesAt t.mem (t.gpr .rdx) 64

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
  saved : Saved (s.gpr .rcx) s.gpr t.mem
  frame : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem
  rsp : t.gpr .rsp = s.gpr .rsp

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hret, hn⟩ := hs
  have hws : (⟨s.gpr .rcx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok asc (ka.2.2.2 ▸ hws)) fun b ⟨gb, rb, wb, mb, svb⟩ => ?_
  have bs : b.gpr .rdx = s.gpr .rcx := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.2.2.2]; exact hws))
    fun c ⟨cs, gc, rc, wc, mc, cp, cr, cc⟩ => ?_
  have fm : Frame [⟨s.gpr .rcx, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.2.1] at f
    exact f
  have sv : Saved (s.gpr .rcx) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.1
    simp only [Impl.X25519.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.2.2.1)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.2.2.2)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.1 .rdi (by decide)]
    · rw [cr, gb, ka.1 .rsi (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .rsi) 32) d = off (s.gpr .rsi) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi; exact farScratch hpk hi (by decide)
    · intro i hi; exact farScratch hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact farScratch hsig (by omega) (by decide)
    · intro i hi; exact farScratch hchallenge hi (by decide)
  exact ⟨hc, sv, fm, by rw [gc _ (by decide), gb, ka.1 _ (by decide)]⟩

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa (verifyEquation fld dbl) s fun t => gprPreserved s t ∧ verifyLocal.post s t := by
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  have hret := hs.2.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ke⟩ => ?_
  have er : e.gpr .rdx = s.gpr .rcx := es.trans (kd.scratch hc.scratch).rdi
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.2.2.2, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.2.1]; exact svd)) fun t ⟨tr, gt, mt, _, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.rbx, 0) (by decide)
    · exact tr (.rbp, 8) (by decide)
    · rw [gt _ (by decide), ke.1 _ (by decide), kd.gpr _ (by decide) (by decide) (by decide),
        hc0.rsp]
    · exact tr (.r12, 16) (by decide)
    · exact tr (.r13, 24) (by decide)
    · exact tr (.r14, 32) (by decide)
    · exact tr (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem := by
      rw [mt, ke.2.1]; exact fm.trans (scratchFrame md (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  · change t.gpr .rax = _
    rw [gt _ (by decide), ke.1 _ (by decide), dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.X86_64
