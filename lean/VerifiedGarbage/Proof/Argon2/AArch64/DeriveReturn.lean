import VerifiedGarbage.Proof.Argon2.AArch64.DeriveBodySaved
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveRestore

/-! The nested ABI frames return the complete result and restore all saved registers. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def wholeWrites (s : State) : List Region := [abiMatrix s, abiWork s, abiOutput s, below (s.sp) 400]

theorem BodyDone.whole_frame {s t : State} (h : AbiEnvironment s) (done : BodyDone s t) :
    Frame (wholeWrites s) s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ (s.sp).toNat; omega)
  apply (prologue.sub ?_).trans (done.frame.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨below (s.sp) 400, by simp [wholeWrites], below_sub (by decide) (by decide)⟩
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [wholeWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [wholeWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [wholeWrites], fun _ h => h⟩
    · refine ⟨below (s.sp) 400, by simp [wholeWrites], ?_⟩
      rw [prologue_sp]
      exact Offset.sub_below _ (by decide) (by decide)
    · refine ⟨below (s.sp) 400, by simp [wholeWrites], ?_⟩
      rw [prologue_sp]
      unfold below
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Region.sub_prefix (by decide)

theorem return_post {s t : State} (done : BodyDone s t) :
    (Spec.Argon2.deriveContract AArch64.abi 400).post s (frameEnd t Impl.Argon2.AArch64.Derive.saved) := by
  have post := done.post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop]
  exact post

theorem code_wp (v : HPrime.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    WP isa (Impl.Argon2.AArch64.Derive.code name v.hash) s fun t =>
      (Spec.Argon2.deriveContract AArch64.abi 400).post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ Frame (wholeWrites s) s.mem t.mem := by
  have h := abi_environment s pre
  unfold Impl.Argon2.AArch64.Derive.code
  apply frame_ok s Impl.Argon2.AArch64.Derive.saved _ _
    (by have space := h.stack; change 384 ≤ (s.sp).toNat; omega)
  refine (body_ok v name s h).mono ?_
  intro t done
  refine ⟨done.sp, done.wr, return_post done, ?_, ?_, ?_⟩
  · have restored := frame_restored s t Impl.Argon2.AArch64.Derive.saved (by decide)
      (by have space := h.stack; change 384 ≤ (s.sp).toNat; omega) done.sp
      (fun j hj => done.saved h j hj)
    intro r hr
    have member : ∀ r ∈ preserved,
        r ∈ Impl.Argon2.AArch64.Derive.saved ∨ r ∈ [Reg.x25, .x26, .x27, .x28] := by decide
    rcases member r hr with hr | hr
    · exact restored r hr
    · have other : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
          r ∉ Impl.Argon2.AArch64.Derive.saved := by decide
      exact (frameEnd_reg t _ r (other r hr)).trans (done.unused r hr)
  · exact (frameEnd_metadata s t Impl.Argon2.AArch64.Derive.saved done.sp done.wr).1
  · rw [frameEnd_mem]
    exact done.whole_frame h

end VG.Proof.Argon2.AArch64.Derive
