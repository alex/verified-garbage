import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common

/-!
# Streaming SHA-256 on x86-64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/X86_64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/X86_64/`) for SHA-256's
instance (`Proof/Sha256/Md.lean`), for any implementation `f` of the
compression function (`Callee.Ok`), given what SHA-256's own pieces do: its
length field and digest (`shape`) and that the taint analysis accepts its
code between the calls (`taints`).
-/

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)
open VG.Impl.Sha256.X86_64.Stream (Callee update finalize)
open VG.Proof.Sha256.Stream (writeBytes write_eq_writeBytes)

abbrev params := Impl.Sha256.X86_64.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len s hout := by
    rw [show params.len = len64 88 true ++ [] from rfl]
    exact len64_ok hout fun s' g rd wr m => WP.block_nil ⟨g, rd, wr, m⟩
  out s hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem callee {f : Callee} (hf : f.Ok) : CalleeOk (P := params) md f.code :=
  ⟨hf.verified, hf.ct, hf.nosp, hf.depth, hf.keeps_rdi, hf.keeps_rcx⟩

namespace Update

variable {f : Callee} (hf : f.Ok)
include hf

/-- `update` is verified if it never loads MXCSR. -/
theorem verified_of (hm : (update f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update f) Proof.Sha256.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified dims taints (callee hf) hm
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

omit hf

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

theorem pre_of {s₀ : State} (h : Proof.Sha256.finalizeX86_64.pre s₀) : MdStream.X86_64.Finalize.Pre params s₀ :=
  MdStream.X86_64.Finalize.pre_of (H := md) h

variable {f : Callee} (hf : f.Ok)
include hf

theorem correct {s₀ : State} (hp : MdStream.X86_64.Finalize.Pre params s₀) :
    WP isa (finalize f) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.finalizeX86_64.post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx :=
  (MdStream.X86_64.Finalize.correct dims shape (callee hf) hp).mono fun _ ⟨g, h, di, cx⟩ =>
    ⟨g, fun iv m hr hc => h iv m hr trivial hc, di, cx⟩

theorem constantTime :
    ConstantTime isa Proof.Sha256.finalizeX86_64.pre Proof.Sha256.finalizeX86_64.pub (finalize f) :=
  MdStream.X86_64.Finalize.constantTime dims shape taints (callee hf)

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified_of (hm : (finalize f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize f) Proof.Sha256.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified dims shape taints (callee hf) hm
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

omit hf

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

theorem writeW_bswap32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (bswap32 w) = writeBytes m a (Spec.Sha256.wordBytes w) :=
  writeW32 m a true w

theorem flat_length (H : Spec.Sha256.HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap Spec.Sha256.wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (Spec.Sha256.wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

end Finalize

end VG.Proof.Sha256.X86_64.Stream
