import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopKem
import VerifiedGarbage.Proof.MlKem.X86.Extra
import VerifiedGarbage.Impl.MlKem.X86.KeyGen

/-!
# ML-KEM on x86 (32-bit): the setting of key generation

The layout of the arguments (`Y L`: `seed`, `ek`, `dk`, `scratch`, and the
88 bytes of stack), which each parameter set's contract implies; the public
data, which includes `ρ`; and `d`, `z` and the values the body computes from
them.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `seed` (64 bytes, read), `ek`, `dk` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay := ⟨[(64, false), (L.p.ekLen, true), (L.p.dkLen, true), (L.scratch, true)], 3, 88⟩

section
variable (s₀ : State)
/-- `d`. -/
abbrev d : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `z`. -/
abbrev z : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 32, 32⟩) 32
end

/-- What keygen may leak: `ρ`. -/
abbrev lk (L : KemLay) (s₀ : State) : List Byte := KPke.kgRho L.p (d s₀)

theorem addr0 (s₀ : State) (i : Nat) : Buf.addr s₀ ⟨i, 0, 32⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- A taint check of code with `scratch` at `(Y L).sc`, through `esi`. -/
macro "yk_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 3 from fun _ => rfl]); (try simp only
  [ptrTo, reduceIte, Nat.reduceEqDiff, List.cons_append, List.nil_append]); taint_rfl))

end VG.Proof.MlKem.X86.KeyGen
