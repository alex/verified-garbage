import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Double4
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT

/-! Merged from `Proof.Ed25519.X86_64.Ifma.Lit`. -/
section
/-! A checked literal for the doublings with AVX512_IFMA. -/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64

materialize_code double4Lit := (Impl.Ed25519.X86_64.Ifma.double4 : Prog isa)

end VG.Proof.Ed25519.X86_64.Ifma
end

/-!
# Ed25519 doublings with AVX512_IFMA in verification's windows

`Ifma.double4` is four doublings as a window runs them (`EdDouble`): it
represents `16a` in slots 0–3, keeps the slots from 16 up and what `WinKeep`
keeps, and its trace depends on the scratch's address alone.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Ed25519.X86_64

theorem double4_ct :
    RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) Impl.Ed25519.X86_64.Ifma.double4 (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

instance : EdDouble Impl.Ed25519.X86_64.Ifma.double4 :=
  ⟨fun hs ha => WP.mono (double4_ok hs ha) fun _ ⟨r, h, g, rd, wr, m⟩ =>
    ⟨r, h, ⟨fun r hr _ hs => g r hr hs, rd, wr, m⟩⟩, double4_ct⟩

end VG.Proof.Ed25519.X86_64.Ifma
