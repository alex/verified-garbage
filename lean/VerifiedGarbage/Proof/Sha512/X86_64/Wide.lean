import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Sha512.X86_64.Compress

/-!
# SHA-512 compression on x86-64 with the shared contract's scratch space

`compressWideX86_64` is `compressX86_64` with the 1328 bytes of scratch space
that the shared contract (`Spec.Sha512.compressContract`) gives the
compression function, and that the streaming functions pass it
(`Impl.Sha512.X86_64.Stream.params`): every implementation is proven against
it, the scalar one by widening its own proof (`Verified.widen`, the same code
running with the same trace and result).
-/

namespace VG.Proof.Sha512

open VG.X86_64 in
/-- `compressX86_64` with 1328 bytes of scratch. -/
def compressWideX86_64 : Contract X86_64.isa :=
  { compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 64⟩
      let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 1328⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

end VG.Proof.Sha512

namespace VG.Proof.Sha512.X86_64

open _root_.VG.X86_64

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWideX86_64.pre`. -/
def wideSat : State := { satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

theorem compressWide_verified :
    Verified X86_64.target Impl.Sha512.X86_64.compress Proof.Sha512.compressWideX86_64 :=
  Verified.widen compress_verified
    (fun s => [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 176⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub176 _), h₄, h₅.sub_right (sub176 _), h₆, h₇.sub_right (sub176 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    ⟨wideSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

end VG.Proof.Sha512.X86_64
