import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT

/-! Merged from `Proof.Ed25519.X86_64.ScalarBasePrecomputedEngine`. -/
section
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs val4)

variable {fld : Arith} [EdArith fld]

/-- The encoding's value depends only on the point represented. -/
theorem encodedValue_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    encodedValue p = (a.y : Spec.X25519.Fe).val + ((a.x : Spec.X25519.Fe).val % 2) * 2 ^ 255 := by
  have hx : p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.x : Spec.X25519.Fe) := by
    show toZ (p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.x
    rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]
  have hy : p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.y : Spec.X25519.Fe) := by
    show toZ (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.y
    rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]
  simp only [encodedValue, hx, hy]
  rfl

theorem scalarBasePrecomputedEngine_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBasePrecomputedEngine fld) s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBasePrecomputedEngine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, _, bd, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (fld := fld) (kab.scratch hs) hscalar bd bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scratch (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc).trans (PowersKeep.of_rbx kt), ?_⟩
  change val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv, encodedValue_rep cp, encodedValue_rep (pointMul_rep _ basePoint_rep)]

end VG.Proof.Ed25519.X86_64
end

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem scalarBasePrecomputedEngine_ct (base k : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrecomputedEngine fld) (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrepare fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepare_ok h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     scalarBasePrepare_ok h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [scalarBasePrecomputedEngine]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hct : RelCT isa (fun u v =>
      (Scratch u base ∧ env u.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, u.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) < 2 ^ (16 * 16)) ∧
      (Scratch v base ∧ env v.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, v.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) < 2 ^ (16 * 16)))
      (combMultiply fld) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi) (by fld_taint_decide)
  have hm' := withRuns hct (fun u v h =>
    ⟨combMultiply_ok (fld := fld) h.1.1 h.1.2.2.2 h.1.2.1 h.1.2.2.1,
     combMultiply_ok (fld := fld) h.2.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      (pointEncode fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi)
  exact (VG.RelCT.seq hm'' he) _ _ _ _ _ _
    ⟨⟨hx.1.scratch hab.1.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩,
     ⟨hy.1.scratch hab.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2⟩⟩ ex ey

theorem scalarBase_precomputed_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub
    (scalarBase_precomputed fld) :=
  scalarBase_ct_of_engine (scalarBasePrecomputedEngine fld) scalarBasePrecomputedEngine_ok
    scalarBasePrecomputedEngine_ct

end VG.Proof.Ed25519.X86_64
