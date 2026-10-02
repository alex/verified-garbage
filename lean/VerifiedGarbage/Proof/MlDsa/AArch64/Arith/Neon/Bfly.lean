import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q Zq)

def Coeffs (v : BitVec 128) (f : Nat → Zq) : Prop := Lanes v fun e => (f e).val

def Zetas (v : BitVec 128) (f : Nat → Zq) : Prop := Lanes v fun e => (f e).val*2^32%q

def VBflyOk (bf : List Instr) (op : Zq → Zq → Zq → Zq × Zq)
    (zt : Zq → Zq) : Prop :=
  ∀ (s : State), VConsts s → ∀ (a b z : Nat → Zq), Coeffs (s.v .v0) a → Coeffs (s.v .v1) b →
    Zetas (s.v .v18) (fun e => zt (z e)) →
    WP isa (.block bf) s fun s' => Coeffs (s'.v .v0) (fun e => (op (a e) (b e) (z e)).1) ∧
      Coeffs (s'.v .v5) (fun e => (op (a e) (b e) (z e)).2) ∧
      VChg [.v0,.v1,.v2,.v3,.v4,.v5] s s'

theorem bfly_spec : VBflyOk Impl.MlDsa.AArch64.Arith.Neon.bfly
    (fun a b z => (a+z*b,a-z*b)) id := by
  intro s hc a b z ha hb hz
  refine bfly_ok hc ha hb hz (fun e _ => (a e).isLt)
    (fun _ _ => Nat.mod_lt _ (by decide)) (rest := []) fun s' h l0 l5 =>
      WP.block_nil_iff.mpr ⟨?_, ?_, h⟩
  · exact l0.congr fun e _ => by
      change ((a e).val+mont ((b e).val*((z e).val*2^32%q))%q)%q = (a e+z e*b e).val
      rw [mont_mulR, val_add', val_mul, Nat.mul_comm (z e).val]
  · exact l5.congr fun e _ => by
      change ((a e).val+q-mont ((b e).val*((z e).val*2^32%q))%q)%q = (a e-z e*b e).val
      rw [mont_mulR, val_sub, val_mul, Nat.mul_comm (z e).val, condSub_eq]
      have := (a e).isLt
      have := Nat.mod_lt ((b e).val*(z e).val) (show 0 < q by decide)
      omega

theorem bflyInv_spec : VBflyOk Impl.MlDsa.AArch64.Arith.Neon.bflyInv
    (fun a b z => (a+b,z*(b-a))) (fun z => -z) := by
  intro s hc a b z ha hb hz
  refine bflyInv_ok hc ha hb hz (fun e _ => (a e).isLt) (fun e _ => (b e).isLt)
    (fun _ _ => Nat.mod_lt _ (by decide)) (rest := []) fun s' h l0 l5 =>
      WP.block_nil_iff.mpr ⟨?_, ?_, h.mono⟩
  · exact l0.congr fun e _ => (val_add' _ _).symm
  · exact l5.congr fun e _ => by
      change mont (((a e).val+q-(b e).val)*((-z e).val*2^32%q))%q = (z e*(b e-a e)).val
      rw [← neg_mul_sub, val_mul, val_sub, condSub_eq]
      · rw [mont_mulR, Nat.mul_mod_mod, Nat.mul_comm]
      · have := (a e).isLt; have := (b e).isLt; omega
end VG.Proof.MlDsa.AArch64.Arith.Neon
