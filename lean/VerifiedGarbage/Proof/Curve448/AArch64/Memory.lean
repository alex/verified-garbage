import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Proof.X448.Wide.Representation
import VerifiedGarbage.Impl.Curve448.AArch64
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Wide.valN (limbs m base o) 8
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := VG.Proof.X448.toFe (fe m base o)
def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := Within weakBound (limbs m base o)

theorem field_fe {base : Addr} {o : Nat} {m m' : Mem}
    (h : FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ Impl.X448.AArch64.ACC) :
    fe m' base d = fe m base d :=
  VG.Proof.X448.Wide.valN_congr (fun i hi => h.limbs hd hw (by omega : i < 16))

theorem outside_fe {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hw : d + 128 ≤ 8192) :
    fe m' base d = fe m base d :=
  VG.Proof.X448.Wide.valN_congr (fun i hi => h.limbs hd hw (by omega : i < 16))
end VG.Proof.Curve448.AArch64
