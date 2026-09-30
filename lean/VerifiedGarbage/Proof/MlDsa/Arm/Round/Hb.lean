import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA on 32-bit ARM: the values of `Decompose`

Untrusted: everything here is checked by Lean. What `hbRaw`, `csubM` and
`hb` leave in their register, as functions on words (`bhbRaw`, `bcsubM`,
`bhb`), and their values: `f` (`bhbRaw_toNat`, from `hbF_eq`) and
`f mod m`, the `r₁` of `Decompose` (`bhb_toNat`), for both values of `γ₂`.
-/

namespace VG.Proof.MlDsa.Arm.Round

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q n Zq gamma2s)

/-- `γ₂` is one of the two values. -/
def G2 (g : Nat) : Prop := g = g32 ∨ g = g88

theorem G2.mem {g : Nat} (h : G2 g) : g ∈ gamma2s := by
  rcases h with rfl | rfl <;> decide

/-- What `csubM g r t` leaves in `r`. -/
def bcsubM (g : Nat) (x : BitVec 32) : BitVec 32 :=
  if g = 261888 then x - BitVec.ofNat 32 (dMod g) + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 4
  else x - BitVec.ofNat 32 (dMod g) + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 5 +
    (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 3 + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 2

/-- What `hbRaw g x t` leaves in `x`. -/
def bhbRaw (g : Nat) (a : BitVec 32) : BitVec 32 :=
  ((a + 127) >>> 7 * (BitVec.ofNat 16 (dMul g)).setWidth 32 + BitVec.ofNat 32 (dAdd g)) >>> dShift g

/-- What `hb g x t` leaves in `x`. -/
def bhb (g : Nat) (a : BitVec 32) : BitVec 32 := bcsubM g (bhbRaw g a)

theorem hbM_dMod {g : Nat} (h : G2 g) : hbM g = dMod g := by rcases h with rfl | rfl <;> rfl

theorem bhbRaw_32 {a : BitVec 32} (ha : a.toNat < q) : (bhbRaw g32 a).toNat = hbF g32 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g32)).setWidth 32 = (1025 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g32) = (2097152 : BitVec 32) := by decide
  have e3 : dShift g32 = 22 := rfl
  have e4 : hbMul g32 = 1025 := rfl
  have e5 : hbAdd g32 = 2 ^ 21 := rfl
  have e6 : hbShift g32 = 22 := rfl
  unfold bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_88 {a : BitVec 32} (ha : a.toNat < q) : (bhbRaw g88 a).toNat = hbF g88 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g88)).setWidth 32 = (11275 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g88) = (8388608 : BitVec 32) := by decide
  have e3 : dShift g88 = 24 := rfl
  have e4 : hbMul g88 = 11275 := rfl
  have e5 : hbAdd g88 = 2 ^ 23 := rfl
  have e6 : hbShift g88 = 24 := rfl
  unfold bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_toNat {g : Nat} (hg : G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (bhbRaw g a).toNat = hbF g a.toNat := by
  rcases hg with rfl | rfl
  exacts [bhbRaw_32 ha, bhbRaw_88 ha]

theorem bcsubM_toNat {g : Nat} (hg : G2 g) {x : BitVec 32} (hx : x.toNat ≤ dMod g) :
    (bcsubM g x).toNat = x.toNat % dMod g := by
  unfold bcsubM
  rcases hg with rfl | rfl
  · rw [ite_eq_left (show g32 = 261888 from rfl), show dMod g32 = 16 from rfl] at *
    by_cases h : x.toNat < 16
    · rw [Nat.mod_eq_of_lt h]; bv_omega
    · bv_omega
  · rw [ite_eq_right (show ¬g88 = 261888 by decide), show dMod g88 = 44 from rfl] at *
    by_cases h : x.toNat < 44
    · rw [Nat.mod_eq_of_lt h]; bv_omega
    · bv_omega

/-- `r₁` of `Decompose(a)`. -/
theorem bhb_toNat {g : Nat} (hg : G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (bhb g a).toNat = hbF g a.toNat % hbM g := by
  unfold bhb
  rw [bcsubM_toNat hg (by rw [bhbRaw_toNat hg ha, ← hbM_dMod hg]; exact hbF_le hg.mem ha), bhbRaw_toNat hg ha,
    hbM_dMod hg]

theorem bhb_highBits {g : Nat} (hg : G2 g) (r : Zq) :
    (bhb g (BitVec.ofNat 32 r.val)).toNat = (VG.Spec.MlDsa.highBits g r).toNat := by
  have : r.val < 8380417 := r.isLt
  have e : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega
  rw [bhb_toNat hg (by rw [e]; exact r.isLt), e, highBits_eq hg.mem, Int.toNat_natCast]

end VG.Proof.MlDsa.Arm.Round
