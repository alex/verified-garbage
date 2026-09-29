import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM on x86-64: the Barrett reduction `reduce`

Untrusted: everything here is checked by Lean. `reduce` leaves `rax mod q`
in `r10`, for any `rax < 2³²` (`reduce_ok`), which is `barrett64` of
`Arith.lean` followed by `csubQ`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem (q)

theorem sx1290167 : BitVec.signExtend 64 (1290167 : BitVec 32) = 1290167 := by decide

/-- What `reduce` leaves in `r10`, of `x`. -/
def redV (x : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (csub32 (BitVec.setWidth 32 (x - BitVec.ofNat 64
    ((BitVec.ofNat 64 (x.toNat * (1290167 : BitVec 64).toNat) >>> 32).toNat * (3329 : BitVec 64).toNat))))

theorem redV_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 32) : (redV x).toNat = x.toNat % q := by
  have e1 : (BitVec.ofNat 64 (x.toNat * (1290167 : BitVec 64).toNat)).toNat = x.toNat * 1290167 := by
    rw [BitVec.toNat_ofNat, show (1290167 : BitVec 64).toNat = 1290167 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hb := barrett64_bounds hx
  have e2 : (BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * (1290167 : BitVec 64).toNat) >>> 32).toNat *
      (3329 : BitVec 64).toNat)).toNat = barrett64Quot x.toNat * q := by
    rw [shr_toNat, e1, show (3329 : BitVec 64).toNat = 3329 from rfl, BitVec.toNat_ofNat, q_eq,
      Nat.mod_eq_of_lt (by unfold barrett64Quot at hb; rw [q_eq] at hb; omega)]
    rfl
  have e3 : (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * (1290167 : BitVec 64).toNat) >>> 32).toNat *
      (3329 : BitVec 64).toNat)).toNat = barrett64 x.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e2]; exact hb.2), e2]; rfl
  have hl : barrett64 x.toNat < 2 * 3329 := barrett64_lt hx
  have e4 := toNat_setWidth32_64 (show (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat *
    (1290167 : BitVec 64).toNat) >>> 32).toNat * (3329 : BitVec 64).toNat)).toNat < 2 ^ 32 by rw [e3]; omega)
  rw [e3] at e4
  rw [redV, toNat_setWidth64, csub32_toNat (by rw [e4]; exact hl), e4, reduce64 hx]

theorem redV_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) : (redV x).toNat < q := by
  rw [redV_toNat hx]; exact Nat.mod_lt _ (by decide)

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' => (s'.gpr .r10 = redV (s.gpr .rax) ∧ s'.mem = s.mem) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold reduce csubQ
  xrun [List.cons_append, List.nil_append, csub32, redV, sx1290167]

end VG.Proof.MlKem.X86_64
