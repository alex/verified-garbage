import VerifiedGarbage.Impl.Ed25519.X86_64.BaseTable
import VerifiedGarbage.Proof.Ed25519.ScalarMul

/-!
# The cached base-point powers match the specification

Untrusted. `checkList` walks the table once, doubling a literal point with
the specification's formula as it goes, so the kernel evaluates 256
doublings and compares 256 entries. `d` is replaced by its value first, so
that the kernel computes its inversion once.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519

/-- `[Y - X, Y + X, 2dT, 2Z]`: a point cached for addition. -/
def cache (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * d, q.Z * 2⟩

private def dLit : Spec.X25519.Fe :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

private theorem d_eq : d = dLit := by decide +kernel

private def addLit (p q : Point) : Point :=
  let a := (p.Y - p.X) * (q.Y - q.X)
  let b := (p.Y + p.X) * (q.Y + q.X)
  let c := p.T * 2 * dLit * q.T
  let dd := p.Z * 2 * q.Z
  let e := b - a
  let f := dd - c
  let g := dd + c
  let h := b + a
  ⟨e * f, g * h, f * g, e * h⟩

private def cacheLit (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * dLit, q.Z * 2⟩

private theorem addLit_eq (p q : Point) : addLit p q = pointAdd p q := by
  simp only [addLit, pointAdd, d_eq]

private theorem cacheLit_eq (q : Point) : cacheLit q = cache q := by
  simp only [cacheLit, cache, d_eq]

/-- Whether the entries are the cached powers of `p`, from `p` on. -/
private def checkList (p : Point) : List Point → Bool
  | [] => true
  | c :: cs => cacheLit p == c && checkList (addLit p p) cs

private theorem checkList_ok (p : Point) (cs : List Point) (h : checkList p cs = true)
    (k : Nat) (hk : k < cs.length) : cs.getD k identity = cache (powerPoint p k) := by
  induction cs generalizing p k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons c cs ih =>
    simp only [checkList, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => rw [List.getD_cons_zero, ← h.1, cacheLit_eq]; rfl
    | succ k =>
      rw [List.getD_cons_succ, ih _ h.2 k (by simp only [List.length_cons] at hk; omega),
        addLit_eq, Nat.add_comm, powerPoint_add]
      rfl

private theorem table_length : baseCachedTable.length = 256 := by decide +kernel

private theorem table_check : checkList basePoint baseCachedTable = true := by decide +kernel

theorem baseCached_ok (i : Nat) (hi : i < 256) :
    baseCached i = cache (powerPoint basePoint i) :=
  checkList_ok _ _ table_check i (table_length ▸ hi)

end VG.Proof.Ed25519.X86_64
