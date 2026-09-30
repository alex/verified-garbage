import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-! # Key-expansion loops and their byte-array representation -/

namespace VG.Proof.Rc2

open VG

abbrev KeyBytes := Vector Byte 128

def fillStep (t j : Nat) (l : KeyBytes) : KeyBytes :=
  let i := t + j
  l.set! i (Spec.Rc2.pi (l.getD (i - 1) 0 + l.getD (i - t) 0))

def fill (key : List Byte) (n : Nat) : KeyBytes :=
  (List.range n).foldl (fun l j => fillStep key.length j l)
    (Vector.ofFn fun i => key.getD i 0)

def descendStep (t8 j : Nat) (l : KeyBytes) : KeyBytes :=
  let i := 127 - t8 - j
  l.set! i (Spec.Rc2.pi (l.getD (i + 1) 0 ^^^ l.getD (i + t8) 0))

def reduce (l : KeyBytes) (bits : Nat) : KeyBytes :=
  let t8 := (bits + 7) / 8
  let tm := BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * t8))
  l.set! (128 - t8) (Spec.Rc2.pi (l.getD (128 - t8) 0 &&& tm))

def descend (l : KeyBytes) (t8 n : Nat) : KeyBytes :=
  (List.range n).foldl (fun l j => descendStep t8 j l) l

theorem fill_succ (key : List Byte) (n : Nat) :
    fill key (n + 1) = fillStep key.length n (fill key n) := by
  simp only [fill, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem descend_succ (l : KeyBytes) (t8 n : Nat) :
    descend l t8 (n + 1) = descendStep t8 n (descend l t8 n) := by
  simp only [descend, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem expandBytes_eq (key : List Byte) (bits : Nat) :
    Spec.Rc2.expandBytes key bits =
      descend (reduce (fill key (128 - key.length)) bits) ((bits + 7) / 8)
        (128 - (bits + 7) / 8) := by
  simp [Spec.Rc2.expandBytes, fill, fillStep, reduce, descend, descendStep,
    List.forIn_pure_yield_eq_foldl]

/-- Only the prefix below `n` has been initialized during copying and
forward expansion; the remaining bytes are unconstrained. -/
def BytesPrefix (m : Mem) (p : Addr) (l : KeyBytes) (n : Nat) : Prop :=
  ∀ i < n, m (p + BitVec.ofNat 64 i) = l.getD i 0

theorem getD_set (l : KeyBytes) (i j : Nat) (hj : j < 128) (b : Byte) :
    (l.set! i b).getD j 0 = if i = j then b else l.getD j 0 := by
  rw [getD_eq_getElem _ j hj, getD_eq_getElem _ j hj, Vector.getElem_set! hj]

theorem BytesPrefix.write {m : Mem} {p : Addr} {l : KeyBytes} {n i : Nat}
    (h : BytesPrefix m p l n) (hn : n ≤ 128) (hi : i < n) (b : Byte) :
    BytesPrefix (m.writeW (p + BitVec.ofNat 64 i) b) p (l.set! i b) n := by
  intro j hj
  rw [WriteBytes.writeW8_apply, getD_set l i j (by omega)]
  by_cases he : i = j
  · subst j; simp
  · have hne := Offset.add_ofNat_ne p (show j < 2 ^ 64 by omega) (show i < 2 ^ 64 by omega) (Ne.symm he)
    rw [ite_eq_right he, ite_eq_right hne, h j hj]

theorem BytesPrefix.extend {m : Mem} {p : Addr} {l : KeyBytes} {n : Nat}
    (h : BytesPrefix m p l n) (hn : n < 128) (b : Byte) :
    BytesPrefix (m.writeW (p + BitVec.ofNat 64 n) b) p (l.set! n b) (n + 1) := by
  intro j hj
  rw [WriteBytes.writeW8_apply, getD_set l n j (by omega)]
  by_cases he : n = j
  · subst j; simp
  · have hne := Offset.add_ofNat_ne p (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega) (Ne.symm he)
    rw [ite_eq_right he, ite_eq_right hne, h j (by omega)]

theorem scheduleAt_expanded {m : Mem} {p : Addr} {key : List Byte} {bits : Nat}
    (h : BytesPrefix m p (Spec.Rc2.expandBytes key bits) 128) :
    Spec.Rc2.scheduleAt m p = Spec.Rc2.expandKey key bits := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.scheduleAt, Spec.Rc2.expandKey, Vector.getElem_ofFn]
  rw [h (2 * i) (by omega), h (2 * i + 1) (by omega)]

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Rc2.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rc2.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem initial_set (key : List Byte) (i : Nat) :
    (fill key 0).set! i (key.getD i 0) = fill key 0 := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_set! hj]
  by_cases he : i = j
  · subst j; simp [fill]
  · rw [ite_eq_right he]

end VG.Proof.Rc2
