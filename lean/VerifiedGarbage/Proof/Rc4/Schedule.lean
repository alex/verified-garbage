import VerifiedGarbage.Proof.Rc4.Table

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- A proof-oriented view of the specification's sequential scheduling loop. -/
def scheduleRound (key : List Byte) (st : Table × Byte) (i : Nat) : Table × Byte :=
  let j := st.2 + st.1.getD i 0 + key.getD (i % key.length) 0
  (swap st.1 (BitVec.ofNat 8 i) j, j)

def schedulePrefix (key : List Byte) (r : Nat) : Table × Byte :=
  (List.range r).foldl (scheduleRound key)
    (Vector.ofFn (fun i => BitVec.ofNat 8 i.val), 0)

theorem schedule_zero (key : List Byte) :
    schedulePrefix key 0 = (Vector.ofFn (fun i => BitVec.ofNat 8 i.val), 0) := rfl

theorem schedule_succ (key : List Byte) (r : Nat) :
    schedulePrefix key (r + 1) = scheduleRound key (schedulePrefix key r) r := by
  unfold schedulePrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem keySchedule_eq (key : List Byte) : keySchedule key = (schedulePrefix key 256).1 := by
  unfold keySchedule schedulePrefix scheduleRound
  simp only [List.forIn_pure_yield_eq_foldl]
  rfl

end VG.Proof.Rc4
