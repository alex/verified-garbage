import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelArgs

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def currentColumn (p : Params) (slice index : Nat) : Nat := slice * p.segmentLen + index

def previousColumn (p : Params) (slice index : Nat) : Nat :=
  (currentColumn p slice index + p.laneLen - 1) % p.laneLen

def current (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (currentColumn p slice index)

def previous (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (matrix s) p lane (previousColumn p slice index)

def referenced (s : State) (p : Params) (pass lane slice index : Nat) : Addr :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  FillPointers.cell (matrix s) p ref.1 ref.2

structure Prepared (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  ready : FillCompress.Ready t
  currentPtr : t.gpr .r10 = current s p lane slice index
  previousPtr : t.gpr .rdi = previous s p lane slice index
  referencePtr : t.gpr .rsi = referenced s p pass lane slice index
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem prepare_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.prepare s (Prepared s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.prepare
  refine WP.seq ((mapping_ok s p pass lane slice index h).mono ?_)
  intro a mapped
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  refine ((pointers_ok a p pass lane slice index ref.1 ref.2
    (h.layout.of_keeps mapped.keeps) h.bounds (h.position.of_keeps mapped.keeps)
    mapped.selected mapped.column).mono ?_)
  intro b pointers
  have keeps := mapped.keeps.trans pointers.keeps
  have matrixA : matrix a = matrix s := by
    unfold matrix; rw [mapped.keeps.mem, mapped.keeps.regs .rbp (by decide)]
  have matrixB : matrix b = matrix a := by
    unfold matrix; rw [pointers.keeps.mem, pointers.keeps.regs .rbp (by decide)]
  have cur : b.gpr .r10 = current s p lane slice index := by
    rw [pointers.current, matrixA]; rfl
  have prev : b.gpr .rdi = previous s p lane slice index := by
    rw [pointers.previous, matrixA]; rfl
  have other : b.gpr .rsi = referenced s p pass lane slice index := by
    rw [pointers.reference, matrixA]; rfl
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have previousBound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  obtain ⟨refLane, refColumn⟩ := Proof.Argon2.reference_bounds p h.bounds.lanesPositive
    h.bounds.memoryMinimum pass lane slice index (s.gpr .rdi) h.bounds.laneBound
  have compressReady : FillCompress.Ready b := by
    apply compress_ready p b (h.layout.of_keeps keeps) h.bounds.lanesPositive
      lane (previousColumn p slice index) ref.1 ref.2 lane (currentColumn p slice index)
      h.bounds.laneBound previousBound refLane refColumn h.bounds.laneBound columnBound
    · rw [pointers.previous, matrixB]; rfl
    · rw [pointers.reference, matrixB]
    · rw [pointers.current, matrixB]; rfl
  exact ⟨compressReady, cur, prev, other, keeps⟩

end VG.Proof.Argon2.X86_64.FillKernel
