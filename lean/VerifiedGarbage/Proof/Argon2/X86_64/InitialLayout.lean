import VerifiedGarbage.Proof.Argon2.X86_64.InitialArgs
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.Initial

/-! # The stack inputs and scratch allocation used by H₀ -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def slots : List Nat := [72, 80, 88, 96, 104, 112, 176, 184, 200, 208, 216, 224, 264]

def wordAt (s : State) (d : Nat) : Addr :=
  s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64

def inputRegion (s : State) (pointerOffset lengthOffset : Nat) : Region :=
  ⟨wordAt s pointerOffset, (wordAt s lengthOffset).toNat⟩

/-- Hash calls and argument preparation preserve these registers and bytes.
`r12` and `r14` are the running count and the current input length. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16] s.mem t.mem

theorem Keeps.rbx {s t : State} (h : Keeps s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.rbp {s t : State} (h : Keeps s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.rsp {s t : State} (h : Keeps s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Keeps.trans {s t u : State} (h : Keeps s t) (k : Keeps t u) : Keeps s u :=
  ⟨fun r hr h1 h2 => (k.regs r hr h1 h2).trans (h.regs r hr h1 h2),
    k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.rbx, h.rsp] using k.frame)⟩

theorem Keeps.of_hash {s t : State} (h : HPrime.Keeps s t) : Keeps s t :=
  ⟨fun r hr _ _ => h.regs r hr, h.rd, h.wr, h.frame⟩

structure Space (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 16)
  readable : ∀ d ∈ slots, InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8
  output : InRegions s.wr (s.gpr .rbp) 64

theorem Space.keeps {s t : State} (h : Space s) (k : Keeps s t) : Space t := by
  constructor
  · rw [k.rbx, k.wr]; exact h.work
  · rw [k.rbx, k.rsp]; exact h.stackWork
  · rw [k.rbp, k.rbx]; exact h.frameWork
  · rw [k.rbp, k.rsp]; exact h.frameStack
  · intro d hd; rw [k.rbp, k.rd, k.wr]; exact h.readable d hd
  · rw [k.rbp, k.wr]; exact h.output

theorem Space.word_keeps {s t : State} (h : Space s) (k : Keeps s t)
    (d : Nat) (hd : d + 8 ≤ 272) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [k.rbp]
  apply k.frame.readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ hd (by omega)) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
  · exact h.frameStack

theorem Space.write {s : State} (h : Space s) (d n : Nat) (hd : d + n ≤ 16384) :
    InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) n :=
  ⟨_, h.work, Offset.contains_base _ hd (by omega)⟩

theorem Space.input_keeps {s t : State} (h : Space s) (k : Keeps s t)
    (po lo : Nat) (hp : po + 8 ≤ 272) (hl : lo + 8 ≤ 272) :
    inputRegion t po lo = inputRegion s po lo := by
  simp only [inputRegion, h.word_keeps k po hp, h.word_keeps k lo hl]

theorem Keeps.bytes {s t : State} (h : Keeps s t) (r : Region)
    (work : r.Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stack : r.Disjoint (below (s.gpr .rsp) 16)) (bound : r.len ≤ 2 ^ 64) :
    bytesAt t.mem r.base r.len = bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work.sub_right (Region.sub_prefix (by decide))
  · exact stack

end VG.Proof.Argon2.X86_64.Initial
