import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Chain

/-! Merged from `Proof.Argon2.X86_64.HPrime.Written`. -/
section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .r14) xs.length = xs

theorem Written.rbx {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide) (by decide) (by decide)

theorem Written.rsp {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, ?_, rfl⟩
  · exact (h.regs .r14 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .r14 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.rbx, k.rsp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 _ => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 h15 => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩)
    (stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.rbx, ← first.rsp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h1 h2 => (last.regs r hr h1 h2).trans (first.regs r hr h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega) tf)
  · have before : bytesAt t.mem (s.gpr .r14) xs.length = bytesAt u.mem (s.gpr .r14) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (by omega) (by omega)
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, n⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .r14, k⟩ ⟨s.gpr .r14, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.rbx]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega)
  · rw [written.rbx]; exact h.sep.sub_right suffix
  · rw [written.rbx, written.rsp]; exact h.stackWork
  · rw [written.rsp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega, h.work, fun i hi => h.out i (by omega),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega)
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .rbx + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha _ _ => WP.block_nil ?_)
  have base := ha.other .rbx (by decide)
  have dst := ha.other .r14 (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .rbx + 768, n⟩ : Region).Disjoint ⟨a.gpr .r14, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht space.bound
  refine ⟨?_, fun r hr h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.other .rsp (by decide)] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.X86_64.HPrime
