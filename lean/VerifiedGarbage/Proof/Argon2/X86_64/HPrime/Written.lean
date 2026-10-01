import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Chain

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
