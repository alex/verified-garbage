import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize

/-! # H′: the memory changed by hashing a workspace buffer -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

/-- Join the hash's individual writable buffers into its first 832 bytes. -/
theorem workspace_frame {m m' : Mem} (p sp : Addr) (rs : List (Nat × Nat)) (stack : Nat)
    (bounds : ∀ r ∈ rs, r.1 + r.2 ≤ 832) (depth : stack ≤ 16)
    (h : Frame (rs.map (fun r => ⟨p + BitVec.ofNat 64 r.1, r.2⟩) ++ [below sp stack]) m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply h.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base p (bounds q hq)⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub depth (by decide)⟩

theorem init_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, below sp 8] m m') : Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192)] 8 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero] using h

theorem update_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl,
    show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using h

/-- The caller's registers and permissions, and its saved registers above
832, survive every hash operation. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16] s.mem t.mem

theorem Keeps.rbx {s t : State} (h : Keeps s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide)

theorem Keeps.rsp {s t : State} (h : Keeps s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide)

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u where
  regs r hr := (h'.regs r hr).trans (h.regs r hr)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  frame := h.frame.trans (by simpa only [h.rbx, h.rsp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
    (work : r.Disjoint ⟨s.gpr .rbx, 832⟩) (stack : r.Disjoint (below (s.gpr .rsp) 16)) :
    Spec.Blake2.bytesAt t.mem r.base r.len = Spec.Blake2.bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work
  · exact stack

theorem Keeps.prefix {s t : State} (h : Keeps s t)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .rbx + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .rbx + 832) 4 :=
  h.bytes ⟨s.gpr .rbx + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.X86_64.HPrime
