import VerifiedGarbage.Proof.X448.X86_64.Initial
import VerifiedGarbage.Proof.X448.X86_64.DecodeAll

/-!
# X448 on x86-64: reading the arguments

Untrusted: everything here is checked by Lean. Setup saves the two
callee-saved registers, decodes the coordinate, and initializes the ladder.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  word m base 0 = g .rbx ∧ word m base 8 = g .r12

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h16 : 16 ≤ o) : Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega)) (by decide)).trans h.1,
    (ho.word (Or.inl h16) (by decide)).trans h.2⟩

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by decide)).trans h.1,
    (ho.word (Or.inl hx) (Or.inl hy) (by decide)).trans h.2⟩

def setupHead : List Instr :=
  [.store (at_ .rcx 0) .rbx, .store (at_ .rcx 8) .r12,
    .mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx), .mov .r10 (.reg .rdx)]

theorem setupHead_ok {s : State} {base : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block setupHead) s fun t =>
      Scr t base ∧ t.gpr .r12 = s.gpr .rdi ∧ t.gpr .r10 = s.gpr .rdx ∧
      Saved base s.gpr t.mem ∧ Outside base 0 16 s.mem t.mem ∧ Keeps [.r12, .rdi, .r10] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun _ hd => ⟨_, hw, contains_sc hd⟩
  have ea (t : State) (b : Reg) (d : Nat) : t.ea (at_ b d) = off (t.gpr b) d := rfl
  apply WP.of_runBlock
  simp only [setupHead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea, hc, w 0 (by decide), w 8 (by decide), RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, hw, hn⟩, trivial, trivial, ?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · change Saved base s.gpr ((s.mem.writeW (off base 0) (s.gpr .rbx)).writeW (off base 8) (s.gpr .r12))
    constructor
    · rw [word_write_aligned _ base (by decide) (by decide) (by decide) (by decide),
        ite_eq_right (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · exact Mem.readW_writeW_self64 _ _ _
  · exact ((writeW_outside s.mem base _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ base _ (d := 8) (by decide)).mono (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

def setupRegs : List Reg := [.rax, .rdx, .rdi, .r8, .r9, .r10, .r12]

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .rdx = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ t.gpr .r12 = s.gpr .rdi ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  change WP isa (.block (setupHead ++ ((List.range 8).flatMap decodePair ++ initSlots))) s _
  rw [WP.block_append_iff]
  refine WP.mono (setupHead_ok hc hw hn) fun t ⟨ts, tp, tr, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts (tr.trans hp)
    (by intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_bound _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_bound _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t.mem p 8)
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tp),
    (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm.mono (by decide) (by decide)).trans ?_,
    (tv.outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.X86_64
