import VerifiedGarbage.Proof.X448.X86_64.Setup
import VerifiedGarbage.Proof.X448.X86_64.Output
import VerifiedGarbage.Proof.X448.X86_64.Freeze

/-!
# X448 on x86-64: the result and restored registers

Untrusted: everything here is checked by Lean. The final multiplication,
canonical reduction and encoding produce the affine coordinate. The two
callee-saved registers are then restored from the disjoint working space.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m')
    (ho : o + 128 ≤ 8192) : Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o : Nat} (hm : FieldMem base o m m') (ho : 16 ≤ o) : Saved base g m' :=
  ⟨(hm.word (Or.inl (by omega)) (by decide)).trans h.1,
    (hm.word (Or.inl ho) (by decide)).trans h.2⟩

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (.block [.mov .rbx (.mem (sc 0)), .mov .r12 (.mem (sc 8))]) s fun t =>
      t.gpr .rbx = g .rbx ∧ t.gpr .r12 = g .r12 ∧ t.mem = s.mem ∧ Keeps [.rbx, .r12] s t := by
  have hr := hs.read (d := 0) (n := 8) (by decide)
  have hr' := hs.read (d := 8) (n := 8) (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_sc,
    hs.rdi, hr, hr', RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨hsv.1, hsv.2, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem movRsi_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r12)]) s fun t =>
      t.gpr .rsi = s.gpr .r12 ∧ t.mem = s.mem ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

def finishRegs : List Reg := .rbx :: .r12 :: workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hp : s.gpr .rsi = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : Saved base g s.mem) :
    WP isa finish s fun t =>
      t.gpr .rbx = g .rbx ∧ t.gpr .r12 = g .r12 ∧ Keeps finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) := by
  refine WP.seq (WP.mono (mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs vb ((vk.1 _ (by decide)).trans ((uk.1.1 _ (by decide)).trans hp))
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : Saved base g w.mem :=
    ⟨(output_word wm (by decide) (by decide) hfar).trans svv.1,
      (output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  refine WP.mono (restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  refine ⟨tb, tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.X86_64
