import VerifiedGarbage.Proof.X448.X86_64.Init
import VerifiedGarbage.Proof.X448.X86_64.MulLoop
import VerifiedGarbage.Proof.X448.X86_64.Reduce

/-!
# X448 on x86-64: field multiplication

The row loop, coefficient folds and carry passes together compute
multiplication modulo the field prime, with bounded output limbs. Either input
may also be the output.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

def clob : List Reg := [.rax, .rcx, .rdx, .r10, .r11]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps clob s t
  mem : FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base) :
    Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 128 ≤ ACC

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.X86_64.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  rw [Impl.X448.X86_64.mul, WP.seq_iff]
  refine WP.mono (mulInit_ok hs) fun t ⟨tz, tc, tr, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  have ft : ∀ i < 16, limbs t.mem base a i = f i := fun i hi =>
    tm.limbs (Or.inl ha) (Nat.le_trans ha (by decide)) hi
  have gt : ∀ i < 16, limbs t.mem base b i = g i := fun i hi =>
    tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hi
  rw [WP.seq_iff]
  refine WP.mono (mulLoop_ok ts ha hb ft gt ab bb tz tc tr) fun u ⟨uf, um, uk⟩ => ?_
  have us := ts.of_keeps uk (by decide)
  have rawBound : ∀ k < 32, rows f g 16 k < 2 ^ 60 := by
    intro k _
    exact Nat.lt_of_le_of_lt (rows_bound ab bb (by decide) k) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok us uf rawBound) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  refine WP.mono (normalize_ok vs ho vf (fun i hi => reduced_bound rawBound i hi))
    fun w ⟨wf, wm, wk⟩ => ?_
  have val : fe w.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base b) % Spec.X448.P := by
    rw [show fe w.mem base o = valN (normalized (reduced (rows f g 16))) 16 from valN_congr wf,
      normalized_mod (fun i hi => reduced_bound rawBound i hi), reduced_mod, rows_val f g (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have k₁ : Keeps clob s t := tk.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)
    have k₃ : Keeps clob u v := vk.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
    have k₄ : Keeps clob v w := wk.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)
    exact k₁.trans (uk.trans (k₃.trans k₄))
  · exact (FieldMem.work tm (by omega) (by omega)).trans
      ((FieldMem.work um (by omega) (by omega)).trans
      ((FieldMem.work vm (by decide) (by decide)).trans wm))
  · intro i hi; rw [wf i hi]; exact digit_lt _ _
  · exact toFe_mul val

end VG.Proof.X448.X86_64
