import VerifiedGarbage.Proof.X448.AArch64.Fast.Env

/-!
# X448 on AArch64: the field operations of a ladder step

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot)
open VG.Proof.X448.AArch64.Weak (Index Env opMul)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops stepOps)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The slots after the step's operations (slots as in `Impl/X448/AArch64/Common.lean`). -/
def stepOpsEnv (e : Env) : Env :=
  let e := Function.update e 12 (e 8 * e 5)
  let e := Function.update e 13 (e 7 * e 6)
  let e := Function.update e 9 (e 5 * e 5)
  let e := Function.update e 10 (e 6 * e 6)
  let e := Function.update (Function.update e 14 (e 12 + e 13)) 15 (e 12 - e 13)
  let e := Function.update e 11 (e 9 - e 10)
  let e := Function.update e 15 (e 15 * e 15)
  let e := Function.update e 3 (e 14 * e 14)
  let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
  let e := Function.update e 4 (e 0 * e 15)
  let e := Function.update e 1 (e 9 * e 10)
  Function.update e 2 (e 11 * e 16)

/-- What the step's operations keep. -/
def Post (base : Addr) (s t : State) : Prop :=
  FKeep base s t ∧ BEnv t.mem base

theorem mulOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Bnd Mb t.mem base (slot o.val) →
      Same base [o] s.mem t.mem → EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a * EV s.mem base b) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.mul (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q := by
  refine WP.seq (WP.mono (fmulE hs hb o a b hob) fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts ?_)
  rw [te]; rfl

theorem addSubOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o₁ o₂ a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (h12 : o₁ ≠ o₂)
    (h1a : o₁ ≠ a) (h1b : o₁ ≠ b) (h2a : o₂ ≠ a) (h2b : o₂ ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o₁, o₂] s.mem t.mem →
      EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a + EV s.mem base b))
        o₂ (EV s.mem base a - EV s.mem base b) → WP isa (ops rest) t Q) :
    WP isa (ops (.addSub (slot o₁.val) (slot o₂.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (addSubE hs hb ha hb' h12 h1a h1b h2a h2b) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem subOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a) (hob : o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a - EV s.mem base b) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.sub (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (subE hs hb ha hb' hoa hob) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem smallOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a e : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a + Spec.X448.a24 * EV s.mem base e) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.small (slot o.val) (slot a.val) (slot e.val) :: rest)) s Q :=
  WP.seq (WP.mono (smallE hs hb ha) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem ops_append (l₁ l₂ : List Impl.X448.AArch64.Fast.Op) {s : State} {Q : State → Prop}
    (h : WP isa (ops l₁) s fun t => WP isa (ops l₂) t Q) : WP isa (ops (l₁ ++ l₂)) s Q := by
  induction l₁ generalizing s with
  | nil => exact (WP.block_nil_iff.mp h)
  | cons o os ih =>
    rw [ops, WP.seq_iff] at h
    exact WP.seq (WP.mono h fun t ht => ih ht)

/-- The four products of the step. -/
theorem ops1_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (12 : Index).val) (slot (8 : Index).val) (slot (5 : Index).val),
      .mul (slot (13 : Index).val) (slot (7 : Index).val) (slot (6 : Index).val),
      .mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [12, 13, 9, 10] s.mem t.mem ∧
      (∀ i : Index, i.val ∈ [9, 10, 12, 13] → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 12 (e 8 * e 5)
        let e := Function.update e 13 (e 7 * e 6)
        let e := Function.update e 9 (e 5 * e 5)
        Function.update e 10 (e 6 * e 6) := by
  refine mulOp hs hb 12 8 5 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 13 7 6 (by decide) fun t2 k2 b2 m2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 9 5 5 (by decide) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine mulOp hs3 b3 10 6 6 (by decide) fun t4 k4 b4 m4 s4 e4 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans k4)), b4, fun i hi j hj => ?_, fun i hi => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [s4 i (by simp [hi.2.2.2]) j hj, s3 i (by simp [hi.2.2.1]) j hj, s2 i (by simp [hi.2.1]) j hj,
      s1 i (by simp [hi.1]) j hj]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h
    · rw [show i = 9 from Fin.ext h]; exact s4.bnd (by decide) m3
    · rw [show i = 10 from Fin.ext h]; exact m4
    · rw [show i = 12 from Fin.ext h]; exact s4.bnd (by decide) (s3.bnd (by decide) (s2.bnd (by decide) m1))
    · rw [show i = 13 from Fin.ext h]; exact s4.bnd (by decide) (s3.bnd (by decide) m2)
  · rw [e4, e3, e2, e1]

/-- The sums and differences of the step, and the products of `x₃`. -/
theorem ops2_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hM : ∀ i : Index, i.val ∈ [9, 10, 12, 13] → Bnd Mb s.mem base (slot i.val)) :
    WP isa (ops [.addSub (slot (14 : Index).val) (slot (15 : Index).val) (slot (12 : Index).val)
        (slot (13 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (3 : Index).val) (slot (14 : Index).val) (slot (14 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [14, 15, 11, 3] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (3 : Index).val) ∧ Bnd Mb t.mem base (slot (15 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update (Function.update e 14 (e 12 + e 13)) 15 (e 12 - e 13)
        let e := Function.update e 11 (e 9 - e 10)
        let e := Function.update e 15 (e 15 * e 15)
        Function.update e 3 (e 14 * e 14) := by
  refine addSubOp (o₁ := 14) (o₂ := 15) (a := 12) (b := 13) hs hb (hM 12 (by decide)) (hM 13 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t5 k5 b5 s5 e5 => ?_
  have hs5 := k5.scr hs
  refine subOp (o := 11) (a := 9) (b := 10) hs5 b5 (s5.bnd (by decide) (hM 9 (by decide)))
    (s5.bnd (by decide) (hM 10 (by decide))) (by decide) (by decide) fun t6 k6 b6 s6 e6 => ?_
  have hs6 := k6.scr hs5
  refine mulOp hs6 b6 15 15 15 (by decide) fun t7 k7 b7 m7 s7 e7 => ?_
  have hs7 := k7.scr hs6
  refine mulOp hs7 b7 3 14 14 (by decide) fun t8 k8 b8 m8 s8 e8 => ?_
  refine WP.block_nil ⟨k5.trans (k6.trans (k7.trans k8)), b8, fun i hi j hj => ?_,
    m8, s8.bnd (by decide) m7, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [s8 i (by simp [hi.2.2.2]) j hj, s7 i (by simp [hi.2.1]) j hj, s6 i (by simp [hi.2.2.1]) j hj,
      s5 i (by simp [hi.1, hi.2.1]) j hj]
  · rw [e8, e7, e6, e5]

/-- `a + a24 e` and the step's last three products. -/
theorem ops3_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (h9 : Bnd Mb s.mem base (slot (9 : Index).val)) :
    WP isa (ops [.small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .mul (slot (2 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [16, 4, 1, 2] s.mem t.mem ∧
      (∀ i : Index, i.val ∈ [1, 2, 4] → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
        let e := Function.update e 4 (e 0 * e 15)
        let e := Function.update e 1 (e 9 * e 10)
        Function.update e 2 (e 11 * e 16) := by
  refine smallOp (o := 16) (a := 9) (e := 11) hs hb h9 fun t9 k9 b9 s9 e9 => ?_
  have hs9 := k9.scr hs
  refine mulOp hs9 b9 4 0 15 (by decide) fun t10 k10 b10 m10 s10 e10 => ?_
  have hs10 := k10.scr hs9
  refine mulOp hs10 b10 1 9 10 (by decide) fun t11 k11 b11 m11 s11 e11 => ?_
  have hs11 := k11.scr hs10
  refine mulOp hs11 b11 2 11 16 (by decide) fun t12 k12 b12 m12 s12 e12 => ?_
  refine WP.block_nil ⟨k9.trans (k10.trans (k11.trans k12)), b12, fun i hi j hj => ?_, fun i hi => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [s12 i (by simp [hi.2.2.2]) j hj, s11 i (by simp [hi.2.2.1]) j hj, s10 i (by simp [hi.2.1]) j hj,
      s9 i (by simp [hi.1]) j hj]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · rw [show i = 1 from Fin.ext h]; exact s12.bnd (by decide) m11
    · rw [show i = 2 from Fin.ext h]; exact m12
    · rw [show i = 4 from Fin.ext h]; exact s12.bnd (by decide) (s11.bnd (by decide) m10)
  · rw [e12, e11, e10, e9]

theorem stepOps_split : stepOps =
    ([.mul (slot (12 : Index).val) (slot (8 : Index).val) (slot (5 : Index).val),
      .mul (slot (13 : Index).val) (slot (7 : Index).val) (slot (6 : Index).val),
      .mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val)] : List Impl.X448.AArch64.Fast.Op) ++
    (([.addSub (slot (14 : Index).val) (slot (15 : Index).val) (slot (12 : Index).val)
        (slot (13 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (3 : Index).val) (slot (14 : Index).val) (slot (14 : Index).val)] : List Impl.X448.AArch64.Fast.Op) ++
    ([.small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .mul (slot (2 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val)] : List Impl.X448.AArch64.Fast.Op)) := rfl

theorem stepOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hX1 : Bnd Mb s.mem base (slot (0 : Index).val)) :
    WP isa (ops stepOps) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ (∀ i : Index, i.val ∈ [0, 1, 2, 3, 4] → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base = stepOpsEnv (EV s.mem base) := by
  rw [stepOps_split]
  refine ops_append _ _ (WP.mono (ops1_ok hs hb) fun t ⟨tk, tb, ts, tm, te⟩ => ?_)
  have ht := tk.scr hs
  refine ops_append _ _ (WP.mono (ops2_ok ht tb tm) fun u ⟨uk, ub, us, u3, u15, ue⟩ => ?_)
  have hu := uk.scr ht
  refine WP.mono (ops3_ok hu ub (us.bnd (by decide) (tm 9 (by decide)))) fun v ⟨vk, vb, vs, vm, ve⟩ => ?_
  refine ⟨tk.trans (uk.trans vk), vb, fun i hi => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h
    · rw [show i = 0 from Fin.ext h]
      exact vs.bnd (by decide) (us.bnd (by decide) (ts.bnd (by decide) hX1))
    · exact vm i (by simp [h])
    · exact vm i (by simp [h])
    · rw [show i = 3 from Fin.ext h]; exact vs.bnd (by decide) u3
    · exact vm i (by simp [h])
  · rw [ve, ue, te]; rfl

end VG.Proof.X448.AArch64.Fast
