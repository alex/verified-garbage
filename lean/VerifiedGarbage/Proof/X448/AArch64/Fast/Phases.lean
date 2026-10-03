import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
import VerifiedGarbage.Proof.X448.AArch64.Fast.NeonEnv

/-!
# X448 on AArch64: the ladder step's field operations

Untrusted: everything here is checked by Lean. Each half of the step runs
two products in AdvSIMD interleaved with scalar operations; the two streams
are independent (checked by evaluating their footprints), so they run as the
scalar operations and then the vector products.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf weave stepA stepB)
open VG.Impl.Curve448.AArch64.Neon (mul2)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem Same.append {base : Addr} {l₁ l₂ : List Index} {m₁ m₂ m₃ : Mem} (h : Same base l₁ m₁ m₂)
    (h' : Same base l₂ m₂ m₃) : Same base (l₁ ++ l₂) m₁ m₃ := fun i hi j hj => by
  rw [h' i (fun e => hi (List.mem_append_right _ e)) j hj, h i (fun e => hi (List.mem_append_left _ e)) j hj]

/-- The scalar half of `stepA`. -/
theorem opsA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [9, 10, 1, 11, 16] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (1 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 9 (e 5 * e 5)
        let e := Function.update e 10 (e 6 * e 6)
        let e := Function.update e 1 (e 9 * e 10)
        let e := Function.update e 11 (e 9 - e 10)
        Function.update e 16 (e 9 + Spec.X448.a24 * e 11) := by
  refine mulOp hs hb 9 5 5 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 10 6 6 (by decide) fun t2 k2 b2 m2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  have m9 : Bnd Mb t2.mem base (slot (9 : Index).val) := s2.bnd (by decide) m1
  refine mulOp hs2 b2 1 9 10 (by decide) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine subOp (o := 11) (a := 9) (b := 10) hs3 b3 (s3.bnd (by decide) m9) (s3.bnd (by decide) m2)
    (by decide) (by decide) fun t4 k4 b4 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine smallOp (o := 16) (a := 9) (e := 11) hs4 b4 (s4.bnd (by decide) (s3.bnd (by decide) m9))
    fun t5 k5 b5 s5 e5 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans k5))), b5,
    (((s1.append s2).append s3).append s4).append s5, s5.bnd (by decide) (s4.bnd (by decide) m3), ?_⟩
  rw [e5, e4, e3, e2, e1]

theorem stepA_eq : stepA = weave (codeOf [.mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val)])
    (mul2 (slot (12 : Index).val) (slot (8 : Index).val) (slot (5 : Index).val) (slot (13 : Index).val)
      (slot (7 : Index).val) (slot (6 : Index).val)) := rfl

theorem stepA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block stepA) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([9, 10, 1, 11, 16] ++ [12, 13]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (1 : Index).val) ∧ Bnd Mb t.mem base (slot (12 : Index).val) ∧
      Bnd Mb t.mem base (slot (13 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 9 (e 5 * e 5)
        let e := Function.update e 10 (e 6 * e 6)
        let e := Function.update e 1 (e 9 * e 10)
        let e := Function.update e 11 (e 9 - e 10)
        let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
        Function.update (Function.update e 12 (e 8 * e 5)) 13 (e 7 * e 6) := by
  rw [stepA_eq]
  refine WP.weave (by decide +kernel) (WP.mono (block_codeOf (opsA_ok hs hb)) fun t ⟨tk, tb, ts, t1, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 12 8 5 13 7 6 (by decide)) fun u ⟨uk, ub, u12, u13, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, us.bnd (by decide) t1, u12, u13, ?_⟩
  rw [ue, te]

/-- The scalar half of `stepB`. -/
theorem opsB_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [15, 4] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (4 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 15 (e 15 * e 15)
        Function.update e 4 (e 0 * e 15) := by
  refine mulOp hs hb 15 15 15 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  refine mulOp (k1.scr hs) b1 4 0 15 (by decide) fun t2 k2 b2 m2 s2 e2 => ?_
  refine WP.block_nil ⟨k1.trans k2, b2, s1.append s2, m2, ?_⟩
  rw [e2, e1]

theorem stepB_eq : stepB = weave (codeOf [.mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val)])
    (mul2 (slot (2 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val) (slot (3 : Index).val)
      (slot (14 : Index).val) (slot (14 : Index).val)) := rfl

theorem stepB_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block stepB) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([15, 4] ++ [2, 3]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (2 : Index).val) ∧ Bnd Mb t.mem base (slot (3 : Index).val) ∧
      Bnd Mb t.mem base (slot (4 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 15 (e 15 * e 15)
        let e := Function.update e 4 (e 0 * e 15)
        Function.update (Function.update e 2 (e 11 * e 16)) 3 (e 14 * e 14) := by
  rw [stepB_eq]
  refine WP.weave (by decide +kernel) (WP.mono (block_codeOf (opsB_ok hs hb)) fun t ⟨tk, tb, ts, t4, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 2 11 16 3 14 14 (by decide)) fun u ⟨uk, ub, u2, u3, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, u2, u3, us.bnd (by decide) t4, ?_⟩
  rw [ue, te]

/-- The step's field operations, after `A, B, C, D`. -/
def stepOpsCode : Prog isa :=
  .seq (.block stepA) <| .seq (ops [.addSub (slot (14 : Index).val) (slot (15 : Index).val) (slot (12 : Index).val)
    (slot (13 : Index).val)]) (.block stepB)

theorem stepOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hX1 : Bnd Mb s.mem base (slot (0 : Index).val)) :
    WP isa stepOpsCode s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ (∀ i : Index, i.val ∈ [0, 1, 2, 3, 4] → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base = stepOpsEnv (EV s.mem base) := by
  refine WP.seq (WP.mono (stepA_ok hs hb) fun t ⟨tk, tb, ts, t1, t12, t13, te⟩ => ?_)
  have ht := tk.scr hs
  refine WP.seq (addSubOp (o₁ := 14) (o₂ := 15) (a := 12) (b := 13) ht tb t12 t13
    (by decide) (by decide) (by decide) (by decide) (by decide) fun u uk ub us ue => WP.block_nil ?_)
  refine WP.mono (stepB_ok (uk.scr ht) ub) fun v ⟨vk, vb, vs, v2, v3, v4, ve⟩ =>
    ⟨tk.trans (uk.trans vk), vb, fun i hi => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h
    · rw [show i = 0 from Fin.ext h]
      exact vs.bnd (by decide) (us.bnd (by decide) (ts.bnd (by decide) hX1))
    · rw [show i = 1 from Fin.ext h]; exact vs.bnd (by decide) (us.bnd (by decide) t1)
    · rw [show i = 2 from Fin.ext h]; exact v2
    · rw [show i = 3 from Fin.ext h]; exact v3
    · rw [show i = 4 from Fin.ext h]; exact v4
  · rw [ve, ue, te]; rfl

end VG.Proof.X448.AArch64.Fast
