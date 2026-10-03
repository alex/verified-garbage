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
open VG.Impl.X448.AArch64.Fast (ops)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The slots after the step's operations (slots as in `Impl/X448/AArch64/Common.lean`), in the
order `Impl/X448/AArch64/Fast.lean` computes them. -/
def stepOpsEnv (e : Env) : Env :=
  let e := Function.update e 9 (e 5 * e 5)
  let e := Function.update e 10 (e 6 * e 6)
  let e := Function.update e 1 (e 9 * e 10)
  let e := Function.update e 11 (e 9 - e 10)
  let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
  let e := Function.update (Function.update e 12 (e 8 * e 5)) 13 (e 7 * e 6)
  let e := Function.update (Function.update e 14 (e 12 + e 13)) 15 (e 12 - e 13)
  let e := Function.update e 15 (e 15 * e 15)
  let e := Function.update e 4 (e 0 * e 15)
  Function.update (Function.update e 2 (e 11 * e 16)) 3 (e 14 * e 14)

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

end VG.Proof.X448.AArch64.Fast
