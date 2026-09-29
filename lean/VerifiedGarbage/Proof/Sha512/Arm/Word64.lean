import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Impl.Sha512.Arm

/-!
# 64-bit words as pairs of 32-bit halves, on ARMv7

Untrusted: everything here is checked by Lean. The lemmas of
`Proof/Sha512/Word64.lean` about the halves (`lo`, `hi`) of 64-bit words,
stated for the ARMv7 implementation's `lo` and `hi` (the same functions),
and the terms of `Σ`/`σ` as the implementation lists them (`Op`).
-/

namespace VG.Proof.Sha512.Arm

open VG.Impl.Sha512.Arm (lo hi Op)

/-! ## Halves -/

theorem lo_toNat (x : BitVec 64) : (lo x).toNat = x.toNat % 2 ^ 32 := Word64.lo_toNat x

theorem hi_toNat (x : BitVec 64) : (hi x).toNat = x.toNat / 2 ^ 32 := Word64.hi_toNat x

@[simp] theorem lo_zero : lo 0#64 = 0#32 := rfl

@[simp] theorem hi_zero : hi 0#64 = 0#32 := rfl

theorem eq_of_lo_hi {x y : BitVec 64} (h1 : lo x = lo y) (h2 : hi x = hi y) : x = y :=
  Word64.eq_of_lo_hi h1 h2

theorem hi_append_lo (x : BitVec 64) : hi x ++ lo x = x := Word64.hi_append_lo x

theorem lo_append (a b : BitVec 32) : lo (a ++ b) = b := Word64.lo_append a b

theorem hi_append (a b : BitVec 32) : hi (a ++ b) = a := Word64.hi_append a b

theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := Word64.lo_add x y

theorem hi_add (x y : BitVec 64) :
    hi (x + y) = hi x + hi y + (if 2 ^ 32 ≤ (lo x).toNat + (lo y).toNat then 1 else 0) :=
  Word64.hi_add x y

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := Word64.lo_xor x y

theorem hi_xor (x y : BitVec 64) : hi (x ^^^ y) = hi x ^^^ hi y := Word64.hi_xor x y

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := Word64.lo_and x y

theorem hi_and (x y : BitVec 64) : hi (x &&& y) = hi x &&& hi y := Word64.hi_and x y

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := Word64.lo_or x y

theorem hi_or (x y : BitVec 64) : hi (x ||| y) = hi x ||| hi y := Word64.hi_or x y

theorem lo_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x.rotateRight n) = lo x >>> n ^^^ hi x <<< (32 - n) := Word64.lo_rotr x h0 h

theorem hi_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    hi (x.rotateRight n) = hi x >>> n ^^^ lo x <<< (32 - n) := Word64.hi_rotr x h0 h

theorem lo_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    lo (x.rotateRight n) = hi x >>> (n - 32) ^^^ lo x <<< (64 - n) := Word64.lo_rotr' x h0 h

theorem hi_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    hi (x.rotateRight n) = lo x >>> (n - 32) ^^^ hi x <<< (64 - n) := Word64.hi_rotr' x h0 h

theorem lo_shr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x >>> n) = lo x >>> n ^^^ hi x <<< (32 - n) := Word64.lo_shr x h0 h

theorem hi_shr (n : Nat) (x : BitVec 64) : hi (x >>> n) = hi x >>> n := Word64.hi_shr n x

/-! ## The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` -/

/-- A term's value. -/
def _root_.VG.Impl.Sha512.Arm.Op.eval (x : BitVec 64) : Op → BitVec 64
  | .rotr n => x.rotateRight n
  | .shr n => x >>> n

/-- The shift amounts that the code can encode. -/
def _root_.VG.Impl.Sha512.Arm.Op.valid : Op → Bool
  | .rotr n => 0 < n && n < 64 && n != 32
  | .shr n => 0 < n && n < 32

/-- The exclusive or of the terms. -/
def evalOps (x : BitVec 64) (ops : List Op) : BitVec 64 := ops.foldl (fun a o => a ^^^ o.eval x) 0

/-- The values of the parts of a term's low half, from the halves `L`, `H`. -/
def _root_.VG.Impl.Sha512.Arm.Op.loVals (L H : BitVec 32) : Op → List (BitVec 32)
  | .rotr n => if n < 32 then [L >>> n, H <<< (32 - n)] else [H >>> (n - 32), L <<< (64 - n)]
  | .shr n => [L >>> n, H <<< (32 - n)]

/-- The values of the parts of a term's high half. -/
def _root_.VG.Impl.Sha512.Arm.Op.hiVals (L H : BitVec 32) : Op → List (BitVec 32)
  | .rotr n => if n < 32 then [H >>> n, L <<< (32 - n)] else [L >>> (n - 32), H <<< (64 - n)]
  | .shr n => [H >>> n]

/-- The term, as a `Word64.Term` (whose value, validity and parts are the same). -/
def _root_.VG.Impl.Sha512.Arm.Op.term : Op → Word64.Term
  | .rotr n => .rotr n
  | .shr n => .shr n

theorem evalOps_term (x : BitVec 64) (ops : List Op) :
    evalOps x ops = Word64.evalOps x (ops.map Op.term) := by
  have e : (fun a (o : Op) => a ^^^ o.eval x) = fun a o => a ^^^ o.term.eval x :=
    funext fun _ => funext fun o => by cases o <;> rfl
  rw [evalOps, Word64.evalOps, List.foldl_map, e]

theorem valid_term {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    ∀ o ∈ ops.map Op.term, o.valid = true := by
  intro o ho
  obtain ⟨o', h', rfl⟩ := List.mem_map.mp ho
  cases o' <;> exact hv _ h'

theorem flatMap_loVals (L H : BitVec 32) (ops : List Op) :
    ops.flatMap (Op.loVals L H) = (ops.map Op.term).flatMap (Word64.Term.loVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih]
    cases o <;> rfl

theorem flatMap_hiVals (L H : BitVec 32) (ops : List Op) :
    ops.flatMap (Op.hiVals L H) = (ops.map Op.term).flatMap (Word64.Term.hiVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih]
    cases o <;> rfl

theorem lo_evalOps (x : BitVec 64) (ops : List Op) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.loVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = lo (evalOps x ops) := by
  rw [flatMap_loVals, evalOps_term]
  exact Word64.lo_evalOps x _ (valid_term hv)

theorem hi_evalOps (x : BitVec 64) (ops : List Op) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.hiVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = hi (evalOps x ops) := by
  rw [flatMap_hiVals, evalOps_term]
  exact Word64.hi_evalOps x _ (valid_term hv)

theorem bsig0_eq (x : BitVec 64) : Spec.Sha512.bsig0 x = evalOps x Impl.Sha512.Arm.bsig0 := by
  simp [evalOps, Impl.Sha512.Arm.bsig0, Spec.Sha512.bsig0, Op.eval]

theorem bsig1_eq (x : BitVec 64) : Spec.Sha512.bsig1 x = evalOps x Impl.Sha512.Arm.bsig1 := by
  simp [evalOps, Impl.Sha512.Arm.bsig1, Spec.Sha512.bsig1, Op.eval]

theorem ssig0_eq (x : BitVec 64) : Spec.Sha512.ssig0 x = evalOps x Impl.Sha512.Arm.ssig0 := by
  simp [evalOps, Impl.Sha512.Arm.ssig0, Spec.Sha512.ssig0, Op.eval]

theorem ssig1_eq (x : BitVec 64) : Spec.Sha512.ssig1 x = evalOps x Impl.Sha512.Arm.ssig1 := by
  simp [evalOps, Impl.Sha512.Arm.ssig1, Spec.Sha512.ssig1, Op.eval]

/-! ## Words in memory -/

theorem readW_lo (m : Mem) (a : Addr) : lo (m.readW a 64) = m.readW a 32 := Word64.readW_lo m a

theorem readW_hi (m : Mem) (a : Addr) : hi (m.readW a 64) = m.readW (a + 4) 32 := Word64.readW_hi m a

/-- A 64-bit word in memory is its high half at `a + 4` and its low half at `a`. -/
theorem readW64 (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + 4) 32 ++ m.readW a 32 :=
  Word64.readW64 m a

end VG.Proof.Sha512.Arm
