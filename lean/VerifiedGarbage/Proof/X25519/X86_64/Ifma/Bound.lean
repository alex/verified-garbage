import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Bound

/-!
# X25519 on x86-64 with AVX512_IFMA: terms as numbers

The limbs the ladder computes stay below `2⁶⁴`, and its differences never go
negative, so its additions, subtractions, multiply-adds and shifts never wrap.
`T.bnd` and `T.lb` bound each term from above and below, from bounds on the
registers and memory a block starts from; `T.ok` checks that nothing wraps
under those bounds (and that every blend picks whole quadwords); and `T.nat`
is its value as a number, with the reductions modulo `2⁶⁴` left out. `nat_ok`
proves that a term is `T.nat` and within its bounds where the kernel evaluates
`T.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of the ladder by definition.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw pick2 sel4 sel4_lt capW capW_ge orB orB_ge)

/-- Bounds on what a block starts from: the quadwords of each vector register
(`v`), each general-purpose register (`g`), and each quadword of the 32
bytes at each offset of the working space, from above (`m`) and below
(`ml`). -/
structure Bnds where
  v : Nat → Nat
  g : Reg → Nat
  m : Nat → Nat
  ml : Nat → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat → Nat

def envOf (s₀ : State) : Env :=
  ⟨fun r k => (qw s₀ (xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun d k => (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat⟩

/-- Whether `vpblendd`'s selector takes quadword `k` from its second source
(`some true`), its first (`some false`), or doublewords of both (`none`). -/
def selQ (sel k : Nat) : Option Bool :=
  match sel.testBit (2 * k), sel.testBit (2 * k + 1) with
  | true, true => some true
  | false, false => some false
  | _, _ => none

/-- The bound on the low 52 bits of a product. -/
def loB (a b : Nat) : Nat := min (2 ^ 52 - 1) (min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1))
/-- The bound on the high 52 bits of a product. -/
def hiB (a b : Nat) : Nat := min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1) / 2 ^ 52

def T.bnd (B : Bnds) : T → Nat → Nat
  | .reg r, _ => min (B.v r) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld d, _ => min (B.m d) (2 ^ 64 - 1)
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .sub a _, k => a.bnd B k
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .xor _ _, _ => 2 ^ 64 - 1
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .perm a o, k => a.bnd B (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.bnd B k
    | some false => a.bnd B k
    | none => 2 ^ 64 - 1
  | .mad false c a b, k => capW (c.bnd B k + loB (a.bnd B k) (b.bnd B k))
  | .mad true c a b, k => capW (c.bnd B k + hiB (a.bnd B k) (b.bnd B k))
  | .p2 a b hi, k => if k < 2 then a.bnd B (if hi then k + 2 else k) else b.bnd B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.bnd B k else 0

/-- A lower bound. -/
def T.lb (B : Bnds) : T → Nat → Nat
  | .ld d, _ => B.ml d
  | .add a b, k => a.lb B k + b.lb B k
  | .sub a b, k => a.lb B k - b.bnd B k
  | .perm a o, k => a.lb B (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.lb B k
    | some false => a.lb B k
    | none => 0
  | .mad _ c _ _, k => c.lb B k
  | .bc a, _ => a.lb B 0
  | _, _ => 0

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `T.ok` holds. -/
def T.nat (E : Env) : T → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld d, k => E.m d k
  | .add a b, k => a.nat E k + b.nat E k
  | .sub a b, k => a.nat E k - b.nat E k
  | .and a b, k => a.nat E k &&& b.nat E k
  | .xor a b, k => a.nat E k ^^^ b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .perm a o, k => a.nat E (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.nat E k
    | _ => a.nat E k
  | .mad false c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) % 2 ^ 52
  | .mad true c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) / 2 ^ 52
  | .p2 a b hi, k => if k < 2 then a.nat E (if hi then k + 2 else k) else b.nat E (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.nat E k else 0

/-- Nothing in `t` wraps, by the bounds `B`, and every blend picks whole
quadwords. -/
def T.ok (B : Bnds) : T → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .zero, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .sub a b, k => b.bnd B k ≤ a.lb B k && a.ok B k && b.ok B k
  | .and a b, k | .xor a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .perm a o, k => a.ok B (sel4 o k)
  | .blend a b sel, k => (selQ sel k).isSome && a.ok B k && b.ok B k
  | .mad false c a b, k => c.bnd B k + loB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .mad true c a b, k => c.bnd B k + hiB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .p2 a b hi, k => if k < 2 then a.ok B (if hi then k + 2 else k) else b.ok B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.ok B k else true

/-- What a block starts from is within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 4 → (qw s₀ (xr r) k).toNat ≤ B.v r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  m : ∀ d k, k < 4 → (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat ≤ B.m d
  ml : ∀ d k, k < 4 → B.ml d ≤ (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat

theorem pick2_tt (a b : BitVec 64) : pick2 a b true true = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, ite_true, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem pick2_ff (a b : BitVec 64) : pick2 a b false false = a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, Bool.false_eq_true, ite_false, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem pick2_sel (a b : BitVec 64) (sel k : Nat) (hs : (selQ sel k).isSome = true) :
    pick2 a b (sel.testBit (2 * k)) (sel.testBit (2 * k + 1)) = if selQ sel k = some true then b else a := by
  unfold selQ at hs ⊢
  split at hs <;> simp only [Option.isSome_some, Option.isSome_none, reduceCtorEq] at hs
  · rename_i h1 h2
    rw [h1, h2, ite_eq_left rfl, pick2_tt]
  · rename_i h1 h2
    rw [h1, h2, ite_eq_right (by simp), pick2_ff]

theorem loB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) % 2 ^ 52 ≤ loB a b := by
  unfold loB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.le_min.2 ⟨Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)),
    Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul h1 h2)⟩

theorem hiB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) / 2 ^ 52 ≤ hiB a b := by
  unfold hiB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.div_le_div_right (Nat.mul_le_mul h1 h2)

theorem nat_ok {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) :
    ∀ (t : T) {k : Nat}, k < 4 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k ∧
        t.lb B k ≤ (t.eval s₀ k).toNat := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨by simp only [T.eval, T.nat, envOf], Nat.le_min.2 ⟨hE.v r k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩,
      Nat.zero_le _⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, Nat.zero_le _⟩
  | zero => intro k _ _; exact ⟨rfl, by simp [T.eval, T.bnd], Nat.zero_le _⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih (by decide) ho).1, (ih (by decide) ho).2.1, Nat.zero_le _⟩
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld d =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.m d k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, hE.ml d k hk⟩
  | add a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    refine ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  | sub a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    have hle : (b.eval s₀ k).toNat ≤ (a.eval s₀ k).toNat := by omega
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hle), ← ea, ← eb]
    exact ⟨rfl, by omega, by omega⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩,
      Nat.zero_le _⟩
  | xor a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ^^^ b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_xor] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_sub_one_of_lt this, Nat.zero_le _⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this, Nat.zero_le _⟩
  | shl a n ih =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba, _⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this,
      Nat.zero_le _⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba, _⟩ := ih hk ho
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba, Nat.zero_le _⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(iha hk ho).1, (iha hk ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by omega) ho).1, (ihb (by omega) ho).2.1, Nat.zero_le _⟩
  | unph a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by omega) ho).1, (iha (by omega) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho; exact ⟨(ihb hk ho).1, (ihb hk ho).2.1, Nat.zero_le _⟩
  | perm a o ih =>
    intro k _ ho
    exact ih (sel4_lt _ _) ho
  | blend a b sel iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [pick2_sel _ _ _ _ hs]
    rcases hq : selQ sel k with _ | c
    · rw [hq] at hs; cases hs
    · cases c
      · exact ⟨ea, ba, la⟩
      · simp only [ite_true]; exact ⟨eb, bb, lb⟩
  | mad h c a b ihc iha ihb =>
    intro k hk ho
    have ha := BitVec.isLt (a.eval s₀ k)
    have hb := BitVec.isLt (b.eval s₀ k)
    cases h
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := loB_ge ba bb
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [mad52_toNat]
      simp only [Bool.false_eq_true, ite_false]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega)]
      exact ⟨rfl, capW_ge (by omega) (by omega), by omega⟩
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := hiB_ge ba bb (x := (a.eval s₀ k).toNat) (y := (b.eval s₀ k).toNat)
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [mad52_toNat]
      simp only [ite_true]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega)]
      exact ⟨rfl, capW_ge (by omega) (by omega), by omega⟩
  | p2 a b hi iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by split <;> omega) ho).1, (iha (by split <;> omega) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by split <;> omega) ho).1, (ihb (by split <;> omega) ho).2.1, Nat.zero_le _⟩
  | low a ih =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih hk ho).1, (ih hk ho).2.1, Nat.zero_le _⟩
    · simp

theorem SRel.nat {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 4) (ho : (σ.reg (xi r)).ok B k = true) :
    (qw s r k).toNat = (σ.reg (xi r)).nat (envOf s₀) k ∧ (qw s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact ⟨(nat_ok hE _ hk ho).1, (nat_ok hE _ hk ho).2.1⟩

end VG.Proof.X25519.X86_64.Ifma
