import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.TCB.Arm.Target

/-!
# ML-KEM on 32-bit ARM: common lemmas

Untrusted: everything here is checked by Lean. What the proofs of the
primitives share: the rule for a loop counted down to zero (`wp_loop_ne`),
the symbolic execution of a block (`run_block`), addresses in the arrays,
and the arithmetic of the reductions modulo `q` (`fixq`, the value
`VG.Impl.MlKem.Arm.fixup` computes).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm
open VG.Spec.MlKem

/-! ## Loops -/

/-- A `do … while (ne)` loop whose body runs `N` times: iteration `i` keeps
the invariant, and sets `Z` exactly when it is the last. -/
theorem wp_loop_ne {body : Prog isa} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s → WP isa body s (fun s' => Inv (i + 1) s' ∧ s'.z = decide (i + 1 = N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body .ne) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  by_cases h : i + 1 = N
  · refine .inl ⟨?_, hQ s' (h ▸ hs')⟩
    show some (!s'.z) = some false
    rw [hz, decide_eq_true h]; rfl
  · refine .inr ⟨?_, N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩
    show some (!s'.z) = some true
    rw [hz, decide_eq_false h]; rfl

/-- The flag `Z` after `subs r, r, #k` from `k (N - i)`: set when the count
reaches zero. -/
theorem count_z {N i k : Nat} (hi : i < N) (hk0 : 0 < k) (hk : k * N < 2 ^ 32) :
    (BitVec.ofNat 32 (k * (N - i)) - BitVec.ofNat 32 k == 0) = decide (i + 1 = N) := by
  by_cases h : i + 1 = N
  · subst h
    simp only [decide_true, Nat.add_sub_cancel_left, Nat.mul_one, BitVec.sub_self]
    rfl
  · simp only [decide_eq_false h, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    have h1 : k * (N - i) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hk
    have h2 : k * 1 ≤ k * (N - i) := Nat.mul_le_mul_left _ (by omega)
    have h3 : k * 2 ≤ k * (N - i) := Nat.mul_le_mul_left _ (by omega)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt (a := k) (by omega)] at this
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    omega

/-- The count after `subs r, r, #k`. -/
theorem count_sub {N i k : Nat} (hi : i < N) :
    BitVec.ofNat 32 (k * (N - i)) - BitVec.ofNat 32 k = BitVec.ofNat 32 (k * (N - (i + 1))) := by
  have : k * (N - i) = k * (N - (i + 1)) + k := by
    rw [show N - i = (N - (i + 1)) + 1 by omega, Nat.mul_succ]
  rw [this, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-! ## Symbolic execution -/

/-- Runs a straight-line block symbolically (see `WP.of_runBlock`), with the
facts `ls` about the registers and memory it reads. -/
syntax "run_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| run_block [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        Op2.eval, isa, State.setReg, State.load32, State.store32, State.load8, State.store8,
        subFlags, addFlags, ite_true, ite_false, Option.map_some, Option.some.injEq,
        exists_eq_left', List.cons_append, List.nil_append, List.append_nil, $ls,*]))

/-! ## Addresses -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- A pointer `p + i`, plus the offset `o` of an instruction, without
wrapping around. -/
theorem addr_ptr (p : BitVec 32) (i o : Nat) (h : p.toNat + (i + o) < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) = State.addr p + BitVec.ofNat 64 (i + o) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact addr_add h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem inRegions_of {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

/-- An access at offset `off` of a region in `rs`. -/
theorem inRegions_off {rs : List Region} {base : Addr} {len : Nat} (hR : ⟨base, len⟩ ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    InRegions rs (base + BitVec.ofNat 64 off) n :=
  ⟨_, hR, contains_off h ho⟩

theorem mem_append_left' {R : Region} {rs : List Region} (rd : List Region) (h : R ∈ rs) :
    R ∈ rd ++ rs := List.mem_append_right _ h

/-- A byte of a region disjoint from the regions written is unchanged. -/
theorem frame_byte {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {base : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨base, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) {i : Nat} (hi : i < len) :
    m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨base, len⟩) hd hlen hi

/-- A coefficient of a polynomial disjoint from the regions written is
unchanged. -/
theorem frame_coeff {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i :=
  coeffAt_congr (bytes_frame hf hd (by decide)) hi

/-! ## Reduction modulo `q` -/

/-- What `fixup` leaves: `u + q` if `u` is negative, `u` otherwise. -/
def fixq (u : BitVec 32) : BitVec 32 :=
  u + (u >>> 31) + ((u >>> 31) <<< 8) + ((u >>> 31) <<< 10) + ((u >>> 31) <<< 11)

theorem fixq_toNat {u : BitVec 32} (h : u.toNat < 3329 ∨ 2 ^ 32 - 3329 ≤ u.toNat) :
    (fixq u).toNat = if u.toNat < 3329 then u.toNat else u.toNat + 3329 - 2 ^ 32 := by
  unfold fixq
  split <;> bv_omega

/-- `fixq (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixq_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixq (a + b - 3328 - 1)).toNat = (a.toNat + b.toNat) % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (a - b)`: the difference of reduced values, reduced. -/
theorem fixq_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixq (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (x - q)` of `x < 2q`: `x` reduced. -/
theorem fixq_subq {x : BitVec 32} (hx : x.toNat < 2 * q) : (fixq (x - 3328 - 1)).toNat = x.toNat % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

theorem fixq_lt {u : BitVec 32} (h : u.toNat < 3329 ∨ 2 ^ 32 - 3329 ≤ u.toNat) : (fixq u).toNat < q := by
  rw [fixq_toNat h, q_eq]; split <;> omega

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

end VG.Proof.MlKem.Arm
