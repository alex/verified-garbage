import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym

/-!
# Poly1305 on x86-64 with AVX2: terms as numbers

The limbs the code computes stay far below `2⁶⁴`, so its additions, products
and shifts never wrap. `Q.bnd` bounds each term from bounds on the registers
it starts from, `Q.ok` checks that its additions and left shifts do not wrap
under those bounds, and `Q.nat` is its value as a number, with the reductions
modulo `2⁶⁴` (and to the low doubleword, for products) left out. `nat_ok`
proves that a term is `Q.nat` and within `Q.bnd` where the kernel evaluates
`Q.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of `Limbs26` by definition. `Q.natw`
is the value with every reduction kept, which `natw_ok` proves exact for any
term, for the blocks that shift bits out on purpose.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64

/-- Bounds on the registers a block starts from: on each vector register's
quadwords (`v`) and their low doublewords (`lo`), and on the general-purpose
registers. -/
structure Bnds where
  v : XReg → Nat
  lo : XReg → Nat
  g : Reg → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat

def envOf (s₀ : State) : Env :=
  ⟨fun r k => (qw s₀ (xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun j => (s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64).toNat⟩

def capW (x : Nat) : Nat := if x < 2 ^ 64 then x else 2 ^ 64 - 1

/-- A bound on `x ||| y` for `x ≤ a`, `y ≤ b`. -/
def orB (a b : Nat) : Nat := capW (2 ^ max (a.log2 + 1) (b.log2 + 1) - 1)

/-- A bound on the low doubleword of `t`, whose bound is `b`. -/
def loB (B : Bnds) (t : Q) (b : Nat) : Nat :=
  match t with
  | .reg r => min (B.lo (xr r)) (min b (2 ^ 32 - 1))
  | _ => min b (2 ^ 32 - 1)

def Q.bnd (B : Bnds) : Q → Nat → Nat
  | .reg r, _ => min (B.v (xr r)) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld _, _ => 2 ^ 64 - 1
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .mul a b, k => loB B a (a.bnd B k) * loB B b (b.bnd B k)
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .andn _ b, k => b.bnd B k
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .perm a o, k => a.bnd B (sel4 o k)
  | .blend _ _ _, _ => 2 ^ 64 - 1

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `Q.ok` holds. -/
def Q.nat (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld i, k => E.m (i + k)
  | .add a b, k => a.nat E k + b.nat E k
  | .mul a b, k => a.nat E k % 2 ^ 32 * (b.nat E k % 2 ^ 32)
  | .and a b, k => a.nat E k &&& b.nat E k
  | .andn a b, k => (2 ^ 64 - 1 - a.nat E k) &&& b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .perm a o, k => a.nat E (sel4 o k)
  | .blend a b sel, k =>
    (pick2 (BitVec.ofNat 64 (a.nat E k)) (BitVec.ofNat 64 (b.nat E k)) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1))).toNat

/-- The value of a term as a number, reduced as the code does: exact
whatever the bounds (`natw_ok`), for the blocks that shift bits out on
purpose. -/
def Q.natw (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.natw E 0 else 0
  | .bc a, _ => a.natw E 0
  | .ld i, k => E.m (i + k)
  | .add a b, k => (a.natw E k + b.natw E k) % 2 ^ 64
  | .mul a b, k => a.natw E k % 2 ^ 32 * (b.natw E k % 2 ^ 32)
  | .and a b, k => a.natw E k &&& b.natw E k
  | .andn a b, k => (2 ^ 64 - 1 - a.natw E k) &&& b.natw E k
  | .or a b, k => a.natw E k ||| b.natw E k
  | .shl a n, k => a.natw E k * 2 ^ n % 2 ^ 64
  | .shr a n, k => a.natw E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.natw E k else b.natw E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.natw E (k + 1) else b.natw E k
  | .perm a o, k => a.natw E (sel4 o k)
  | .blend a b sel, k =>
    (pick2 (BitVec.ofNat 64 (a.natw E k)) (BitVec.ofNat 64 (b.natw E k)) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1))).toNat

/-- No addition or left shift in `t` wraps, by the bounds `B`. -/
def Q.ok (B : Bnds) : Q → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .mul a b, k | .and a b, k | .andn a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .perm a o, k => a.ok B (sel4 o k)
  | .blend a b _, k => a.ok B k && b.ok B k

/-- The registers `s₀` starts from are within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 4 → (qw s₀ r k).toNat ≤ B.v r
  lo : ∀ r k, k < 4 → (qw s₀ r k).toNat % 2 ^ 32 ≤ B.lo r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g

theorem capW_ge {x y : Nat} (h : x ≤ y) (hx : x < 2 ^ 64) : x ≤ capW y := by
  unfold capW; split <;> omega

theorem orB_ge {x y a b : Nat} (ha : x ≤ a) (hb : y ≤ b) (hx : x ||| y < 2 ^ 64) : x ||| y ≤ orB a b := by
  apply capW_ge _ hx
  have h₁ : x < 2 ^ max (a.log2 + 1) (b.log2 + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt ha Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have h₂ : y < 2 ^ max (a.log2 + 1) (b.log2 + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hb Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  have := Nat.or_lt_two_pow h₁ h₂
  omega

theorem lo32_toNat (x : BitVec 64) : (lo32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [lo32, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

theorem loB_ge {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) {t : Q} {k : Nat} (hk : k < 4) {b : Nat}
    (hb : (t.eval s₀ k).toNat ≤ b) : (t.eval s₀ k).toNat % 2 ^ 32 ≤ loB B t b := by
  unfold loB
  split
  · rename_i r
    have := hE.lo (xr r) k hk
    have h₁ := Nat.mod_le (qw s₀ (xr r) k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (qw s₀ (xr r) k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [Q.eval] at hb ⊢
    omega
  · have h₁ := Nat.mod_le (t.eval s₀ k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (t.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    omega

theorem nat_ok {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) :
    ∀ (t : Q) {k : Nat}, k < 4 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.v (xr r) k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ih (by decide) ho
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld i =>
    intro k _ _
    refine ⟨?_, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩
    simp only [Q.eval, Q.nat, envOf, Nat.mul_add]
  | add a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | mul a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have la := loB_ge hE hk ba
    have lb := loB_ge hE hk bb
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_mul, lo32_toNat]
    rw [← ea, ← eb]
    have p₁ := Nat.mod_lt (a.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have hp : (a.eval s₀ k).toNat % 2 ^ 32 * ((b.eval s₀ k).toNat % 2 ^ 32) < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt hp]
    exact ⟨rfl, Nat.mul_le_mul la lb⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩⟩
  | andn a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, _⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and, BitVec.toNat_not]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_trans Nat.and_le_right bb⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this⟩
  | shl a n ih =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba⟩ := ih hk ho
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha hk ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (by omega) ho
  | unph a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (by omega) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb hk ho
  | perm a o ih =>
    intro k _ ho
    exact ih (sel4_lt _ _) ho
  | blend a b sel iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, _⟩ := iha hk ho.1
    obtain ⟨eb, _⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd]
    rw [← ea, ← eb, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]
    exact ⟨rfl, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩

theorem natw_ok (s₀ : State) : ∀ (t : Q) (k : Nat), (t.eval s₀ k).toNat = t.natw (envOf s₀) k := by
  intro t
  induction t with
  | reg r => intro k; rfl
  | gpr g => intro k; rfl
  | lane0 a ih =>
    intro k
    simp only [Q.eval, Q.natw]
    split
    · exact ih 0
    · rfl
  | bc a ih => intro k; exact ih 0
  | ld i => intro k; simp only [Q.eval, Q.natw, envOf, Nat.mul_add]
  | add a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_add, iha, ihb]
  | mul a b iha ihb =>
    intro k
    simp only [Q.eval, Q.natw, BitVec.toNat_mul, lo32_toNat, iha, ihb]
    have p₁ := Nat.mod_lt (a.natw (envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.natw (envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide))
  | and a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, iha, ihb]
  | andn a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, BitVec.toNat_not, iha, ihb]
  | or a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_or, iha, ihb]
  | shl a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ih]
  | shr a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ih]
  | unpl a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha k
    · exact ihb _
  | unph a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb k
  | perm a o ih => intro k; exact ih _
  | blend a b sel iha ihb =>
    intro k
    simp only [Q.eval, Q.natw]
    rw [← iha, ← ihb, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem SRel.nat {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 4) (ho : (σ.reg (xi r)).ok B k = true) :
    (qw s r k).toNat = (σ.reg (xi r)).nat (envOf s₀) k ∧ (qw s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact nat_ok hE _ hk ho

theorem SRel.natw {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) (r : XReg) {k : Nat} (hk : k < 4) :
    (qw s r k).toNat = (σ.reg (xi r)).natw (envOf s₀) k := by
  rw [h.reg r k hk]; exact natw_ok s₀ _ k

theorem envOf_v (s₀ : State) (r : XReg) (k : Nat) : (envOf s₀).v (xi r) k = (qw s₀ r k).toNat := by
  simp only [envOf, xr_xi]

end VG.Proof.Poly1305.X86_64.Avx2
