import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Word
import VerifiedGarbage.Impl.Curve448.AArch64.Fast
import VerifiedGarbage.Proof.X448.AArch64.Mem

/-!
# Product accumulation, for any list of steps

Untrusted: everything here is checked by Lean. `mops_ok`: running the code
of a list of `MOp`s leaves in each accumulator, modulo `2 ^ 128`, the signed
sum of products that `sem` computes from the multiplicands' values in the
initial state. The registers are checked once (`Good`, by `decide`): the
temporaries and accumulators are distinct, and no multiplicand is one of them
(`MOp.ok`).
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld)
open VG.Proof.X448.Wide (pair)
open VG.Proof.X448.AArch64 (Keeps Scr word off load_sc addr_word read8_eq)
open VG.Proof.Ed25519.AArch64 (mulHi read_x)

/-- The value of an accumulator. -/
def accVal (s : State) (a : Acc) : Nat := pair (s.gpr a.lo) (s.gpr a.hi)

/-- The value of a multiplicand, for the second operand at `b`. -/
def srcVal (s : State) (base : Addr) (b : Nat) : Src → Nat
  | .reg r => (s.gpr r).toNat
  | .mem d => (word s.mem base d).toNat
  | .arg k => (word s.mem base (b + 8 * k)).toNat

abbrev Env := Acc → Int

def upd (e : Env) (a : Acc) (v : Int) : Env := fun c => if c = a then v else e c

/-- One target of a product `p`. -/
def target (p : Int) (e : Env) (t : Acc × Bool) : Env :=
  upd e t.1 (if t.2 then e t.1 + p else e t.1 - p)

def opSem (v : Src → Nat) (e : Env) : MOp → Env
  | .set a x y => upd e a (v x * v y)
  | .prod x y ts => ts.foldl (target (v x * v y)) e
  | .merge d s add => upd e d (if add then e d + e s else e d - e s)

/-- The accumulators after a list of steps. -/
def sem (v : Src → Nat) : Env → List MOp → Env
  | e, [] => e
  | e, op :: ops => sem v (opSem v e op) ops

/-! ## Well-formedness, by `decide` -/

def accRegs (accs : List Acc) : List Reg := accs.flatMap fun a => [a.lo, a.hi]

/-- The registers the steps may write. -/
def writes (R : Regs) (accs : List Acc) : List Reg := R.t :: R.p0 :: R.p1 :: accRegs accs

/-- Distinct temporaries and accumulators, other than `x3` and `x12`. -/
abbrev Good (R : Regs) (accs : List Acc) : Prop :=
  R.t ≠ R.p0 ∧ R.t ≠ R.p1 ∧ R.p0 ≠ R.p1 ∧
  (∀ a ∈ accs, a.lo ≠ a.hi ∧ a.lo ∉ [R.t, R.p0, R.p1] ∧ a.hi ∉ [R.t, R.p0, R.p1]) ∧
  (∀ a ∈ accs, ∀ c ∈ accs, a ≠ c → a.lo ∉ [c.lo, c.hi] ∧ a.hi ∉ [c.lo, c.hi]) ∧
  .x3 ∉ writes R accs ∧ .x12 ∉ writes R accs

def srcOk (W : List Reg) : Src → Bool
  | .reg r => !W.contains r
  | .mem d => d % 8 == 0 && d + 8 ≤ 8192
  | .arg k => k < 8

def opOk (W : List Reg) (accs : List Acc) : MOp → Bool
  | .set a x y => accs.contains a && srcOk W x && srcOk W y
  | .prod x y ts => srcOk W x && srcOk W y && ts.all (fun t => accs.contains t.1)
  | .merge d s _ => accs.contains d && accs.contains s && d != s

/-! ## The instructions -/

theorem ld_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat}
    (h8 : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [ld r d]) s fun t =>
      t.gpr r = word s.mem base d ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  have l := hs.read (d := d) (n := 8) hd
  have ae : d % 8 = 0 ∧ d < 32768 := ⟨h8, by omega⟩
  refine WP.of_runBlock ⟨_, by
    simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, ae, and_self, hs.x3, l, ite_true, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]
    exact BitVec.setWidth_eq _
  · exact RegUpd.gpr_write_of_ne _ _ _ (fun e => hq (by simp [e]))

theorem mul2_ok (s : State) {d₁ d₂ x y : Reg} (h₁ : d₁ ≠ x) (h₂ : d₁ ≠ y) (h₃ : d₁ ≠ d₂) :
    WP isa (.block [.mul .x d₁ x y, .umulh d₂ x y]) s fun t =>
      pair (t.gpr d₁) (t.gpr d₂) = (s.gpr x).toNat * (s.gpr y).toNat ∧ t.mem = s.mem ∧
      Keeps [d₁, d₂] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [State.read, BitVec.setWidth_eq, RegUpd.gpr_write, h₃, Ne.symm h₁, Ne.symm h₂,
      ite_true, ite_false]
    exact mulPair (s.gpr x) (s.gpr y)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [RegUpd.gpr_write_of_ne _ _ _ hq.2, RegUpd.gpr_write_of_ne _ _ _ hq.1]

theorem addPair_ok (s : State) (a : Acc) {lo hi : Reg} (add : Bool) (h₁ : a.lo ≠ a.hi)
    (h₂ : a.lo ≠ hi) :
    WP isa (.block (addPair a lo hi add)) s fun t =>
      accVal t a = (if add then (accVal s a + pair (s.gpr lo) (s.gpr hi)) % M
        else (accVal s a + (M - pair (s.gpr lo) (s.gpr hi))) % M) ∧ t.mem = s.mem ∧
      Keeps [a.lo, a.hi] s t := by
  cases add
  all_goals
    refine WP.of_runBlock ⟨_, by
      simp only [addPair, Bool.false_eq_true, ite_false, ite_true, runBlock_cons, runStep_some,
        runBlock_nil, exec]; rfl, ?_⟩
    refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]
  · have := subPair_mod (s.gpr a.lo) (s.gpr a.hi) (s.gpr lo) (s.gpr hi)
    simp only [accVal, read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, h₁, Ne.symm h₁,
      Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq, Bool.false_eq_true]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this
  · have := addPair_mod (s.gpr a.lo) (s.gpr a.hi) (s.gpr lo) (s.gpr hi)
    simp only [accVal, read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, h₁, Ne.symm h₁,
      Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this

/-! ## Registers of well-formed steps -/

section
variable {R : Regs} {accs : List Acc}

theorem lo_mem {a : Acc} (h : a ∈ accs) : a.lo ∈ writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨a, h, List.mem_cons_self⟩)))

theorem hi_mem {a : Acc} (h : a ∈ accs) : a.hi ∈ writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨a, h, List.mem_cons_of_mem _ List.mem_cons_self⟩)))

theorem t_mem : R.t ∈ writes R accs := List.mem_cons_self
theorem p0_mem : R.p0 ∈ writes R accs := List.mem_cons_of_mem _ List.mem_cons_self
theorem p1_mem : R.p1 ∈ writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem accRegs_sub {r : Reg} (h : r ∈ accRegs accs) : r ∈ writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

theorem pair_sub {a : Acc} (h : a ∈ accs) {r : Reg} (hr : r ∈ [a.lo, a.hi]) : r ∈ accRegs accs :=
  List.mem_flatMap.mpr ⟨a, h, hr⟩

theorem reg_not_mem {r : Reg} (h : srcOk (writes R accs) (.reg r) = true) :
    r ∉ writes R accs := by
  intro hm
  simp [srcOk, hm] at h

/-- A multiplicand's register is its temporary or is not written. -/
theorem reg?_cases {r : Reg} {x : Src} (h : srcOk (writes R accs) x = true) :
    x.reg? r = r ∨ x.reg? r ∉ writes R accs := by
  cases x with
  | reg q => exact Or.inr (reg_not_mem h)
  | mem d => exact Or.inl rfl
  | arg k => exact Or.inl rfl

theorem Good.acc (hG : Good R accs) {a : Acc} (h : a ∈ accs) :
    a.lo ≠ a.hi ∧ a.lo ∉ [R.t, R.p0, R.p1] ∧ a.hi ∉ [R.t, R.p0, R.p1] := hG.2.2.2.1 a h

theorem Good.disj (hG : Good R accs) {a c : Acc} (ha : a ∈ accs) (hc : c ∈ accs) (h : a ≠ c) :
    a.lo ∉ [c.lo, c.hi] ∧ a.hi ∉ [c.lo, c.hi] := hG.2.2.2.2.1 a ha c hc h

theorem Good.scr (hG : Good R accs) {s t : State} {base : Addr} (hs : Scr s base) {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ writes R accs) : Scr t base :=
  hs.of_keeps h ⟨fun e => hG.2.2.2.2.2.1 (hrs _ e), fun e => hG.2.2.2.2.2.2 (hrs _ e)⟩

end

/-! ## One step -/

def AccsEq (accs : List Acc) (s : State) (e : Env) : Prop :=
  ∀ a ∈ accs, (accVal s a : Int) = e a % M

theorem accVal_keep {s t : State} {rs : List Reg} (h : Keeps rs s t) {a : Acc}
    (hlo : a.lo ∉ rs) (hhi : a.hi ∉ rs) : accVal t a = accVal s a := by
  simp only [accVal, h.1 _ hlo, h.1 _ hhi]

theorem add_emod' {x p : Nat} {e f : Int} (h : (x : Int) = e % M) (hp : (p : Int) = f % M) :
    (((x + p) % M : Nat) : Int) = (e + f) % M := by
  rw [Int.natCast_emod, Int.natCast_add, h, hp, Int.emod_add_emod, Int.add_emod_emod]

theorem sub_emod' {x p : Nat} {e f : Int} (h : (x : Int) = e % M) (hp : (p : Int) = f % M)
    (hpM : p ≤ M) : (((x + (M - p)) % M : Nat) : Int) = (e - f) % M := by
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub hpM, h, hp, Int.emod_add_emod]
  rw [show e + ((M : Nat) - f % (M : Nat)) = (e - f % (M : Nat)) + (M : Nat) by omega,
    Int.add_emod_right, Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]

theorem self_emod {x : Nat} (h : x < M) : (x : Int) = (x : Int) % M := by
  rw [← Int.natCast_emod, Nat.mod_eq_of_lt h]

theorem upd_self (e : Env) (a : Acc) (v : Int) : upd e a v a = v := by simp [upd]
theorem upd_ne (e : Env) {a c : Acc} (v : Int) (h : c ≠ a) : upd e a v c = e c := by simp [upd, h]

section
variable {R : Regs} {accs : List Acc} {base : Addr} {b : Nat}

theorem load_ok (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State} (hs : Scr s base) (r : Reg)
    {x : Src} (hx : srcOk (writes R accs) x = true) :
    WP isa (.block (x.load b r)) s fun t =>
      (t.gpr (x.reg? r)).toNat = srcVal s base b x ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  cases x with
  | reg q => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | mem d =>
    simp only [srcOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    exact WP.mono (ld_ok hs r hx.1 hx.2) fun t ⟨h1, h2, h3⟩ =>
      ⟨by simp only [Src.reg?, h1, srcVal], h2, h3⟩
  | arg k =>
    simp only [srcOk, decide_eq_true_eq] at hx
    exact WP.mono (ld_ok hs r (d := b + 8 * k) (by omega) (by omega))
      fun t ⟨h1, h2, h3⟩ => ⟨by simp only [Src.reg?, h1, srcVal], h2, h3⟩

theorem loads_ok (hG : Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State}
    (hs : Scr s base) {x y : Src} (hx : srcOk (writes R accs) x = true)
    (hy : srcOk (writes R accs) y = true) :
    WP isa (.block (x.load b R.p0 ++ y.load b R.p1)) s fun t =>
      (t.gpr (x.reg? R.p0)).toNat = srcVal s base b x ∧
      (t.gpr (y.reg? R.p1)).toNat = srcVal s base b y ∧ t.mem = s.mem ∧
      Keeps [R.p0, R.p1] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hb8 hb hs R.p0 hx) fun t ⟨tx, tm, tk⟩ => ?_
  have ts : Scr t base := hG.scr hs tk (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr ▸ p0_mem)
  refine WP.mono (load_ok hb8 hb ts R.p1 hy) fun u ⟨uy, um, uk⟩ => ?_
  have xne : x.reg? R.p0 ∉ [R.p1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases reg?_cases (r := R.p0) hx with h | h
    · rw [h]; exact hG.2.2.1
    · exact fun e => h (e ▸ p1_mem)
  have yv : srcVal t base b y = srcVal s base b y := by
    cases y with
    | reg q =>
      have hq := reg_not_mem hy
      have hq' : q ∉ [R.p0] := fun e => hq (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        exact e ▸ p0_mem)
      simp only [srcVal]
      rw [tk.1 q hq']
    | mem d => simp only [srcVal, tm]
    | arg k => simp only [srcVal, tm]
  refine ⟨by rw [uk.1 _ xne, tx], by rw [uy, yv], um.trans tm, ?_⟩
  refine (tk.mono ?_).trans (uk.mono ?_) <;> intro r hr <;> simp_all

theorem targets_ok (hG : Good R accs) (P : Nat) (ts : List (Acc × Bool)) (hts : ∀ t ∈ ts, t.1 ∈ accs)
    {s : State} (hP : pair (s.gpr R.t) (s.gpr R.p1) = P) {e : Env} (he : AccsEq accs s e) :
    WP isa (.block (ts.flatMap fun a => addPair a.1 R.t R.p1 a.2)) s fun u =>
      AccsEq accs u (ts.foldl (target P) e) ∧ u.mem = s.mem ∧ Keeps (accRegs accs) s u := by
  induction ts generalizing s e with
  | nil => exact WP.block_nil ⟨he, rfl, Keeps.refl _ _⟩
  | cons t ts ih =>
    have ht := hts t List.mem_cons_self
    obtain ⟨hlh, hlo, hhi⟩ := hG.acc ht
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (addPair_ok s t.1 t.2 hlh (fun e => hlo (by simp [e])))
      fun u ⟨uv, um, uk⟩ => ?_
    have tk : R.t ∉ [t.1.lo, t.1.hi] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hlo (by simp [e]), fun e => hhi (by simp [e])⟩
    have pk : R.p1 ∉ [t.1.lo, t.1.hi] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hlo (by simp [e]), fun e => hhi (by simp [e])⟩
    have hP' : pair (u.gpr R.t) (u.gpr R.p1) = P := by rw [uk.1 _ tk, uk.1 _ pk, hP]
    have he' : AccsEq accs u (target P e t) := by
      intro c hc
      by_cases hct : c = t.1
      · subst hct
        simp only [target, upd_self]
        rw [uv, ← hP]
        cases t.2
        · exact sub_emod' (he _ hc) (self_emod (pair_lt _ _)) (Nat.le_of_lt (pair_lt _ _))
        · exact add_emod' (he _ hc) (self_emod (pair_lt _ _))
      · obtain ⟨d1, d2⟩ := hG.disj hc ht hct
        rw [accVal_keep uk d1 d2, target, upd_ne _ _ hct]
        exact he c hc
    refine WP.mono (ih (fun t' h => hts t' (List.mem_cons_of_mem _ h)) hP' he')
      fun w ⟨wv, wm, wk⟩ => ⟨wv, wm.trans um, (uk.mono ?_).trans wk⟩
    intro r hr; exact pair_sub ht hr

/-- Registers that are neither temporaries nor in an accumulator other than the written ones. -/
theorem other_acc (hG : Good R accs) {a c : Acc} (ha : a ∈ accs) (hc : c ∈ accs) (h : c ≠ a)
    {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ [R.t, R.p0, R.p1] ∨ r ∈ [a.lo, a.hi]) :
    c.lo ∉ rs ∧ c.hi ∉ rs := by
  obtain ⟨-, hlo, hhi⟩ := hG.acc hc
  obtain ⟨d1, d2⟩ := hG.disj hc ha h
  exact ⟨fun e => (hrs _ e).elim hlo d1, fun e => (hrs _ e).elim hhi d2⟩

theorem mop_ok (hG : Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State}
    (hs : Scr s base) (op : MOp) (hop : opOk (writes R accs) accs op = true) {v : Src → Nat}
    (hv : ∀ x, srcOk (writes R accs) x = true → srcVal s base b x = v x)
    {e : Env} (he : AccsEq accs s e) :
    WP isa (.block (op.code R b)) s fun t =>
      AccsEq accs t (opSem v e op) ∧ t.mem = s.mem ∧ Keeps (writes R accs) s t := by
  have sub : ∀ r ∈ accRegs accs, r ∈ writes R accs := fun r h => accRegs_sub h
  cases op with
  | set a x y =>
    simp only [opOk, Bool.and_eq_true, List.contains_iff_mem] at hop
    obtain ⟨⟨ha, hx⟩, hy⟩ := hop
    obtain ⟨hlh, hlo, hhi⟩ := hG.acc ha
    simp only [MOp.code, List.append_assoc]
    rw [← List.append_assoc, WP.block_append_iff]
    refine WP.mono (loads_ok hG hb8 hb hs hx hy) fun t ⟨tx, ty, tm, tk⟩ => ?_
    have nx : a.lo ≠ x.reg? R.p0 := by
      rcases reg?_cases (r := R.p0) hx with h | h
      · rw [h]; exact fun e => hlo (by simp [e])
      · exact fun e => h (e ▸ lo_mem ha)
    have ny : a.lo ≠ y.reg? R.p1 := by
      rcases reg?_cases (r := R.p1) hy with h | h
      · rw [h]; exact fun e => hlo (by simp [e])
      · exact fun e => h (e ▸ lo_mem ha)
    refine WP.mono (mul2_ok t nx ny hlh) fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, ?_⟩
    · intro c hc
      by_cases hca : c = a
      · subst hca
        simp only [opSem, upd_self]
        change ((pair (u.gpr c.lo) (u.gpr c.hi) : Nat) : Int) = _
        have hlt : v x * v y < M := by
          rw [← hv x hx, ← hv y hy, ← tx, ← ty, ← uv]; exact pair_lt _ _
        rw [uv, tx, ty, hv x hx, hv y hy, ← Int.natCast_mul]
        exact self_emod hlt
      · obtain ⟨n1, n2⟩ := other_acc hG ha hc hca (rs := [R.p0, R.p1]) (by simp)
        obtain ⟨n3, n4⟩ := other_acc hG ha hc hca (rs := [a.lo, a.hi]) (by simp)
        rw [accVal_keep uk n3 n4, accVal_keep tk n1 n2]
        simp only [opSem, upd_ne _ _ hca]
        exact he c hc
    · refine (tk.mono ?_).trans (uk.mono ?_)
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact p0_mem
        · exact p1_mem
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact lo_mem ha
        · exact hi_mem ha
  | prod x y ts =>
    simp only [opOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hop
    obtain ⟨⟨hx, hy⟩, hts⟩ := hop
    simp only [MOp.code, List.append_assoc]
    rw [← List.append_assoc, WP.block_append_iff]
    refine WP.mono (loads_ok hG hb8 hb hs hx hy) fun t ⟨tx, ty, tm, tk⟩ => ?_
    have ts' : Scr t base := hG.scr hs tk (by simp [p0_mem, p1_mem])
    have nx : R.t ≠ x.reg? R.p0 := by
      rcases reg?_cases (r := R.p0) hx with h | h
      · rw [h]; exact hG.1
      · exact fun e => h (e ▸ t_mem)
    have ny : R.t ≠ y.reg? R.p1 := by
      rcases reg?_cases (r := R.p1) hy with h | h
      · rw [h]; exact hG.2.1
      · exact fun e => h (e ▸ t_mem)
    rw [WP.block_append_iff]
    refine WP.mono (mul2_ok t nx ny hG.2.1) fun u ⟨uv, um, uk⟩ => ?_
    have he' : AccsEq accs u e := by
      intro c hc
      obtain ⟨-, hlo, hhi⟩ := hG.acc hc
      have n1 : c.lo ∉ [R.p0, R.p1] := fun h => hlo (by simp at h; rcases h with h | h <;> simp [h])
      have n2 : c.hi ∉ [R.p0, R.p1] := fun h => hhi (by simp at h; rcases h with h | h <;> simp [h])
      have n3 : c.lo ∉ [R.t, R.p1] := fun h => hlo (by simp at h; rcases h with h | h <;> simp [h])
      have n4 : c.hi ∉ [R.t, R.p1] := fun h => hhi (by simp at h; rcases h with h | h <;> simp [h])
      rw [accVal_keep uk n3 n4, accVal_keep tk n1 n2]
      exact he c hc
    have hP : pair (u.gpr R.t) (u.gpr R.p1) = v x * v y := by rw [uv, tx, ty, hv x hx, hv y hy]
    refine WP.mono (targets_ok hG _ ts hts hP he') fun w ⟨wv, wm, wk⟩ =>
      ⟨by simpa only [opSem, Nat.cast_mul] using wv, wm.trans (um.trans tm), ?_⟩
    refine ((tk.mono ?_).trans (uk.mono ?_)).trans (wk.mono sub)
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact p0_mem
      · exact p1_mem
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact t_mem
      · exact p1_mem
  | merge d c add =>
    simp only [opOk, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hop
    obtain ⟨⟨hd, hc⟩, hdc⟩ := hop
    obtain ⟨hlh, -, -⟩ := hG.acc hd
    obtain ⟨d1, -⟩ := hG.disj hd hc hdc
    have nh : d.lo ≠ c.hi := fun e => d1 (by simp [e])
    simp only [MOp.code]
    refine WP.mono (addPair_ok s d add hlh nh) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono ?_⟩
    · intro a ha
      by_cases had : a = d
      · subst had
        simp only [opSem, upd_self]
        change ((accVal u a : Nat) : Int) = _
        rw [uv]
        have hcv : ((pair (s.gpr c.lo) (s.gpr c.hi) : Nat) : Int) = e c % M := he c hc
        cases add
        · exact sub_emod' (he a ha) hcv (Nat.le_of_lt (pair_lt _ _))
        · exact add_emod' (he a ha) hcv
      · obtain ⟨n1, n2⟩ := hG.disj ha hd had
        rw [accVal_keep uk n1 n2]
        simp only [opSem, upd_ne _ _ had]
        exact he a ha
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact lo_mem hd
      · exact hi_mem hd

theorem mops_ok (hG : Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ops : List MOp)
    (hops : ops.all (opOk (writes R accs) accs) = true) {s : State} (hs : Scr s base)
    {v : Src → Nat} (hv : ∀ x, srcOk (writes R accs) x = true → srcVal s base b x = v x)
    {e : Env} (he : AccsEq accs s e) :
    WP isa (.block (ops.flatMap (MOp.code R b))) s fun t =>
      AccsEq accs t (sem v e ops) ∧ t.mem = s.mem ∧ Keeps (writes R accs) s t := by
  induction ops generalizing s e with
  | nil => exact WP.block_nil ⟨he, rfl, Keeps.refl _ _⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hops
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (mop_ok hG hb8 hb hs op hops.1 hv he) fun t ⟨tv, tm, tk⟩ => ?_
    have hv' : ∀ x, srcOk (writes R accs) x = true → srcVal t base b x = v x := by
      intro x hx
      rw [← hv x hx]
      cases x with
      | reg q => simp only [srcVal, tk.1 q (reg_not_mem hx)]
      | mem d => simp only [srcVal, tm]
      | arg k => simp only [srcVal, tm]
    refine WP.mono (ih hops.2 (hG.scr hs tk (fun _ h => h)) hv' tv) fun u ⟨uv, um, uk⟩ =>
      ⟨uv, um.trans tm, tk.trans uk⟩

end

end VG.Proof.Curve448.AArch64.Fast
