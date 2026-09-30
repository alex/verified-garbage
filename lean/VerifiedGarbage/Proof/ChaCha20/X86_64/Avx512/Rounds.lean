import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.ChaCha20.Spec

/-!
# ChaCha20 on x86-64 with AVX-512: the rounds

Untrusted: everything here is checked by Lean. Doubleword `j` of a register
(doubleword `j % 4` of lane `j / 4`) holds a word of block `j`, register `k`
word `k`. Every instruction of the rounds acts on each block as a step on its
state (`zstep`), so the rounds are proven once on the sixteen states and then,
without the machine, equal to the specification's.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

/-- The number of a vector register. -/
def xidx : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

theorem xidx_lt (r : XReg) : xidx r < 16 := by cases r <;> decide

theorem xidx_inj {r r' : XReg} : xidx r = xidx r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

theorem xidx_zreg : ∀ k < 16, xidx (zreg k) = k := by decide

/-- Doubleword `j` of `r`: the word of block `j`. -/
abbrev zw (s : State) (r : XReg) (j : Nat) : Word := dword (s.zlane r (j / 4)) (j % 4)

/-- The sixteen states `vs 0, …, vs 15` are in the registers: word `k` of
block `j` in doubleword `j` of register `k`. -/
def ZH (vs : Nat → CState) (s : State) : Prop :=
  ∀ r j, j < 16 → zw s r j = (vs j)[xidx r]'(xidx_lt r)

/-- The instructions of the rounds: `vpaddd`, `vpxord` and `vprold` on `zmm`
registers. -/
inductive ZI
  | add (d a b : XReg) | xor (d a b : XReg) | rol (d a : XReg) (n : BitVec 8)

def ZI.instr : ZI → Instr
  | .add d a b => z .vpaddd d a b
  | .xor d a b => z .vpxord d a b
  | .rol d a n => .zop (.vprold d a n)

/-- An instruction of the rounds, on one block's state. -/
def zstep (v : CState) : ZI → CState
  | .add d a b => v.set (xidx d) (v[xidx a]'(xidx_lt a) + v[xidx b]'(xidx_lt b)) (xidx_lt d)
  | .xor d a b => v.set (xidx d) (v[xidx a]'(xidx_lt a) ^^^ v[xidx b]'(xidx_lt b)) (xidx_lt d)
  | .rol d a n => v.set (xidx d) ((v[xidx a]'(xidx_lt a)).rotateLeft (n.toNat % 32)) (xidx_lt d)

theorem div4_lt {j : Nat} (hj : j < 16) : j / 4 < 4 := by omega
theorem mod4_lt (j : Nat) : j % 4 < 4 := Nat.mod_lt _ (by decide)

theorem getElem_set_xidx (v : CState) (d r : XReg) (x : Word) :
    (v.set (xidx d) x (xidx_lt d))[xidx r]'(xidx_lt r) = if r = d then x else v[xidx r]'(xidx_lt r) := by
  rw [Vector.getElem_set]
  by_cases h : r = d
  · subst h; simp
  · simp [h, xidx_inj, Ne.symm h]

/-- One instruction of the rounds, on all sixteen blocks. -/
theorem step_ok (i : ZI) {vs : Nat → CState} {s : State} (h : ZH vs s) :
    ∃ s', exec i.instr s = some s' ∧ ZH (fun j => zstep (vs j) i) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | add d a b =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zw, zlane_zbin _ _ _ _ _ _ (div4_lt hj), zstep, getElem_set_xidx]
    split
    · simp only [ZBinOp.sse, dword_paddd _ _ (mod4_lt j)]; rw [← h a j hj, ← h b j hj]
    · exact h r j hj
  | xor d a b =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zw, zlane_zbin _ _ _ _ _ _ (div4_lt hj), zstep, getElem_set_xidx]
    split
    · simp only [ZBinOp.sse, dword_pxor]; rw [← h a j hj, ← h b j hj]
    · exact h r j hj
  | rol d a n =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zw, zlane_vprold _ _ _ _ _ (div4_lt hj), zstep, getElem_set_xidx]
    split
    · rw [dword_rolDwords _ _ (mod4_lt j), ← h a j hj]
    · exact h r j hj

/-- The frame of the rounds. -/
structure Same (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Instructions of the rounds, in sequence, on all sixteen blocks. -/
theorem block_ok : ∀ (is : List ZI) {vs : Nat → CState} {s : State}, ZH vs s →
    WP isa (.block (is.map ZI.instr)) s fun s' => ZH (fun j => is.foldl zstep (vs j)) s' ∧ Same s s'
  | [], _, _, h => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | i :: is, _, _, h => by
    obtain ⟨s', he, h', g, m, r, w⟩ := step_ok i h
    exact WP.block_cons_iff.2 ⟨s', he, WP.mono (block_ok is h') fun _ ⟨ht, hs⟩ =>
      ⟨ht, hs.gpr.trans g, hs.mem.trans m, hs.rd.trans r, hs.wr.trans w⟩⟩

/-- `half`, as instructions of the rounds. -/
def halfZ (qs : List (XReg × XReg × XReg × XReg)) (r₁ r₂ : BitVec 8) : List ZI :=
  qs.map (fun (a, b, _, _) => .add a a b) ++
  qs.map (fun (a, _, _, d) => .xor d d a) ++
  qs.map (fun (_, _, _, d) => .rol d d r₁) ++
  qs.map (fun (_, _, c, d) => .add c c d) ++
  qs.map (fun (_, b, c, _) => .xor b b c) ++
  qs.map (fun (_, b, _, _) => .rol b b r₂)

theorem half_eq (qs : List (XReg × XReg × XReg × XReg)) (r₁ r₂ : BitVec 8) :
    half qs r₁ r₂ = (halfZ qs r₁ r₂).map ZI.instr := by
  simp only [half, halfZ, List.map_append, List.map_map]; rfl

def quartersZ (ws : List (Nat × Nat × Nat × Nat)) : List ZI :=
  let qs := ws.map fun (a, b, c, d) => (zreg a, zreg b, zreg c, zreg d)
  halfZ qs 16 12 ++ halfZ qs 8 7

theorem quarters_eq (ws : List (Nat × Nat × Nat × Nat)) :
    quarters ws = (quartersZ ws).map ZI.instr := by
  simp only [quarters, quartersZ, half_eq, List.map_append]

/-! ## The rounds on one block

The words after a round are terms in the words before it (`E`), computed by
the kernel for the code and for the specification and compared. -/

/-- A term in the words `var k` of a state. -/
inductive E
  | var (k : Nat) | add (a b : E) | xor (a b : E) | rol (a : E) (n : Nat)
  deriving DecidableEq

def E.eval (v : CState) : E → Word
  | .var k => if h : k < 16 then v[k] else 0
  | .add a b => a.eval v + b.eval v
  | .xor a b => a.eval v ^^^ b.eval v
  | .rol a n => (a.eval v).rotateLeft n

/-- A state of terms. -/
abbrev ES := Nat → E

def ES.set (f : ES) (i : Nat) (x : E) : ES := fun k => if k = i then x else f k

/-- `zstep` on terms. -/
def zstepE (f : ES) : ZI → ES
  | .add d a b => f.set (xidx d) (.add (f (xidx a)) (f (xidx b)))
  | .xor d a b => f.set (xidx d) (.xor (f (xidx a)) (f (xidx b)))
  | .rol d a n => f.set (xidx d) (.rol (f (xidx a)) (n.toNat % 32))

/-- `qround` on terms. -/
def qroundE (f : ES) (x y z w : Fin 16) : ES :=
  let a := E.add (f x) (f y); let d := E.rol (.xor (f w) a) 16
  let c := E.add (f z) d; let b := E.rol (.xor (f y) c) 12
  let a := E.add a b; let d := E.rol (.xor d a) 8
  let c := E.add c d; let b := E.rol (.xor b c) 7
  (((f.set x a).set y b).set z c).set w d

/-- The terms `f` evaluate to `v`, in the words of `v₀`. -/
def Rel (v₀ : CState) (f : ES) (v : CState) : Prop := ∀ k (hk : k < 16), (f k).eval v₀ = v[k]

theorem Rel.set {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) {i : Nat} (hi : i < 16) {x : E}
    {y : Word} (hx : x.eval v₀ = y) : Rel v₀ (f.set i x) (v.set i y hi) := by
  intro k hk
  simp only [ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem Rel.step {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (i : ZI) :
    Rel v₀ (zstepE f i) (zstep v i) := by
  cases i with
  | add d a b => exact h.set (xidx_lt d) (by simp only [E.eval, h _ (xidx_lt a), h _ (xidx_lt b)])
  | xor d a b => exact h.set (xidx_lt d) (by simp only [E.eval, h _ (xidx_lt a), h _ (xidx_lt b)])
  | rol d a n => exact h.set (xidx_lt d) (by simp only [E.eval, h _ (xidx_lt a)])

theorem Rel.foldl {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) :
    ∀ is : List ZI, Rel v₀ (is.foldl zstepE f) (is.foldl zstep v)
  | [] => h
  | i :: is => (h.step i).foldl is

theorem Rel.qround {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (x y z w : Fin 16) :
    Rel v₀ (qroundE f x y z w) (qround v x y z w) := by
  simp only [qroundE]
  refine (((h.set x.2 ?_).set y.2 ?_).set z.2 ?_).set w.2 ?_ <;>
    simp only [E.eval, h _ x.2, h _ y.2, h _ z.2, h _ w.2, Fin.getElem_fin]

/-- The words of a state, as terms. -/
def vars : ES := .var

theorem rel_vars (v : CState) : Rel v vars v := fun k hk => by simp [vars, E.eval, hk]

theorem Rel.eq {v₀ : CState} {f : ES} {v v' : CState} (h : Rel v₀ f v) (h' : Rel v₀ f v') : v = v' :=
  Vector.ext fun k hk => (h k hk).symm.trans (h' k hk)

/-- Two states of terms agree on the words of a state. -/
def ES.eq16 (f g : ES) : Bool := (List.range 16).all fun k => f k == g k

theorem Rel.of_eq16 {v₀ : CState} {f g : ES} {v : CState} (h : Rel v₀ f v) (e : ES.eq16 f g = true) :
    Rel v₀ g v := by
  intro k hk
  simp only [ES.eq16, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e k hk]; exact h k hk

def cols : List (Nat × Nat × Nat × Nat) := [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
def diags : List (Nat × Nat × Nat × Nat) := [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

theorem cols_eq (v : CState) :
    (quartersZ cols).foldl zstep v =
      qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 := by
  have e : ES.eq16 ((quartersZ cols).foldl zstepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 4 8 12).qround 1 5 9 13 |>.qround 2 6 10 14).qround 3 7 11 15)

theorem diags_eq (v : CState) :
    (quartersZ diags).foldl zstep v =
      qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := by
  have e : ES.eq16 ((quartersZ diags).foldl zstepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 5 10 15).qround 1 6 11 12 |>.qround 2 7 8 13).qround 3 4 9 14)

theorem innerBlock_eq (v : CState) : (quartersZ cols ++ quartersZ diags).foldl zstep v = innerBlock v := by
  rw [List.foldl_append, cols_eq, diags_eq]; rfl

theorem doubleRound_eq : doubleRound = (quartersZ cols ++ quartersZ diags).map ZI.instr := by
  simp only [doubleRound, quarters_eq, List.map_append, cols, diags]

/-! ## The rounds on the sixteen blocks -/

theorem Same.trans {s₀ s₁ s₂ : State} (h₁ : Same s₀ s₁) (h₂ : Same s₁ s₂) : Same s₀ s₂ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : ZH vs s) :
    WP isa (.block doubleRound) s fun s' => ZH (fun j => innerBlock (vs j)) s' ∧ Same s s' := by
  have e : (fun j => (quartersZ cols ++ quartersZ diags).foldl zstep (vs j)) = fun j => innerBlock (vs j) :=
    funext fun j => innerBlock_eq (vs j)
  rw [doubleRound_eq]
  exact WP.mono (block_ok _ h) fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

theorem rounds_ok {vs : Nat → CState} {s₀ : State} (h : ZH vs s₀) :
    ∀ n, WP isa (rounds n) s₀ fun s => ZH (fun j => Nat.repeat innerBlock n (vs j)) s ∧ Same s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ ⟨h₁, hs⟩ =>
      WP.mono (doubleRound_ok h₁) fun _ ⟨h₂, hs'⟩ => ⟨h₂, hs.trans hs'⟩)

end VG.Proof.ChaCha20.X86_64.Avx512
