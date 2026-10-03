import VerifiedGarbage.Proof.MlKem.X86.TopSeq2
import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Impl.MlKem.X86.Kem

/-!
# ML-KEM on x86 (32-bit): the code of a parameter set

The code over the `k` rows, entries or polynomials is a sequence (`seqs`) of
one piece per index (`Piece.seqs`). A parameter set's functions that compress
to `d_u` and `d_v` bits and decompress from them (`KemLay.ceCode`,
`KemLay.ddCode`) are leaves of the contracts of `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` for widths that include `d_u` and `d_v` (`CeOK`),
so their calls are pieces (`ceK_piece`, `ddK_piece`).
-/

namespace VG.Proof.MlKem.X86.Top

open Lean Meta Elab Tactic in
/-- Proves `(Taint.check A τ c ?hint).isSome = true` with the hint `Taint.hintOf A τ c`, by the
kernel's evaluation of the check: for code that mentions the offsets of a parameter set that is not
given, which `taint_decide` cannot compute (it compiles the code), but whose analysis does not depend
on them. The goal is closed by `Eq.refl true` without the elaborator's check of it, whose heuristics
give up on some of these evaluations; the kernel checks it with the declaration (and rejects the
declaration if the check fails). -/
elab "taint_rfl" : tactic => do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_rfl: the goal is not an equation"
  unless rhs.isConstOf ``Bool.true do throwError "taint_rfl: the goal is not `… = true`"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "taint_rfl: the goal is not about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let h := args[4]!
  if h.isMVar then h.mvarId!.assign (mkApp4 (mkConst ``Taint.hintOf) args[0]! args[1]! args[2]! args[3]!)
  g.assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  replaceMainGoal []

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- `decide`, for a goal that mentions a parameter set that is not given but evaluates without it. -/
macro "rdecide" : tactic => `(tactic| exact of_decide_eq_true rfl)

/-- `f a`, …, `f (a + n - 1)`, then `c`, each from `P i` to `P (i + 1)`. -/
theorem _root_.VG.Proof.MlKem.X86.Piece.seqs {Pre : State → Prop} {Pub : State → State → Prop}
    {P : Nat → State → State → Prop} {f : Nat → Prog isa} {Q : State → State → Prop} {c : Prog isa} :
    ∀ (n a : Nat), (∀ i, a ≤ i → i < a + n → Piece Pre Pub (P i) (P (i + 1)) (f i)) →
      Piece Pre Pub (P (a + n)) Q c → Piece Pre Pub (P a) Q (seqs ((List.range' a n).map f) c)
  | 0, _, _, hc => hc
  | n + 1, a, h, hc => by
    rw [List.range'_succ, List.map_cons, Impl.MlKem.X86.seqs]
    exact .seq (h a (Nat.le_refl _) (by omega)) (Piece.seqs n (a + 1) (fun i h₁ h₂ => h i (by omega) (by omega))
      (by rw [show a + 1 + n = a + (n + 1) by omega]; exact hc))

/-- `f 0`, …, `f (n - 1)`, then `c`. -/
theorem _root_.VG.Proof.MlKem.X86.Piece.seqs0 {Pre : State → Prop} {Pub : State → State → Prop}
    {P : Nat → State → State → Prop} {f : Nat → Prog isa} {Q : State → State → Prop} {c : Prog isa} (n : Nat)
    (h : ∀ i < n, Piece Pre Pub (P i) (P (i + 1)) (f i)) (hc : Piece Pre Pub (P n) Q c) :
    Piece Pre Pub (P 0) Q (seqs ((List.range n).map f) c) := by
  rw [List.range_eq_range']
  exact Piece.seqs n 0 (fun i _ h₂ => h i (by omega)) (by rw [Nat.zero_add]; exact hc)

/-! ## Indices of a `k × k` matrix, row by row -/

theorem idx_mod {k i j : Nat} (hj : j < k) : (k * i + j) % k = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem idx_div {k i j : Nat} (hj : j < k) : (k * i + j) / k = i := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]

theorem idx_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

/-! ## Buffers of `k` parts -/

theorem catK_congr {f g : Nat → List Byte} : ∀ {k : Nat}, (∀ i < k, f i = g i) → KPke.catK f k = KPke.catK g k
  | 0, _ => rfl
  | 1, h => h 0 (by decide)
  | k + 2, h => by
    show KPke.catK f (k + 1) ++ f (k + 1) = KPke.catK g (k + 1) ++ g (k + 1)
    rw [catK_congr fun i hi => h i (by omega), h (k + 1) (by omega)]

/-- A part of a buffer within an argument is within it. -/
theorem Lay.ok_sub {Y : Lay} {a o l o' l' : Nat} (h : Y.ok ⟨a, o, l⟩ = true) (h₀ : 0 < l')
    (h₂ : o' + l' ≤ o + l) : Y.ok ⟨a, o', l'⟩ = true := by
  simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-- The bytes of `n` parts of `c` bytes each. -/
theorem bytes_catK {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o c : Nat} :
    ∀ {n : Nat}, Y.ok ⟨a, o, c * n⟩ = true →
      Spec.Sha3.bytesAt m (Buf.addr s₀ ⟨a, o, c * n⟩) (c * n) =
        KPke.catK (fun i => Spec.Sha3.bytesAt m (Buf.addr s₀ ⟨a, o + c * i, c⟩) c) n
  | 0, h => absurd h (by simp [Lay.ok])
  | 1, _ => by simp only [Nat.mul_one]; rfl
  | n + 2, h => by
    have hc : 0 < c := by
      simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Nat.pos_of_mul_pos_right h.1.2
    have e : c * (n + 2) = c * (n + 1) + c := Nat.mul_succ c (n + 1)
    rw [bytes_split hp m (o' := o + c * (n + 1)) (l₁ := c * (n + 1)) (l₂ := c) rfl e.symm
      (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _)) (by omega))
      (Lay.ok_sub h hc (by omega)),
      bytes_catK hp m (n := n + 1) (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _))
        (by omega))]
    rfl

/-- `copyW_piece`, for `l = 4n` bytes. -/
theorem copyW_piece' (sa so da dO n l : Nat) (hl : 4 * n = l) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : (Y.ok ⟨sa, so, l⟩ && Y.okW ⟨da, dO, l⟩ && Y.sep ⟨sa, so, l⟩ ⟨da, dO, l⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi ⟨sa, so, l⟩ ++
      ptrTo Y.sc .ebp ⟨da, dO, l⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, l⟩] s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, l⟩) l = Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨sa, so, l⟩) l →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, l⟩ ⟨da, dO, l⟩ n) := by
  subst hl
  exact copyW_piece sa so da dO n hn hn' hc t₁ t₂ hA hQ

/-- The parameter set's leaves compress to `d_u` and `d_v` bits, and decompress from them. -/
class CeOK (L : KemLay) : Prop where
  ce : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ CeFn L.ceCode ws
  dd : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ DdFn L.ddCode ws

instance : CeOK L768 := ⟨⟨_, by decide, by decide, ce768⟩, ⟨_, by decide, by decide, dd768⟩⟩

variable {L : KemLay} [CeOK L]

theorem ceK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ceK L Y.sc d ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.ce (L := L)
  exact ceC_piece F d (by rcases hd with rfl | rfl <;> assumption) fa fo oa oo hc hN tt hA hQ

theorem ddK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ddK L Y.sc d ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.dd (L := L)
  exact ddC_piece F d (by rcases hd with rfl | rfl <;> assumption) ba bo fa fo hc hN tt hA hQ

end VG.Proof.MlKem.X86.Top
