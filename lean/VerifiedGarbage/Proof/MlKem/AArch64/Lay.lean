import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.MlKem.AArch64.Kem
import Lean.Meta.Tactic.Delta

/-!
# ML-KEM on AArch64: the parameter sets of the top-level functions

The proofs of `keygen`, `encaps` and `decaps` are stated once for a
parameter set `P` (`KemLay`) that is well formed (`KemLay.Wf`): the facts
about `k`, the widths and the size of `scratch` that the buffers in
`scratch` need, each decided for ML-KEM-768 and ML-KEM-1024 on their
literals; and whose functions at the widths `d_u` and `d_v` meet their
contracts (`KemLay.Calls`). `lom` does the arithmetic on the offsets.

Their code runs steps one after another (`seqs`): `WPs` and `RelCTs` are
the weakest precondition and the constant time of such a list of steps, by
an invariant over the steps of a loop (`WPs.range`, `WPs.matrix`, `RelCTs.matrix`)
or over the products of a sum (`WPs.dot`).
-/

namespace VG.Impl.MlKem.AArch64.KemLay

open VG VG.AArch64 VG.Spec.MlKem

/-- The parameter set of FIPS 203 (`η₁ = η₂ = 2`). -/
def params (P : KemLay) : Params := { k := P.k, η₁ := 2, η₂ := 2, du := P.du, dv := P.dv }

/-- What the buffers in `scratch` need: `1 ≤ k ≤ 4`, widths of at most 11
bits, and room for the buffers of `KG` and `KEM` in `scratch` and below 32 KiB, and
`scratch` below 64 KiB. -/
structure Wf (P : KemLay) : Prop where
  facts : 1 ≤ P.k ∧ P.k ≤ 4 ∧ P.k * P.k ≤ 16 ∧ 1 ≤ P.du ∧ P.du ≤ 11 ∧ 1 ≤ P.dv ∧ P.dv ≤ 11 ∧
    P.du * P.k ≤ 44 ∧ 4128 + 1024 * (P.k * P.k) + 1024 * P.k + 3072 + 48 ≤ P.scl ∧
    4248 + 1024 * (P.k * P.k) + 1024 * P.k + 5120 + 32 * (P.du * P.k + P.dv) + 48 ≤ P.scl ∧
    4248 + 1024 * (P.k * P.k) + 1024 * P.k + 5120 + 32 * (P.du * P.k + P.dv) + 48 ≤ 32768 ∧
    P.scl < 65536

end VG.Impl.MlKem.AArch64.KemLay

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- The offsets of `KG` and `KEM` and the lengths of a `KemLay`. -/
def offsetNames : Array Lean.Name :=
  #[``KG.ST, ``KG.WK, ``KG.SB, ``KG.SG, ``KG.BK, ``KG.PB, ``KG.SS, ``KG.NS, ``KG.AH, ``KG.SH,
    ``KG.EP, ``KG.TP, ``KG.PP, ``KG.SV, ``KG.aOff, ``KG.sOff, ``KEM.ST, ``KEM.WK, ``KEM.SB,
    ``KEM.HB, ``KEM.MB, ``KEM.RB, ``KEM.KP, ``KEM.JB, ``KEM.PB, ``KEM.SS, ``KEM.NS, ``KEM.AH,
    ``KEM.YH, ``KEM.EP, ``KEM.TP, ``KEM.PP, ``KEM.TH, ``KEM.CB, ``KEM.SV, ``KEM.aOff,
    ``KEM.yOff, ``KemLay.ctLen, ``KemLay.ekLen, ``KemLay.dkLen]

open Lean Meta Elab Tactic in
/-- Unfolds the offsets (`offsetNames`) in the goal and every hypothesis.
Like `delta` (and unlike `simp only [KG.ST, …]`, which builds its lemmas
from the definitions at every call) it only replaces each constant by its
value. -/
elab "lom_unfold" : tactic => withMainContext do
  let p := (offsetNames.contains ·)
  let mut g ← getMainGoal
  for fv in (← getLCtx).getFVarIds do
    let d ← fv.getDecl
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← deltaExpand t p
    if t' != t then g ← g.replaceLocalDeclDefEq fv t'
  let t ← instantiateMVars (← g.getType)
  let t' ← deltaExpand t p
  if t' != t then g ← g.replaceTargetDefEq t'
  replaceMainGoal [g]

/-- Arithmetic on the offsets of a well-formed parameter set (`‹KemLay.Wf _›`
in the context) and the facts `hs`. -/
syntax "lom" ("[" term,* "]")? : tactic

macro_rules
  | `(tactic| lom) => `(tactic| (
      (try have := (‹KemLay.Wf _›).facts); clear_non_arith; lom_unfold; omega))
  | `(tactic| lom []) => `(tactic| lom)
  | `(tactic| lom [$h:term, $hs:term,*]) => `(tactic| (have := $h; lom [$hs,*]))
  | `(tactic| lom [$h:term]) => `(tactic| (have := $h; lom))

/-- Entry `k i + j` of a `k × k` matrix. -/
theorem ij_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

theorem ij_div {k i j : Nat} (hj : j < k) : (k * i + j) / k = i ∧ (k * i + j) % k = j := by
  have hk : 0 < k := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem div_lt {k e : Nat} (he : e < k * k) : e / k < k := Nat.div_lt_of_lt_mul he

theorem mod_lt {k e : Nat} (he : e < k * k) : e % k < k :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at he)

theorem div_add_mod' {k e : Nat} : k * (e / k) + e % k = e := Nat.div_add_mod e k

/-- `a i + a ≤ a k` for `i < k`. -/
theorem mul_succ_le {a i k : Nat} (hi : i < k) : a * i + a ≤ a * k := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-! ## Steps one after another -/

theorem map_range_ne_nil {α : Type} {k : Nat} (hk : 1 ≤ k) (f : Nat → α) : (List.range k).map f ≠ [] := by
  simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega

theorem matrix_ne_nil {α : Type} {k : Nat} (hk : 1 ≤ k) {g : Nat → Nat → α} :
    ((List.range k).flatMap fun i => (List.range k).map (g i)) ≠ [] := by
  intro h
  exact map_range_ne_nil hk (g 0) (List.flatMap_eq_nil_iff.mp h 0 (List.mem_range.mpr (by omega)))

/-- `WP` of running `cs` one after another. -/
def WPs : List (Prog isa) → State → (State → Prop) → Prop
  | [], s, Q => Q s
  | c :: cs, s, Q => WP isa c s fun s' => WPs cs s' Q

namespace WPs

theorem mono : ∀ {cs : List (Prog isa)} {s : State} {Q Q' : State → Prop}, WPs cs s Q →
    (∀ s, Q s → Q' s) → WPs cs s Q'
  | [], _, _, _, h, hq => hq _ h
  | _ :: _, _, _, _, h, hq => WP.mono h fun _ h' => mono h' hq

theorem seqs : ∀ {cs : List (Prog isa)} {s : State} {Q : State → Prop}, cs ≠ [] → WPs cs s Q →
    WP isa (Impl.MlKem.AArch64.seqs cs) s Q
  | [_], _, _, _, h => WP.mono h fun _ h' => h'
  | _ :: _ :: _, _, _, _, h => WP.seq (WP.mono h fun _ h' => seqs (List.cons_ne_nil _ _) h')

theorem append : ∀ {l₁ l₂ : List (Prog isa)} {s : State} {Q : State → Prop},
    WPs l₁ s (fun s' => WPs l₂ s' Q) → WPs (l₁ ++ l₂) s Q
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => WP.mono h fun _ h' => append h'

theorem cons {c : Prog isa} {cs : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => WPs cs s' Q) : WPs (c :: cs) s Q := h

theorem single {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) : WPs [c] s Q :=
  WP.mono h fun _ h' => h'

/-- A loop over `i < n`, by an invariant `I i` before step `i`. -/
theorem range {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, ∀ s, I i s → WP isa (f i) s (I (i + 1))) →
      ∀ {s : State}, I 0 s → WPs ((List.range n).map f) s (I n)
  | 0, _, _, h => h
  | n + 1, hf, _, h => by
    rw [List.range_succ, List.map_append]
    exact append (mono (range (fun i hi => hf i (by omega)) h) fun s' h' =>
      single (hf n (by omega) s' h'))

/-- The `k²` steps of a matrix, row by row, by an invariant `I e` before
entry `e = k i + j`. -/
theorem matrix {k : Nat} {g : Nat → Nat → Prog isa} {I : Nat → State → Prop}
    (hg : ∀ i < k, ∀ j < k, ∀ s, I (k * i + j) s → WP isa (g i j) s (I (k * i + j + 1))) :
    ∀ {n : Nat}, n ≤ k → ∀ {s : State}, I 0 s →
      WPs ((List.range n).flatMap fun i => (List.range k).map (g i)) s (I (k * n))
  | 0, _, _, h => h
  | n + 1, hn, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine append (mono (matrix hg (by omega) h) fun s' h' => ?_)
    have r := range (f := g n) (I := fun j => I (k * n + j)) (n := k)
      (fun j hj s hs => hg n (by omega) j hj s hs) h'
    rwa [← Nat.mul_succ] at r

/-- A sum of `n` products into `tp` (`T`), each other one first into `pp`
(`Q`), by an invariant `E`: after the steps, `tp` holds `v 0 + ⋯ + v (n - 1)`. -/
theorem dot {tp pp : Nat} {term : Nat → Nat → List (Prog isa)} {E : State → Prop}
    {T Q : State → Spec.MlKem.Poly → Prop} {v : Nat → Spec.MlKem.Poly} {N : Nat}
    (h0 : ∀ s, E s → WPs (term 0 tp) s fun s' => E s' ∧ T s' (v 0))
    (hj : ∀ j, 1 ≤ j → j < N → ∀ s a, E s → T s a →
      WPs (term j pp) s fun s' => E s' ∧ T s' a ∧ Q s' (v j))
    (hadd : ∀ s a b, E s → T s a → Q s b →
      WP isa (addAt tp pp) s fun s' => E s' ∧ T s' (Spec.MlKem.add a b)) :
    ∀ {n : Nat}, 1 ≤ n → n ≤ N → ∀ {s : State}, E s →
      WPs (dotSteps tp pp term n) s fun s' => E s' ∧ T s' (KPke.foldK Spec.MlKem.add Spec.MlKem.zero v n)
  | 1, _, _, _, h => h0 _ h
  | n + 2, _, hn, _, h => by
    rw [dotSteps, List.append_assoc]
    refine append (mono (dot h0 hj hadd (n := n + 1) (by omega) (by omega) h) fun s₁ ⟨e₁, t₁⟩ => ?_)
    refine append (mono (hj (n + 1) (by omega) (by omega) s₁ _ e₁ t₁) fun s₂ ⟨e₂, t₂, q₂⟩ => ?_)
    exact single (hadd s₂ _ _ e₂ t₂ q₂)

end WPs

/-- Constant time of running `cs` one after another, through relations
between the steps. -/
def RelCTs : (State → State → Prop) → List (Prog isa) → (State → State → Prop) → Prop
  | P, [], Q => ∀ s₁ s₂, P s₁ s₂ → Q s₁ s₂
  | P, c :: cs, Q => ∃ R, RelCT isa P c R ∧ RelCTs R cs Q

namespace RelCTs

theorem seqs : ∀ {cs : List (Prog isa)} {P Q : State → State → Prop}, cs ≠ [] → RelCTs P cs Q →
    RelCT isa P (Impl.MlKem.AArch64.seqs cs) Q
  | [_], _, _, _, ⟨_, h, hq⟩ => RelCT.mono h (fun _ _ h => h) hq
  | _ :: _ :: _, _, _, _, ⟨_, h, hr⟩ => RelCT.seq h (seqs (List.cons_ne_nil _ _) hr)

theorem append : ∀ {l₁ l₂ : List (Prog isa)} {P R Q : State → State → Prop},
    RelCTs P l₁ R → RelCTs R l₂ Q → RelCTs P (l₁ ++ l₂) Q
  | [], [], _, _, _, h₁, h₂ => fun _ _ h => h₂ _ _ (h₁ _ _ h)
  | [], _ :: _, _, _, _, h₁, ⟨R', h, hr⟩ => ⟨R', RelCT.mono h h₁ fun _ _ h => h, hr⟩
  | _ :: _, _, _, _, _, ⟨R', h, hr⟩, h₂ => ⟨R', h, append hr h₂⟩

theorem range {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, RelCT isa (I i) (f i) (I (i + 1))) → RelCTs (I 0) ((List.range n).map f) (I n)
  | 0, _ => fun _ _ h => h
  | n + 1, hf => by
    rw [List.range_succ, List.map_append]
    exact append (range fun i hi => hf i (by omega)) ⟨_, hf n (by omega), fun _ _ h => h⟩

theorem matrix {k : Nat} {g : Nat → Nat → Prog isa} {I : Nat → State → State → Prop}
    (hg : ∀ i < k, ∀ j < k, RelCT isa (I (k * i + j)) (g i j) (I (k * i + j + 1))) :
    ∀ {n : Nat}, n ≤ k → RelCTs (I 0) ((List.range n).flatMap fun i => (List.range k).map (g i)) (I (k * n))
  | 0, _ => fun _ _ h => h
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have r := range (f := g n) (I := fun j => I (k * n + j)) (n := k) fun j hj => hg n (by omega) j hj
    rw [Nat.add_zero, ← Nat.mul_succ] at r
    exact append (matrix hg (by omega)) r

end RelCTs

end VG.Proof.MlKem.AArch64
