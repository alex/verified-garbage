import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The Salsa20/8 Core on AArch64: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt.AArch64

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_x1 {k : Nat} (hk : k < 16) : wreg k ≠ .x1 := by
  have key : ∀ k, k < 16 → wreg k ≠ .x1 := by decide
  exact key k hk

/-- The registers that hold words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

/-! ## One line, on registers -/

/-- `a ^= R(b + c)` through `w1`, rotating right by `sh`. -/
theorem line_regs {a b c : Reg} (ha : a ≠ .x1) {sh : Nat} (hsh : sh < 32) (s : State) (va vb vc : Word)
    (hva : s.gpr a = va.setWidth 64) (hvb : s.gpr b = vb.setWidth 64)
    (hvc : s.gpr c = vc.setWidth 64) :
    WP isa (.block [.add .w .x1 b c, .ror .w .x1 .x1 sh, .logic .eor .w a a .x1]) s fun s' =>
      s'.gpr a = (va ^^^ (vb + vc).rotateRight sh).setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logic, exec_ror_w hsh, isa, State.read, State.write, Size.bits, hva, hvb, hvc, ha,
    ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h1 h2 => ?_, trivial⟩
  simp only [h1, h2, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop :=
  ∀ k (hk : k < 16), s.gpr (wreg k) = v[k].setWidth 64

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  have ne : ∀ {a b}, a < 16 → b < 16 → a ≠ b → wreg a ≠ wreg b := fun ha hb hab e =>
    hab (wreg_inj ha hb e)
  refine WP.mono (line_regs (wreg_ne_x1 hi) (show 32 - n < 32 by omega) s _ _ _ (h.holds i hi) (h.holds j hj)
    (h.holds k hk)) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw hx => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, rotateLeft_eq _ (by omega) (by omega)]
    · simp only [e, ite_false]
      rw [hr _ (ne hm' hi (Ne.symm e)) (wreg_ne_x1 hm')]
      exact h.holds m hm'
  · rw [hr r (fun e => hw ⟨i, hi, e⟩) hx]
    exact h.keep r hw hx

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.Scrypt.AArch64

/-!
# The Salsa20/8 Core on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`:
replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` and `scratch` (64 bytes each; the contents of
`scratch` on exit are unspecified), which may not overlap. The pointers are
public; the data is secret. -/
def salsaAArch64 : Contract AArch64.isa where
  pre s :=
    let b : Region := ⟨s.gpr .x0, 64⟩
    let scratch : Region := ⟨s.gpr .x1, 64⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch
  post s s' := bytesAt s'.mem (s.gpr .x0) 64 = salsa (bytesAt s.mem (s.gpr .x0) 64)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .x0
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

abbrev bR (p : Addr) : Region := ⟨p, 64⟩

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR (bp s₀), ⟨s₀.gpr .x1, 64⟩]

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR (bp s₀), by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR (bp s₀), by simp [hp.wr], contains_off (by omega) (by omega)⟩

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

theorem not_words_x0 : ¬ Words .x0 := fun ⟨k, hk, h⟩ => by
  have key : ∀ k, k < 16 → wreg k ≠ .x0 := by decide
  exact key k hk h.symm

theorem not_words_preserved {r : Reg} (hr : r ∈ preserved) : ¬ Words r ∧ r ≠ .x1 := by
  have key : ∀ r ∈ preserved, ∀ k, k < 16 → wreg k ≠ r := by decide
  refine ⟨fun ⟨k, hk, h⟩ => key r hr k hk h.symm, ?_⟩
  rintro rfl; simp [preserved] at hr

/-! ## Loading the input -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → s.gpr (wreg j) = (V s₀)[j].setWidth 64
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.ldr .w (wreg n) .x0 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hx0 : s.gpr .x0 = bp s₀ := h.keep _ not_words_x0
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [h.rd, h.wr, hx0]; exact hp.in_b hn _
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem, V_get _ hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_ldr_w (show 4 * n % 4 = 0 ∧ 4 * n < 16384 by omega) hin, isa,
    Option.some.injEq, exists_eq_left', hx0, hv]
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn e) (by omega)
      simp only [e, ite_false]; exact h.loaded j hj hjn
    · simp [Size.bits]
  · have e : r ≠ wreg n := fun e => hr ⟨n, hn, e⟩
    simp only [State.write, e, ite_false]; exact h.keep r hr

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums, the
others still hold the input, and words `i … 15` of the rounds' result `R` are
still in their registers. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + (V s₀)[j] else (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → s.gpr (wreg j) = R[j].setWidth 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) : WP isa (.block (finishWord i)) s (FI s₀ R (i + 1)) := by
  have hx0 : s.gpr .x0 = bp s₀ := h.keep _ not_words_x0 (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.rd, h.wr, hx0]; exact hp.in_b hi _
  have hout : InRegions s.wr (bp s₀ + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.wr]; exact hp.out_b hi
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * i)) 32 = (V s₀)[i] := by
    rw [h.out i hi, ite_neg' (Nat.lt_irrefl i)]
  have hr := h.rest i hi (Nat.le_refl i)
  have n1 : wreg i ≠ .x1 := wreg_ne_x1 hi
  have n0 : Reg.x0 ≠ wreg i := fun e => not_words_x0 ⟨i, hi, e⟩
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some,
    exec_ldr_w (show 4 * i % 4 = 0 ∧ 4 * i < 16384 by omega) hin, exec_add, isa, hx0, hv]
  simp (config := {decide := true}) only [State.write, State.read, Size.bits, n1, ite_false,
    hr, ite_true, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [exec_str_w (show 4 * i % 4 = 0 ∧ 4 * i < 16384 by omega)
    (by simpa [State.write, n0, n1, hx0] using hout)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left', ite_true, ite_false, hx0, n0, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  refine ⟨fun j hj => ?_, fun j hj hij => ?_, h.rd, h.wr, fun r hw hx => ?_⟩
  · by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_pos' (Nat.lt_succ_self j)]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_pos' hji, ite_pos' (by omega)]
      · rw [ite_neg' hji, ite_neg' (by omega)]
  · have e1 : wreg j ≠ wreg i := fun e => absurd (wreg_inj hj hi e) (by omega)
    have e2 : wreg j ≠ .x1 := wreg_ne_x1 hj
    simp only [e1, e2, ite_false]; exact h.rest j hj (by omega)
  · have e1 : r ≠ wreg i := fun e => hw ⟨i, hi, e⟩
    simp only [e1, hx, ite_false]; exact h.keep r hw hx

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Scrypt.salsaAArch64.post s₀ s' := by
  have hl₀ : LI s₀ 0 s₀ := ⟨fun _ _ h => absurd h (by omega), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₀ (LI s₀ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₀) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₀ hl₀
  refine WP.seq (WP.mono hload fun s₁ h₁ => ?_)
  have hh₁ : Holds (V s₀) s₁ := fun k hk => h₁.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₁ 4) fun s₂ h₂ => ?_)
  have hF₀ : FI s₀ (Rs s₀) 0 s₂ :=
    ⟨fun j hj => by rw [ite_neg' (Nat.not_lt_zero j), h₂.mem, h₁.mem, V_get _ hj],
      fun j hj _ => h₂.holds j hj, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
      fun r hw hx => (h₂.keep r hw hx).trans (h₁.keep r hw)⟩
  unfold finish
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ (Rs s₀)) (fun i s hi h => finish_step hp hi h)
    16 (Nat.le_refl _) s₂ hF₀) fun s' hF => ⟨fun r hr => ?_, ?_⟩
  · have ⟨hw, hx⟩ := not_words_preserved hr
    exact hF.keep r hw hx
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 =
      Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    exact post_of fun j hj => by rw [hF.out j hj, ite_pos' hj]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaAArch64.pre Proof.Scrypt.salsaAArch64.pub
    Impl.Scrypt.AArch64.salsa := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem salsa_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.salsa (Spec.Scrypt.salsaContract AArch64.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, Proof.Scrypt.salsaAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Scrypt.AArch64.satState] using
      Proof.Scrypt.AArch64.satState)

end VG.Proof.Scrypt.AArch64
