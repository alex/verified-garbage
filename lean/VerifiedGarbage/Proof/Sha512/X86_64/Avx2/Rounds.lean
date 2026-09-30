import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Impl.Sha512.X86_64.Avx2
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit

/-!
# SHA-512 with AVX2 on x86-64: one round

Untrusted: everything here is checked by Lean. `round j t` computes
`roundKW`, with `Σ₀` and `Σ₁` as three `rorx`, `Ch` as a sum of two
disjoint masks and `Maj` from the previous round's `a ⊕ b`.
-/

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` is in `carry t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7] ∧ s.gpr (carry t) = v[1] ^^^ v[2]

/-- The registers that hold pointers and the count, and `rsp`: never written
by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, carry t, carry (t + 1), T,
      .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  have e : carry (t + 1) = if t % 2 = 0 then .r14 else .r13 := by
    simp only [carry]; split <;> split <;> first | rfl | omega
  rw [e]
  simp only [var, carry]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega)
  rw [show t % 2 = t % 8 % 2 by omega]
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

theorem ch_add (e f g : Word) : ch e f g = (e &&& f) + (~~~e &&& g) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi
    simp only [ch, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_carry (a b c : Word) : maj a b c = (b ^^^ c) &&& (a ^^^ b) ^^^ b := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

theorem bsig0_rorx (x : Word) : bsig0 x = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39 := rfl
theorem bsig1_rorx (x : Word) : bsig1 x = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41 := rfl

/-- `T₁` in the order the round adds it up. -/
theorem t1_order (h e f g k w : Word) :
    h + k + w + ((e &&& f) + (~~~e &&& g)) +
        (e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) =
      h + bsig1 e + ch e f g + k + w := by
  rw [ch_add, bsig1_rorx]; ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the others). -/
theorem round_ok (j t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hin : InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8)
    (hw : s.mem.readW (s.ea (wSlot j t)) 64 = w) :
    WP isa (.block (round j t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hc⟩ := hv
  have ea : s.ea (wSlot j t) =
      s.gpr .rcx + BitVec.ofInt 64 ((32 * (t / 2) + 16 * j + 8 * (t % 2) : Nat) : Int) := rfl
  rw [ea] at hin hw
  apply WP.of_runBlock
  simp only [Impl.Sha512.X86_64.Avx2.round, wSlot, at_]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  generalize carry t = x at *
  generalize carry (t + 1) = y at *
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execRorx, execAndn, readSrc, State.ea,
    isa, State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags,
    RegUpd.ymmHi_setFlags, ite_true, ite_false,
    hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hc, hin, hw, and_self, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  rotate_left
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hd']
  · simp only [roundKW, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, maj_carry, bsig0_rorx, t1_order, and_self]
    exact ⟨BitVec.add_assoc _ _ _, trivial⟩

/-! ## Rounds of a block -/

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- Round `t` of block `j` can read `Wₜ` of `M`. -/
def WOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8 ∧ s.mem.readW (s.ea (wSlot j t)) 64 = W M t

theorem WOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : WOk j M s t) (hk : Keeps s s') :
    WOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hk.2.2.2.1 .rcx (by decide)]
  rw [WOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem round_step (j t : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : Vars t s (Spec.Sha512.rounds H M t)) (hw : WOk j M s t) :
    WP isa (.block (round j t)) s fun s' => Vars (t + 1) s' (Spec.Sha512.rounds H M (t + 1)) ∧ Keeps s s' := by
  rw [rounds_succ, round_eq]
  exact round_ok j t s _ _ hv hw.1 hw.2

theorem rounds2_step (j n : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : Vars (2 * n) s (Spec.Sha512.rounds H M (2 * n))) (hw : ∀ q < 2, WOk j M s (2 * n + q)) :
    WP isa (.block (round j (2 * n) ++ round j (2 * n + 1))) s
      fun s' => Vars (2 * n + 2) s' (Spec.Sha512.rounds H M (2 * n + 2)) ∧ Keeps s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (round_step j _ H M s hv (hw 0 (by omega))) fun s₁ ⟨hv₁, hk₁⟩ => ?_
  refine WP.mono (round_step j _ H M s₁ hv₁ ((hw 1 (by omega)).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ => ?_
  exact ⟨hv₂, hk₁.trans hk₂⟩

/-- The rounds of the second block. -/
theorem rounds2_ok (H : HashValue) (M : Block) (s : State) (hv : Vars 0 s H)
    (hw : ∀ t < 80, WOk 1 M s t) :
    ∀ n ≤ 80, WP isa (rounds2 n) s fun s' => Vars n s' (Spec.Sha512.rounds H M n) ∧ Keeps s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨hv, Keeps.refl s⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hv₁, hk₁⟩ => ?_)
    exact WP.mono (round_step 1 n H M s₁ hv₁ ((hw n (by omega)).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ =>
      ⟨hv₂, hk₁.trans hk₂⟩

end VG.Proof.Sha512.X86_64.Avx2
