import VerifiedGarbage.Proof.Poly1305.X86.Common

/-!
# Poly1305 on x86 (32-bit): saving registers and clamping the key

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- The state's words on entry. -/
def words (m : Mem) (st : BitVec 32) : Nat → Nat := fun k => wv m st (4 * k)

theorem words_ok (m : Mem) (st : BitVec 32) : Words m st (words m st) := fun _ _ => rfl

theorem save_eq : save = [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax 116) .ebx,
    .store (at_ .eax 120) .esi, .store (at_ .eax 124) .edi, .store (at_ .eax 20) .ebp,
    .mov .edi (.reg .eax)] := rfl

/-- The callee-saved registers of `s`, saved in the words `f`. -/
def SavedIn (s : State) (f : Nat → Nat) : Prop :=
  f 29 = v s .ebx ∧ f 30 = v s .esi ∧ f 31 = v s .edi ∧ f 5 = v s .ebp

/-- The state at `[esp + 4]` into `edi`, saving `ebx, esi, edi, ebp` in it. -/
theorem save_ok {s : State} {st : BitVec 32} (hst : s.mem.readW (addr (s.gpr .esp) 4) 32 = st)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : sR st ∈ s.wr) :
    WP isa (.block save) s fun s' => ∃ f, After st s s' f [.eax, .edi] ∧ s'.gpr .edi = st ∧
      (∀ k, k < 29 → k ≠ 5 → f k = words s.mem st k) ∧ SavedIn s f := by
  have hc : ∀ d, d + 4 ≤ 128 → InRegions s.wr (addr st d) 4 := fun d hd =>
    ⟨_, hw, sR_contains hfit hd (by omega)⟩
  rw [save_eq]
  refine wp_movm (a := addr (s.gpr .esp) 4) (ea_at _ _ _) harg fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hst]
  refine wp_store (a := addr st (4 * 29)) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact hc _ (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr st (4 * 30)) (by rw [ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₃ u₃ => ?_
  refine wp_store (a := addr st (4 * 31)) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr st (4 * 5)) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ _ => WP.block_nil ⟨upd (upd (upd (upd (words s.mem st) 29 (v s .ebx)) 30
    (v s .esi)) 31 (v s .edi)) 5 (v s .ebp), ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, fun k hk hk5 => ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    exact ((((words_ok s.mem st).write hfit (j := 29) (by omega) _).write hfit (j := 30) (by omega)
      _).write hfit (j := 31) (by omega) _).write hfit (j := 5) (by omega) _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (frame_write (frame_write (frame_write (Frame.refl _ _) hfit (by omega) _) hfit
      (by omega) _) hfit (by omega) _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, e₁]
  · simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) only [upd, ite_true, ite_false]


theorem and0_toNat (x : BitVec 32) : (x &&& 0x0fffffff).toNat = x.toNat &&& 0x0fffffff := by
  rw [BitVec.toNat_and]; rfl

theorem and1_toNat (x : BitVec 32) : (x &&& 0x0ffffffc).toNat = x.toNat &&& 0x0ffffffc := by
  rw [BitVec.toNat_and]; rfl

/-- `r0` clamped. -/
theorem clamp0_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat} (hw : Words s.mem st f) :
    WP isa (.block clamp0) s fun s' => After st s s' (upd f 18 (f 6 &&& 0x0fffffff)) [.eax] := by
  have hfit := hc.fit
  refine wp_movm (a := addr st (4 * 6)) (by rw [ea_at, hc.edi]) (hc.inRW (by omega) (by omega))
    fun s₁ u₁ _ => wp_andx (readSrc_imm _ _) fun s₂ u₂ => ?_
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other .edi (by decide), u₁.other .edi (by decide), hc.edi]
  refine wp_store (a := addr st (4 * 18)) (by rw [ea_at, edi₂]; rfl)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
    refine (hw.write hfit (by omega) _).congr fun k _ => ?_
    simp only [upd]
    split
    · rw [and0_toNat, hw.readW (k := 6) (by omega)]
    · rfl
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_singleton] at hr; rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
theorem clampS_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat} (hw : Words s.mem st f)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block (clampS j)) s fun s' => After st s s' (upd (upd f (18 + j) (f (6 + j) &&& 0x0ffffffc))
      (21 + j) ((f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4)) [.eax, .ecx] := by
  have hfit := hc.fit
  have hr : f (6 + j) &&& 0x0ffffffc < 2 ^ 28 := mask1_lt _
  refine wp_movm (a := addr st (4 * (6 + j))) (by rw [ea_at, hc.edi]; congr 1; omega)
    (hc.inRW (by omega) (by omega)) fun s₁ u₁ _ => wp_andx (readSrc_imm _ _) fun s₂ u₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = f (6 + j) &&& 0x0ffffffc := by
    rw [u₂.gpr, u₁.gpr, and1_toNat, hw.readW (k := 6 + j) (by omega)]
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  refine wp_store (a := addr st (4 * (18 + j))) (by rw [ea_at, edi₂]; simp only [rOff]; congr 1; omega)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ _ => wp_shr (by omega) fun s₅ u₅ => wp_addx (readSrc_reg _ _) fun s₆ u₆ _ => ?_
  have e₆ : (s₆.gpr .eax).toNat = (f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4 := by
    rw [u₆.gpr, u₅.other .eax (by decide), u₅.gpr, u₄.gpr, u₄.other .eax (by decide), u₃.gpr,
      BitVec.toNat_add, shr2_toNat, e₂]
    omega
  have edi₆ : s₆.gpr .edi = st := by
    rw [u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.other .edi (by decide), u₃.gpr, edi₂]
  refine wp_store (a := addr st (4 * (21 + j))) (by rw [ea_at, edi₆]; simp only [sOff]; congr 1; omega)
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ((hw.write hfit (j := 18 + j) (by omega) _).write hfit (j := 21 + j) (by omega) _).congr
      fun k _ => ?_
    rw [e₂, e₆]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (frame_write (Frame.refl _ _) hfit (by omega) _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.1, u₅.other r hr.2, u₄.other r hr.2, u₃.gpr, u₂.other r hr.1,
      u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]


theorem setup_eq : setup = save ++ (clamp0 ++ (clampS 1 ++ (clampS 2 ++ clampS 3))) := by
  simp only [setup, List.append_assoc]

section
variable (m : Mem) (st : BitVec 32)
/-- The clamped `r0`, and `rj = 4 qj`, of the key in the state's words. -/
def r0v : Nat := words m st 6 &&& 0x0fffffff
def qv (j : Nat) : Nat := (words m st (6 + j) &&& 0x0ffffffc) / 4
end

theorem coef_facts {x : Nat} : x &&& 0x0ffffffc = 4 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) + (x &&& 0x0ffffffc) / 4 = 5 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) / 4 < 2 ^ 26 := by
  have h1 := mask1_mod x; have h2 := mask1_lt x
  refine ⟨by omega, by omega, by omega⟩

/-- Everything each function but `init` does first: the state at `[esp + 4]`
into `edi`, the callee-saved registers saved in it, and the clamped `r`
and `sj` in its words. -/
theorem setup_ok {s₀ : State} {st : BitVec 32} (hst : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = st)
    (harg : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : sR st ∈ s₀.wr) :
    WP isa (.block setup) s₀ fun s => ∃ F, After st s₀ s F [.eax, .ecx, .edi] ∧ Ctx st s ∧
      (∀ k, (k < 18 ∧ k ≠ 5) ∨ (25 ≤ k ∧ k < 29) → F k = words s₀.mem st k) ∧ SavedIn s₀ F ∧
      Coefs F (r0v s₀.mem st) (qv s₀.mem st 1) (qv s₀.mem st 2) (qv s₀.mem st 3) := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (save_ok hst harg hfit hw) fun s₁ ⟨f₁, A₁, e₁, h₁, sv₁⟩ => ?_)
  have c₁ : Ctx st s₁ := ⟨e₁, hfit, A₁.wr ▸ hw⟩
  refine WP.block_append (WP.mono (clamp0_ok c₁ A₁.words) fun s₂ A₂ => ?_)
  have c₂ := A₂.ctx c₁
  refine WP.block_append (WP.mono (clampS_ok c₂ A₂.words (j := 1) (by omega)) fun s₃ A₃ => ?_)
  have c₃ := A₃.ctx c₂
  refine WP.block_append (WP.mono (clampS_ok c₃ A₃.words (j := 2) (by omega)) fun s₄ A₄ => ?_)
  have c₄ := A₄.ctx c₃
  refine WP.mono (clampS_ok c₄ A₄.words (j := 3) (by omega)) fun s₅ A₅ =>
    ⟨_, (A₁.trans (A₂.trans (A₃.trans (A₄.trans A₅)))).mono, A₅.ctx c₄, fun k hk => ?_, ?_, ?_⟩
  · simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), h₁ k (by omega) (by omega)]
  · obtain ⟨b1, b2, b3, b4⟩ := sv₁
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) only [upd, ite_false] <;>
      assumption
  · have w6 : f₁ 6 = words s₀.mem st 6 := h₁ 6 (by omega) (by omega)
    have w7 : f₁ 7 = words s₀.mem st 7 := h₁ 7 (by omega) (by omega)
    have w8 : f₁ 8 = words s₀.mem st 8 := h₁ 8 (by omega) (by omega)
    have w9 : f₁ 9 = words s₀.mem st 9 := h₁ 9 (by omega) (by omega)
    obtain ⟨a1, a2, a3⟩ := coef_facts (x := words s₀.mem st 7)
    obtain ⟨b1, b2, b3⟩ := coef_facts (x := words s₀.mem st 8)
    obtain ⟨d1, d2, d3⟩ := coef_facts (x := words s₀.mem st 9)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mask0_lt _, a3, b3, d3⟩ <;>
      simp (config := {decide := true}) only [upd, ite_true, ite_false, w6, w7, w8, w9, r0v, qv,
        Nat.reduceAdd]
    exacts [a1, b1, d1, a2, b2, d2]

end VG.Proof.Poly1305.X86
