import VerifiedGarbage.Proof.Argon2.X86.Derive.Contract

/-!
# Argon2 on x86 (32-bit): the derivation's frames

`vg_argon2` pushes `ebp`, `edi`, `esi` and `ebx` in frames of their own and
then a frame of 144 bytes for the locals (`Impl.Argon2.X86.Derive.frames`).
`entry s₀` is the state its body starts in; `frames_ok` gives the
callee-saved registers and the return address back, from a body that keeps
`esp`, the saved words and the return address (`BodyDone`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Impl.Argon2.X86.Derive (frames saved body derive locals)

/-- The pushes of the saved registers and the locals. -/
def entry (s₀ : State) : State :=
  pushed (List.replicate 36 .eax) (pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))))

/-- The stack pointer of the body: below the four saved registers and the locals. -/
abbrev E (s₀ : State) : BitVec 32 := E0 s₀ - BitVec.ofNat 32 160

/-- The caller's registers, in the order of their words above the locals. -/
def savedVal (s₀ : State) : Nat → BitVec 32
  | 0 => s₀.gpr .ebx
  | 1 => s₀.gpr .esi
  | 2 => s₀.gpr .edi
  | _ => s₀.gpr .ebp

/-- The word `j` above the locals, where register `savedVal j` is. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).setWidth 64

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  esp : t.gpr .esp = E s₀
  saved : ∀ j < 4, t.mem.readW (slot s₀ j) 32 = savedVal s₀ j
  ret : t.mem.readW ((E0 s₀).setWidth 64) 32 = s₀.mem.readW ((E0 s₀).setWidth 64) 32

theorem popped_one_self (r : Reg) (s : State) (h : r ≠ .esp) :
    (popped r 1 s).gpr r = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  simp [popped, popReg, State.setReg, h]

section
variable {s₀ : State} (hlo : 160 ≤ (E0 s₀).toNat)
include hlo

theorem E_sub (k : Nat) (hk : k ≤ 160) :
    E s₀ + BitVec.ofNat 32 k = E0 s₀ - BitVec.ofNat 32 (160 - k) := by
  apply BitVec.eq_of_toNat_eq
  have := (E0 s₀).isLt
  rw [BitVec.toNat_add, sub_toNat hlo, sub_toNat (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem frames_ok {Q : State → Prop} (hsp : NoSp body)
    (hb : WP isa body (entry s₀) fun t => BodyDone s₀ t ∧ Q t)
    (hQ : ∀ t u, Q t → u.mem = t.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (E0 s₀).isLt
  have hlo' : 160 ≤ (s₀.gpr .esp).toNat := hlo
  have nf : ∀ {r : Reg} {k : Nat} {rs : List Reg} {b : Prog isa}, r ≠ .esp → NoSp b →
      NoSp (.frame (.push rs) b (.pop r k)) := fun {r k rs b} hr hb i hi => by
    simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | rfl
    · rfl
    · exact hb i hi
    · simp [Taint.clobbers, Taint.dst, hr]
  have e1 : ((pushed [.ebp] s₀).gpr .esp).toNat = (E0 s₀).toNat - 4 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega)]; rfl
  have e2 : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (E0 s₀).toNat - 8 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e1]; rfl
  have e3 : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat = (E0 s₀).toNat - 12 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e2]; rfl
  have e4 : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (E0 s₀).toNat - 16 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e3]; rfl
  simp only [derive, saved, frames]
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) (nf (by decide) (nf (by decide) hsp)))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) (nf (by decide) hsp))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) hsp)) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) hsp) ?_
  refine WP.frame (by simp [locals]) (by decide) (by decide)
    (by simp only [List.length_replicate, locals]; omega) hsp (hb.mono fun t ⟨d, q⟩ => ?_)
  -- The pops.
  have add4 : ∀ a : Nat, E s₀ + BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * 1) =
      E s₀ + BitVec.ofNat 32 (a + 4) := fun a => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  set t₁ := popped .eax (List.replicate (locals / 4) Reg.eax).length t with ht₁
  have sp₁ : t₁.gpr .esp = E s₀ + BitVec.ofNat 32 144 := by
    rw [ht₁, popped_esp, d.esp]; simp [locals]
  set t₂ := popped .ebx [Reg.ebx].length t₁ with ht₂
  have sp₂ : t₂.gpr .esp = E s₀ + BitVec.ofNat 32 148 := by
    rw [ht₂, popped_esp, sp₁]; exact add4 144
  set t₃ := popped .esi [Reg.esi].length t₂ with ht₃
  have sp₃ : t₃.gpr .esp = E s₀ + BitVec.ofNat 32 152 := by
    rw [ht₃, popped_esp, sp₂]; exact add4 148
  set t₄ := popped .edi [Reg.edi].length t₃ with ht₄
  have sp₄ : t₄.gpr .esp = E s₀ + BitVec.ofNat 32 156 := by
    rw [ht₄, popped_esp, sp₃]; exact add4 152
  set u := popped .ebp [Reg.ebp].length t₄ with hu
  have spu : u.gpr .esp = E0 s₀ := by
    rw [hu, popped_esp, sp₄, List.length_singleton, add4 156, E_sub hlo 160 (by decide)]; simp
  have mu : u.mem = t.mem := by simp [hu, ht₄, ht₃, ht₂, ht₁]
  have b₂ : t₂.gpr .ebx = s₀.gpr .ebx := by
    rw [ht₂, List.length_singleton, popped_one_self _ _ (by decide), sp₁, ht₁, popped_mem]
    exact d.saved 0 (by decide)
  have b₃ : t₃.gpr .esi = s₀.gpr .esi := by
    rw [ht₃, List.length_singleton, popped_one_self _ _ (by decide), sp₂, ht₂, popped_mem, ht₁,
      popped_mem]
    exact d.saved 1 (by decide)
  have b₄ : t₄.gpr .edi = s₀.gpr .edi := by
    rw [ht₄, List.length_singleton, popped_one_self _ _ (by decide), sp₃, ht₃, popped_mem, ht₂,
      popped_mem, ht₁, popped_mem]
    exact d.saved 2 (by decide)
  have b₅ : u.gpr .ebp = s₀.gpr .ebp := by
    rw [hu, List.length_singleton, popped_one_self _ _ (by decide), sp₄, ht₄, popped_mem, ht₃,
      popped_mem, ht₂, popped_mem, ht₁, popped_mem]
    exact d.saved 3 (by decide)
  refine ⟨⟨fun r hr => ?_, by rw [mu]; exact d.ret⟩, hQ t u q mu⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide), ht₄, popped_gpr _ _ _ (by decide) (by decide),
      ht₃, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₂
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide), ht₄, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₃
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₄
  · exact b₅
  · exact spu

end

end VG.Proof.Argon2.X86.Derive
