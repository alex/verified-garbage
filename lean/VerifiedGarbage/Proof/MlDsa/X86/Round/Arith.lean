import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on x86 (32-bit): what the rounding code computes

Untrusted: everything here is checked by Lean. Continuation-style rules for
the pieces of `Impl/MlDsa/X86/Round/Round.lean`: `condAdd` leaves
`condAddN r x k` (`condAdd_spec`), `hbRaw g` leaves `⌊(a + γ₂ - 1)/(2γ₂)⌋`
(`hbRaw_spec`, by `hbF_eq` of `Proof/MlDsa/Round/Decompose.lean`) and `hb g`
its remainder modulo `m` (`hb_spec`), each changing only the registers it
names (`Only`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq)
open VG.Proof.MlKem.X86 (Only wp_cons wp_mul execMul_eax execMul_other toNat_ofNat32 eq_ofNat_of_toNat)

theorem updOnly {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr⟩

theorem Fupd.only {s s' : State} (h : Fupd s s') (ds : List Reg) : Only ds s s' :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr⟩

theorem Only.gpr_of {ds : List Reg} {s s' : State} (h : Only ds s s') {r : Reg} (hr : r ∉ ds) :
    s'.gpr r = s.gpr r := h.gpr r hr

/-- Two `Only`s, as one over a list that contains both. -/
theorem Only.comp {ds es fs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃)
    (hd : ∀ r ∈ ds, r ∈ fs := by decide) (he : ∀ r ∈ es, r ∈ fs := by decide) : Only fs s₁ s₃ :=
  (h₁.trans h₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact hd r h
    · exact he r h

/-- `sub d, [b + o]`, and the flags. -/
theorem wp_subm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sub d, r`, and the carry. -/
theorem wp_subr {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `cmp d, [b + o]`: ZF is `d = [b + o]`. -/
theorem wp_cmpm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp [exec, execAlu, readSrc_mem hb hin]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

/-- `mul r` of values whose product is less than `2³²`: `eax` is the product. -/
theorem wp_mulSmall {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (hp : (s.gpr .eax).toNat * (s.gpr r).toNat < 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = (s.gpr .eax).toNat * (s.gpr r).toNat →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  wp_mul (k _ (VG.Proof.MlKem.X86.execMul_only r s) (by rw [execMul_eax, toNat_ofNat32 hp]))

/-! ## Conditional addition -/

/-- What `condAdd` computes: `r - x`, plus `k` if that borrows. -/
def condAddN (r x k : Nat) : Nat := if r < x then r + k - x else r - x

theorem condAdd_val (r x k : BitVec 32) (hx : x.toNat ≤ r.toNat + k.toNat) :
    (r - x + ((if decide (r.toNat < x.toNat) = true then BitVec.allOnes 32 else 0) &&& k)).toNat =
      condAddN r.toNat x.toNat k.toNat := by
  unfold condAddN
  have := r.isLt; have := x.isLt; have := k.isLt
  by_cases h : r.toNat < x.toNat
  · simp only [h, decide_true, ite_true, BitVec.allOnes_and, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  · have e : r - x + ((if decide (r.toNat < x.toNat) = true then BitVec.allOnes 32 else 0) &&& k) = r - x := by
      simp [h]
    rw [e, BitVec.toNat_sub, ite_eq_right h]
    omega

/-- `condAdd r x t k`, from `x` read as `X`: `r ← condAddN r X k`, changing only `r`, `t` and the
flags. -/
theorem condAdd_spec {r t : Reg} (hrt : r ≠ t) {x : Src} {k X : BitVec 32} {is : List Instr} {s : State}
    {P : State → Prop} (hx : readSrc s x = some X) (hX : X.toNat ≤ (s.gpr r).toNat + k.toNat)
    (c : ∀ s', Only [r, t] s s' → (s'.gpr r).toNat = condAddN (s.gpr r).toNat X.toNat k.toNat →
      WP isa (.block is) s' P) :
    WP isa (.block (condAdd r x t k ++ is)) s P := by
  have htr : t ≠ r := fun e => hrt e.symm
  rw [condAdd, List.cons_append]
  refine cons (s' := (arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
    (s.gpr r - X))).setReg r (s.gpr r - X)) (by simp only [exec, execAlu, hx, Option.bind_some]) ?_
  have u₁ := Upd.flags s r (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X (s.gpr r - X))
    (s.gpr r - X)
  have c₁ : ((arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
      (s.gpr r - X))).setReg r (s.gpr r - X)).cf = some (decide ((s.gpr r).toNat < X.toNat)) := rfl
  generalize (arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
    (s.gpr r - X))).setReg r (s.gpr r - X) = s₁ at u₁ c₁ ⊢
  refine wp_sbb_self c₁ fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_add fun s₄ u₄ _ => c s₄ ?_ ?_
  · refine ⟨fun y hy => ?_, u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem)),
      u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd)), u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [u₄.other y hy.1, u₃.other y hy.2, u₂.other y hy.2, u₁.other y hy.1]
  · rw [u₄.gpr, u₃.other r hrt, u₃.gpr, u₂.gpr, u₂.other r hrt, u₁.gpr]
    exact condAdd_val _ _ _ hX

/-! ## `Decompose` -/

theorem dMul_eq (g : Nat) : dMul g = Proof.MlDsa.Round.hbMul g := rfl
theorem dAdd_eq (g : Nat) : dAdd g = Proof.MlDsa.Round.hbAdd g := rfl
theorem dShift_eq (g : Nat) : dShift g = Proof.MlDsa.Round.hbShift g := rfl

theorem dMod_eq {g : Nat} (h : g ∈ gamma2s) : dMod g = hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

theorem dShift_range (g : Nat) : 1 ≤ dShift g ∧ dShift g ≤ 31 := by unfold dShift; split <;> decide

theorem ofNat_small {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := toNat_ofNat32 h

/-- `hbRaw g` leaves `hbF g a` in `eax` from `a < q` there, changing only `eax`, `edx` and the flags. -/
theorem hbRaw_spec {g : Nat} (hg : g ∈ gamma2s) {is : List Instr} {s : State} {P : State → Prop} {a : Nat}
    (ha : (s.gpr .eax).toNat = a) (haq : a < q)
    (c : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = hbF g a → WP isa (.block is) s' P) :
    WP isa (.block (hbRaw g ++ is)) s P := by
  rw [q_eq] at haq
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  simp only [hbRaw, List.cons_append, List.nil_append]
  refine wp_addi fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ _ => wp_movi fun s₃ u₃ => ?_
  have e₁ : (s₁.gpr .eax).toNat = a + 127 := by
    rw [u₁.gpr, BitVec.toNat_add, ha]; simp; omega
  have e₂ : (s₂.gpr .eax).toNat = (a + 127) / 128 := by
    rw [u₂.gpr, BitVec.toNat_ushiftRight, e₁, Nat.shiftRight_eq_div_pow]
  have e₃ : (s₃.gpr .eax).toNat = (a + 127) / 128 := by rw [u₃.other _ (by decide), e₂]
  have m₃ : (s₃.gpr .edx).toNat = dMul g := by rw [u₃.gpr]; exact ofNat_small (by omega)
  have hp : (a + 127) / 128 * dMul g ≤ 65473 * 11275 := Nat.mul_le_mul (by omega) hM
  refine wp_mulSmall (by rw [e₃, m₃]; omega) fun s₄ o₄ v₄ => wp_addi fun s₅ u₅ =>
    wp_shr (dShift_range g) fun s₆ u₆ _ => c s₆ ?_ ?_
  · refine ((((updOnly u₁ |>.trans (updOnly u₂)).trans (updOnly u₃)).trans o₄).trans
      ((updOnly u₅).trans (updOnly u₆))).mono ?_
    intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (((h | h) | h) | h | h) | h | h <;> simp [h]
  · rw [u₆.gpr, BitVec.toNat_ushiftRight, u₅.gpr, BitVec.toNat_add, v₄, e₃, m₃, ofNat_small (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, hbF_eq hg (by rw [q_eq]; exact haq), dMul_eq,
      dAdd_eq, dShift_eq]

/-- `hb g` leaves `hbF g a % hbM g` (the `r₁` of `Decompose(a)`) in `eax` from `a < q` there,
changing only `eax`, `edx` and the flags. -/
theorem hb_spec {g : Nat} (hg : g ∈ gamma2s) {is : List Instr} {s : State} {P : State → Prop} {a : Nat}
    (ha : (s.gpr .eax).toNat = a) (haq : a < q)
    (c : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = hbF g a % hbM g → WP isa (.block is) s' P) :
    WP isa (.block (hb g ++ is)) s P := by
  rw [hb, List.append_assoc]
  refine hbRaw_spec hg ha haq fun s₁ o₁ v₁ => ?_
  have hf := hbF_le hg haq
  have hm : 16 ≤ hbM g ∧ hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hk : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by rw [dMod_eq hg]; exact ofNat_small (by omega)
  refine condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl (by rw [hk, v₁]; omega)
    fun s₂ o₂ v₂ => c s₂ ((o₁.trans o₂).mono fun r hr => ?_) ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h) <;> simp [h]
  · rw [v₂, v₁, hk]
    unfold condAddN
    split
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.MlDsa.X86.Round
