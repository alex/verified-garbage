import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits

/-!
# ML-DSA on x86 (32-bit): what `makeHint` and `useHint` compute per coefficient

The cores of the two loops (`Core2`), from the coefficients `a = [esi]` and `b =
[edi]`:

* `mhCore g`: `MakeHint(a, b)` as 0 or 1 (`mhV`): whether the `r₁` of `b`
  and of `b + a mod q` differ, from their xor `x < 64` as `(x + 63) >> 6`;
  it also adds it to `ecx`;
* `uhCore g`: `UseHint(a ≠ 0, b)` (`uhV`): `(f + m + δ) mod m`, with `δ` the
  masked `±1`.
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM hbF_le hbM_mul mem_gamma2s q_eq)
open VG.Proof.MlKem.X86 (Only wp_movm toNat_ofNat32 eq_ofNat_of_toNat)

/-- `core` leaves `V a b` in `eax` from `a = [esi]` (less than `q` if `reqA`) and `b = [edi] < q`,
changing only `eax`, `edx`, `ebx`, `ecx` and the flags, and adds it to `ecx` if `cnt`. -/
def Core2 (core : List Instr) (V : Nat → Nat → Nat) (reqA cnt : Bool) : Prop :=
  ∀ (is : List Instr) (s : State) (P : State → Prop) (a b : Nat), (reqA = true → a < q) → b < q →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 → (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 → (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    (∀ s', Only [.eax, .edx, .ebx, .ecx] s s' → (s'.gpr .eax).toNat = V a b →
      (cnt = true → s'.gpr .ecx = s.gpr .ecx + s'.gpr .eax) → WP isa (.block is) s' P) →
    WP isa (.block (core ++ is)) s P

/-- `MakeHint`, as 0 or 1. -/
def mhV (g a b : Nat) : Nat := if hbV g b = hbV g ((b + a) % q) then 0 else 1

theorem xor_shift {x y : Nat} (hx : x < 64) (hy : y < 64) : ((x ^^^ y) + 63) / 64 = if x = y then 0 else 1 := by
  have hl : x ^^^ y < 2 ^ 6 := Nat.xor_lt_two_pow (by omega) (by omega)
  by_cases e : x = y
  · subst e; rw [Nat.xor_self, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
    have : x ^^^ y ≠ 0 := fun h => e (Nat.eq_of_testBit_eq fun i => by
      have := congrArg (Nat.testBit · i) h
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases x.testBit i <;> cases y.testBit i <;> simp)
    omega

theorem hbV_lt64 {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : hbV g a < 64 := by
  have := Nat.mod_lt (hbF g a) (show hbM g > 0 by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have : hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold hbV; omega

theorem mhCore_eq (g : Nat) (is : List Instr) : mhCore g ++ is =
    .mov .eax (.mem (at_ .edi 0)) :: (hb g ++ (.mov .ebx (.reg .eax) :: .mov .eax (.mem (at_ .edi 0)) ::
      .alu .add .eax (.mem (at_ .esi 0)) :: (condAdd .eax (.imm qImm) .edx qImm ++ (hb g ++
      (.alu .xor .eax (.reg .ebx) :: .alu .add .eax (.imm 63) :: .shift .shr .eax 6 ::
        .alu .add .ecx (.reg .eax) :: is))))) := by
  simp only [mhCore, List.cons_append, List.nil_append, List.append_assoc]

theorem mhCore_spec {g : Nat} (hg : g ∈ gamma2s) : Core2 (mhCore g) (mhV g) true true := by
  intro is s P a b ha hb hia hva hib hvb c
  have ha := ha rfl
  have hq : q = 8380417 := rfl
  have hB : ∀ {s' : State} {B : BitVec 32}, s'.gpr .esi = B → s'.ea (at_ .esi 0) = addr B 0 :=
    fun h => by rw [State.ea, at_, h]; rfl
  rw [mhCore_eq]
  refine wp_movm hib (hb_spec hg (a := b) (by simp [State.setReg, hvb]) hb fun s₁ o₁ v₁ => ?_)
  have esi₁ : s₁.gpr .esi = s.gpr .esi := by rw [o₁.gpr _ (by decide)]; simp [State.setReg]
  have edi₁ : s₁.gpr .edi = s.gpr .edi := by rw [o₁.gpr _ (by decide)]; simp [State.setReg]
  have m₁ : s₁.mem = s.mem := o₁.mem
  have rw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [o₁.rd, o₁.wr]; rfl
  refine wp_mov fun s₂ u₂ => wp_ldm (B := s.gpr .edi) (o := 0) (by rw [u₂.other _ (by decide), edi₁])
    (by rw [u₂.rd, u₂.wr, rw₁]; exact hib) fun s₃ u₃ =>
    wp_addm (B := s.gpr .esi) (o := 0) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), esi₁])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hia) fun s₄ u₄ => ?_
  have v₃ : (s₃.gpr .eax).toNat = b := by rw [u₃.gpr, u₂.mem, m₁]; exact hvb
  have v₄ : (s₄.gpr .eax).toNat = b + a := by
    rw [u₄.gpr, BitVec.toNat_add, v₃, u₃.mem, u₂.mem, m₁]
    rw [show (s.mem.readW (addr (s.gpr .esi) 0) 32) = s.mem.readW (s.ea (at_ .esi 0)) 32 from rfl, hva]
    omega
  refine condAdd_spec (by decide) (X := qImm) rfl (by rw [v₄, show qImm.toNat = q from rfl]; omega)
    fun s₅ o₅ v₅ => hb_spec hg (a := (b + a) % q) (by rw [v₅, v₄, show qImm.toNat = 8380417 from rfl, hq]; unfold condAddN; split <;> omega)
      (Nat.mod_lt _ (by decide)) fun s₆ o₆ v₆ => wp_xor fun s₇ u₇ => wp_addi fun s₈ u₈ =>
      wp_shr (by decide) fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => c s₁₀ ?_ ?_ fun _ => ?_
  · have o := (VG.Proof.MlKem.X86.Only.setReg s .eax (s.mem.readW (s.ea (at_ .edi 0)) 32)).trans o₁
    have o := (o.trans (updOnly u₂)).trans (updOnly u₃)
    have o := ((o.trans (updOnly u₄)).trans o₅).trans o₆
    have o := (((o.trans (updOnly u₇)).trans (updOnly u₈)).trans (updOnly u₉)).trans (updOnly u₁₀)
    exact o.mono (by decide)
  · have eb₆ : (s₆.gpr .ebx).toNat = hbV g b := by
      rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, v₁]
      rfl
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_add,
      BitVec.toNat_xor, v₆, eb₆, Nat.shiftRight_eq_div_pow]
    have h1 := hbV_lt64 hg ((b + a) % q)
    have h2 := hbV_lt64 hg b
    have hx : hbF g ((b + a) % q) % hbM g ^^^ hbV g b < 2 ^ 6 := Nat.xor_lt_two_pow (by unfold hbV at h1; omega) (by omega)
    rw [show (63 : BitVec 32).toNat = 63 from rfl, Nat.mod_eq_of_lt (by omega),
      show hbF g ((b + a) % q) % hbM g = hbV g ((b + a) % q) from rfl, xor_shift h1 h2, mhV]
    by_cases e : hbV g b = hbV g ((b + a) % q)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e.symm), ite_eq_left_of_eq_true _ _ (eq_true e)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => e h.symm), ite_eq_right_of_eq_false _ _ (eq_false e)]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), o₆.gpr _ (by decide),
      o₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      o₁.gpr _ (by decide), u₁₀.other _ (by decide)]
    simp [State.setReg]

/-- `UseHint`, from the hint word `a` and `b`. -/
def uhV (g a b : Nat) : Nat :=
  (if a ≠ 0 then (if hbF g b * (2 * g) < b then hbF g b + hbM g + 1 else hbF g b + hbM g - 1)
    else hbF g b + hbM g) % hbM g

/-- The masked `±1`: `1` or `-1` if `c₂`, as `c₁`, and else `0`. -/
def uhD (c₁ c₂ : Bool) : BitVec 32 :=
  (((if c₁ then BitVec.allOnes 32 else 0) &&& 2) - 1) &&& (if c₂ then BitVec.allOnes 32 else 0)

/-- The masked `±1` and the additions of `f` and `m`. -/
theorem uh_val (c₁ c₂ : Bool) (F M : BitVec 32) (hF : F.toNat + M.toNat + 1 < 2 ^ 32) (hM : 1 ≤ M.toNat) :
    (uhD c₁ c₂ + F + M).toNat =
      if c₂ then (if c₁ then F.toNat + M.toNat + 1 else F.toNat + M.toNat - 1) else F.toNat + M.toNat := by
  cases c₁ <;> cases c₂
  · rw [show uhD false false = 0 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega
  · rw [show uhD false true = BitVec.allOnes 32 by decide, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_allOnes]
    simp; omega
  · rw [show uhD true false = 0 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega
  · rw [show uhD true true = 1 by decide, BitVec.toNat_add, BitVec.toNat_add]
    simp; omega

/-- Two conditional subtractions of `m` reduce a value less than `3m`. -/
theorem condAdd_twice {x m : Nat} (hx : x < 3 * m) : condAddN (condAddN x m m) m m = x % m := by
  unfold condAddN
  by_cases h₁ : x < m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), show x + m - m = x by omega,
      ite_eq_left_of_eq_true _ _ (eq_true h₁), show x + m - m = x by omega, Nat.mod_eq_of_lt h₁]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁)]
    by_cases h₂ : x - m < m
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₂), show x - m + m - m = x - m by omega,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h₂]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₂), Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem uhCore_eq (g : Nat) (is : List Instr) : uhCore g ++ is =
    .mov .eax (.mem (at_ .edi 0)) :: .mov .ebx (.reg .eax) :: (hbRaw g ++
      (.mov .ecx (.reg .eax) :: .mov .edx (.imm (BitVec.ofNat 32 (2 * g))) :: .mul .edx ::
        .alu .sub .eax (.reg .ebx) :: .alu .sbb .eax (.reg .eax) :: .alu .and .eax (.imm 2) ::
        .alu .sub .eax (.imm 1) :: .mov .ebx (.imm 0) :: .alu .sub .ebx (.mem (at_ .esi 0)) ::
        .alu .sbb .ebx (.reg .ebx) :: .alu .and .eax (.reg .ebx) :: .alu .add .eax (.reg .ecx) ::
        .alu .add .eax (.imm (BitVec.ofNat 32 (dMod g))) ::
        (condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g)) ++
        (condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g)) ++ is)))) := by
  simp only [uhCore, List.cons_append, List.nil_append, List.append_assoc]

theorem uhCore_spec {g : Nat} (hg : g ∈ gamma2s) : Core2 (uhCore g) (uhV g) false false := by
  intro is s P a b _ hb hia hva hib hvb c
  have hq : q = 8380417 := rfl
  have hf := hbF_le hg hb
  have hm : 16 ≤ hbM g ∧ hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hgl : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hk : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by rw [dMod_eq hg]; exact ofNat_small (by omega)
  rw [uhCore_eq]
  refine wp_movm hib (wp_mov fun s₂ u₂ => hbRaw_spec hg (a := b) ?_ hb fun s₃ o₃ v₃ => ?_)
  · rw [u₂.other _ (by decide)]; simp [State.setReg, hvb]
  have b₃ : (s₃.gpr .ebx).toNat = b := by
    rw [o₃.gpr _ (by decide), u₂.gpr]; simp [State.setReg, hvb]
  have esi₃ : s₃.gpr .esi = s.gpr .esi := by
    rw [o₃.gpr _ (by decide), u₂.other _ (by decide)]; simp [State.setReg]
  have m₃ : s₃.mem = s.mem := by rw [o₃.mem, u₂.mem]; rfl
  have rw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [o₃.rd, o₃.wr, u₂.rd, u₂.wr]; rfl
  refine wp_mov fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have e₅ : (s₅.gpr .eax).toNat = hbF g b := by rw [u₅.other _ (by decide), u₄.other _ (by decide), v₃]
  have d₅ : (s₅.gpr .edx).toNat = 2 * g := by rw [u₅.gpr]; exact ofNat_small (by omega)
  have hmul : hbF g b * (2 * g) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_trans hf hm.2) hgl) (by decide)
  refine wp_mulSmall (r := .edx) (by rw [e₅, d₅]; exact hmul) fun s₆ o₆ v₆ => ?_
  refine wp_subr fun s₇ u₇ c₇ => wp_sbb_self c₇ fun s₈ u₈ => wp_andi fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ _ _ =>
    wp_movi fun s₁₁ u₁₁ => wp_subm (B := s.gpr .esi) (o := 0) ?_ ?_ fun s₁₂ u₁₂ c₁₂ =>
    wp_sbb_self c₁₂ fun s₁₃ u₁₃ => wp_and fun s₁₄ u₁₄ => wp_add fun s₁₅ u₁₅ _ => wp_addi fun s₁₆ u₁₆ => ?_
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), o₆.gpr _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
  · rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, o₆.rd, o₆.wr, u₅.rd, u₅.wr,
      u₄.rd, u₄.wr, rw₃]
    exact hia
  have e₆ : (s₆.gpr .eax).toNat = hbF g b * (2 * g) := by rw [v₆, e₅, d₅]
  have eb₆ : (s₆.gpr .ebx).toNat = b := by
    rw [o₆.gpr _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃]
  have eF : (s₁₂.gpr .ecx).toNat = hbF g b := by
    rw [u₁₂.other .ecx (by decide), u₁₁.other .ecx (by decide), u₁₀.other .ecx (by decide),
      u₉.other .ecx (by decide), u₈.other .ecx (by decide), u₇.other .ecx (by decide), o₆.gpr .ecx (by decide),
      u₅.other .ecx (by decide), u₄.gpr, v₃]
  have ea : (s₁₁.mem.readW (addr (s.gpr .esi) 0) 32).toNat = a := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, o₆.mem, u₅.mem, u₄.mem, m₃]; exact hva
  have e0 : (s₁₁.gpr .ebx).toNat = 0 := by rw [u₁₁.gpr]; rfl
  have x₁₆ : (s₁₆.gpr .eax).toNat =
      if 0 < a then (if hbF g b * (2 * g) < b then hbF g b + hbM g + 1 else hbF g b + hbM g - 1)
      else hbF g b + hbM g := by
    rw [u₁₆.gpr, u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₄.other .ecx (by decide), u₁₃.other .eax (by decide),
      u₁₃.other .ecx (by decide), u₁₂.other .eax (by decide), u₁₁.other .eax (by decide), u₁₀.gpr, u₉.gpr,
      u₈.gpr, e₆, eb₆, e0, ea]
    refine (uh_val _ _ _ _ (by rw [eF, hk]; omega) (by rw [hk]; omega)).trans ?_
    rw [eF, hk]
    by_cases h₁ : 0 < a <;> by_cases h₂ : hbF g b * (2 * g) < b <;> simp [h₁, h₂]
  have hx : (s₁₆.gpr .eax).toNat < 3 * hbM g := by
    rw [x₁₆]; split
    · split <;> omega
    · omega
  refine condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl (by rw [hk]; omega)
    fun s₁₇ o₁₇ v₁₇ => condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl
      (by rw [hk, v₁₇, hk]; unfold condAddN; split <;> omega) fun s₁₈ o₁₈ v₁₈ =>
      c s₁₈ ?_ ?_ (fun h => absurd h (by decide))
  · have o := (VG.Proof.MlKem.X86.Only.setReg s .eax (s.mem.readW (s.ea (at_ .edi 0)) 32)).trans (updOnly u₂)
    have o := ((o.trans o₃).trans (updOnly u₄)).trans (updOnly u₅)
    have o := (((o.trans o₆).trans (updOnly u₇)).trans (updOnly u₈)).trans (updOnly u₉)
    have o := (((o.trans (updOnly u₁₀)).trans (updOnly u₁₁)).trans (updOnly u₁₂)).trans (updOnly u₁₃)
    have o := ((((o.trans (updOnly u₁₄)).trans (updOnly u₁₅)).trans (updOnly u₁₆)).trans o₁₇).trans o₁₈
    exact o.mono (by decide)
  · rw [v₁₈, v₁₇, hk, condAdd_twice hx, x₁₆, uhV]
    by_cases h₁ : 0 < a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), ite_eq_left_of_eq_true _ _ (eq_true (by omega : a ≠ 0))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬a ≠ 0))]

end VG.Proof.MlDsa.X86.Round
