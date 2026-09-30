import VerifiedGarbage.Proof.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt

/-!
# ML-DSA on x86 (32-bit): the butterflies

Untrusted: everything here is checked by Lean. With `esi` at coefficient `j`
and `edi` at coefficient `j + len` of a polynomial `G` stored at `p` and
`ebp` at the zeta `z` in Montgomery form (`z · 2³² mod q`, `BIn`),
`bflyBody` leaves `bfly G j len z` there and `ibflyBody` leaves
`bflyInv G j len z` (`BOut`), both advancing `esi` and `edi` by 4 and
counting `ecx` down.
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n Poly Zq PolyIs coeffAt)
open VG.Proof.MlKem.X86 (Only wp_cons wp_movm wp_movr wp_mul toNat_ofNat32 eq_ofNat_of_toNat execMul_other)

/-- A butterfly's inputs. -/
structure BIn (s : State) (p : Addr) (G : Poly) (j len : Nat) (zA : Addr) (z : Zq) : Prop where
  ea_i : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p j
  ea_d : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p (j + len)
  ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = zA
  in_i : InRegions s.wr (coeffAddr p j) 4
  in_d : InRegions s.wr (coeffAddr p (j + len)) 4
  in_z : InRegions (s.rd ++ s.wr) zA 4
  z_v : s.mem.readW zA 32 = BitVec.ofNat 32 (z.val * 2 ^ 32 % q)
  z_sep : Mem.Sep zA 4 (coeffAddr p j) 4
  poly : PolyIs s.mem p G
  hj : j + len < 256
  hl : 0 < len

/-- What a butterfly leaves. -/
structure BOut (s : State) (p : Addr) (G' : Poly) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → r ≠ .esi → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r
  esi : s'.gpr .esi = s.gpr .esi + 4
  edi : s'.gpr .edi = s.gpr .edi + 4
  ecx : s'.gpr .ecx = s.gpr .ecx - 1
  ne : eval .ne s' = some (!(s.gpr .ecx - 1 == 0))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [polyRegion p] s.mem s'.mem
  poly : PolyIs s'.mem p G'

theorem inRd {s : State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- The polynomial `G'` is stored after two coefficients of `G` are written,
if `G'` differs from `G` only there. -/
theorem polyIs_two {m : Mem} {p : Addr} {G G' : Poly} (h : PolyIs m p G) {i₁ i₂ : Nat} (h₁ : i₁ < n)
    (h₂ : i₂ < n) {v₁ v₂ : BitVec 32} (hv₁ : v₁.toNat = (G'[i₁]!).val)
    (hv₂ : v₂.toNat = (G'[i₂]!).val) (hr : ∀ i < n, i ≠ i₁ → i ≠ i₂ → G'[i]! = G[i]!) :
    PolyIs ((m.writeW (coeffAddr p i₁) v₁).writeW (coeffAddr p i₂) v₂) p G' := by
  refine polyIs_of_toNat fun i hi => ?_
  rw [coeffAt_writeW _ _ hi h₂, coeffAt_writeW _ _ hi h₁]
  by_cases e₂ : i₂ = i
  · subst e₂; rw [ite_eq_left rfl, hv₂]
  rw [ite_eq_right e₂]
  by_cases e₁ : i₁ = i
  · subst e₁; rw [ite_eq_left rfl, hv₁]
  rw [ite_eq_right e₁, polyIs_toNat h hi, hr i hi (Ne.symm e₁) (Ne.symm e₂)]

/-- The coefficient stored for `G[i]`. -/
theorem polyIs_coeffAt {m : Mem} {p : Addr} {G : Poly} (h : PolyIs m p G) {i : Nat} (hi : i < n) :
    coeffAt m p i = BitVec.ofNat 32 (G[i]!).val := by
  apply BitVec.eq_of_toNat_eq
  rw [polyIs_toNat h hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt G[i]!; omega)]

theorem bflyBody_eq : bflyBody =
    .mov .eax (.mem (at_ .edi 0)) :: .mov .edx (.mem (at_ .ebp 0)) :: .mul .edx :: (mred .ebx ++
      ([.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm qImm), .alu .sub .eax (.reg .ebx)] ++
        csubQ .eax .edx ++
        [.store (at_ .edi 0) .eax, .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.reg .ebx)] ++
        csubQ .eax .edx ++
        [.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
          .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [bflyBody, List.cons_append, List.nil_append, List.append_assoc]

theorem bfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Zq}
    (h : BIn s p G j len zA z) : WP isa (.block bflyBody) s (BOut s p (bfly G j len z)) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := val_lt z
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have hzv := h.z_v
  generalize ez : z.val = zv at lz hzv
  have hzm : zv * 2 ^ 32 % q < q := Nat.mod_lt _ (by decide)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 (zv * 2 ^ 32 % q)).toNat = zv * 2 ^ 32 % q := toNat_ofNat32 (mod_q_lt32 _)
  have hbz : b * (zv * 2 ^ 32 % q) < q * 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lb hzm
    rw [q_eq] at this ⊢; omega
  rw [bflyBody_eq]
  refine wp_movm ?_ (wp_movm ?_ (wp_mul (mred_spec (r := .ebx) (by decide) (by decide) _ _ _
    (x := b * (zv * 2 ^ 32 % q)) ?_ hbz fun s₂ o₂ v₂ => ?_)))
  · rw [State.ea, at_]; exact h.ea_d ▸ inRd h.in_d
  · simp only [State.ea, at_, State.setReg, show Reg.ebp ≠ Reg.eax by decide, ite_false, h.ea_z]
    exact h.in_z
  · rw [execMul_pair]
    simp (config := {decide := true}) only [State.setReg, ite_true, ite_false, State.ea, at_, h.ea_d, h.ea_z,
      hb, hzv]
    rw [hb', hz']
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [State.setReg, h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [o₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr]; rfl
  have ht : mont (b * (zv * 2 ^ 32 % q)) % q = b * zv % q := mont_mulR b zv
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (b * zv % q) := eq_ofNat_of_toNat (v₂.trans ht)
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p (j + len)) V).readW (coeffAddr p j) 32 =
      s.mem.readW (coeffAddr p j) 32 := fun V => coeffAt_writeW_ne _ _ hj hjl (by omega) V
  have inI := h.in_i
  have inD := h.in_d
  have inI' := inRd h.in_i
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csubQ, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32, State.store32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, esi₂, edi₂, ecx₂, m₂,
    rd₂, wr₂, bx₂, ea_i, ea_d, inI, inD, inI', hrw, ha, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have lt := Nat.mod_lt (b * zv) (show q > 0 by decide)
  rw [q_eq] at lt
  have e1 : (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 (b * zv % q)).toNat = a + q - b * zv % q := by
    have hQ : (BitVec.ofNat 32 a + qImm).toNat = a + 8380417 := by
      rw [BitVec.toNat_add, toNat_ofNat32 (by omega), qImm_toNat, q_eq, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, toNat_ofNat32 (by rw [q_eq]; omega)]; rw [q_eq]; omega),
      hQ, toNat_ofNat32 (by rw [q_eq]; omega), q_eq]
  have e2 : (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * zv % q)).toNat = a + b * zv % q := by
    rw [BitVec.toNat_add, toNat_ofNat32 (by omega), toNat_ofNat32 (by rw [q_eq]; omega),
      Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
  rw [csubQ_eq (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 (b * zv % q)) _ (by rw [e1, q_eq]; omega),
    csubQ_eq (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * zv % q)) _ (by rw [e2, q_eq]; omega), e1, e2]
  have ht' : (z * G[j + len]!).val = b * zv % q := by
    rw [val_mul, ez, eb, Nat.mul_comm]
  have hv1 : BitVec.ofNat 32 ((a + q - b * zv % q) % q) = BitVec.ofNat 32 ((G[j]! - z * G[j + len]!).val) := by
    rw [sub_val, ht', ea]
  have hv2 : BitVec.ofNat 32 ((a + b * zv % q) % q) = BitVec.ofNat 32 ((G[j]! + z * G[j + len]!).val) := by
    rw [val_add', ht', ea]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h1, h2, h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)
  · rw [hv1, hv2]
    refine polyIs_two h.poly hjl hj ?_ ?_ fun i hi h1 h2 => ?_
    · rw [bfly_get _ hl hjl _ hjl, ite_eq_right (by omega), ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! - z * G[j + len]!); omega)
    · rw [bfly_get _ hl hjl _ hj, ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! + z * G[j + len]!); omega)
    · rw [bfly_get _ hl hjl _ hi, ite_eq_right h2, ite_eq_right h1]

theorem ibflyBody_eq : ibflyBody =
    (([.mov .ebx (.mem (at_ .esi 0)), .alu .add .ebx (.imm qImm), .alu .sub .ebx (.mem (at_ .edi 0)),
      .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] : List Instr) ++ csubQ .eax .edx ++
      ([.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] : List Instr)) ++
    (mred .ebx ++ ([.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [ibflyBody, List.append_assoc]

theorem ibfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Zq}
    (h : BIn s p G j len zA z) : WP isa (.block ibflyBody) s (BOut s p (bflyInv G j len z)) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := val_lt z
  rw [coeffAt_eq] at ha hb
  have hzv := h.z_v
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  generalize ez : z.val = zv at lz hzv
  have hzm : zv * 2 ^ 32 % q < q := Nat.mod_lt _ (by decide)
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 (zv * 2 ^ 32 % q)).toNat = zv * 2 ^ 32 % q := toNat_ofNat32 (mod_q_lt32 _)
  have hbz : (a + q - b) * (zv * 2 ^ 32 % q) < q * 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a + q - b < 2 * q by rw [q_eq]; omega) hzm
    rw [q_eq] at this ⊢; omega
  have hrz : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p j) V).readW zA 32 = s.mem.readW zA 32 :=
    fun V => Mem.readW_writeW_sep h.z_sep (by decide)
  have inI := h.in_i
  have inD := h.in_d
  have inI' := inRd h.in_i
  have inD' := inRd h.in_d
  have inZ := h.in_z
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  have ea_z := h.ea_z
  rw [ibflyBody_eq, WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csubQ, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, ea_i, ea_d,
    ea_z, inI, inI', inD', inZ, ha, hb, hrz, hzv, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hsub : (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 b).toNat = a + q - b := by
    have hQ : (BitVec.ofNat 32 a + qImm).toNat = a + q := by
      rw [BitVec.toNat_add, ha', qImm_toNat, Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, hb']; omega), hQ, hb']
  have hsum : (BitVec.ofNat 32 a + BitVec.ofNat 32 b).toNat = a + b := by
    rw [BitVec.toNat_add, ha', hb', Nat.mod_eq_of_lt (by omega)]
  refine mred_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := (a + q - b) * (zv * 2 ^ 32 % q)) ?_ hbz
    fun s₂ o₂ v₂ => ?_
  · rw [execMul_pair]
    simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz']
  have m₂ := o₂.mem
  simp only [execMul, State.setReg, State.setFlags] at m₂
  rw [csubQ_eq _ _ (by rw [hsum, q_eq]; omega), hsum] at m₂
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [h1, h2, h3, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr]; rfl
  have ht : mont ((a + q - b) * (zv * 2 ^ 32 % q)) % q = (a + q - b) * zv % q := mont_mulR _ zv
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 ((a + q - b) * zv % q) := eq_ofNat_of_toNat (v₂.trans ht)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, edi₂, ecx₂, m₂, rd₂, wr₂, bx₂, ea_d, inD, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hv1 : BitVec.ofNat 32 ((a + b) % q) = BitVec.ofNat 32 ((G[j]! + G[j + len]!).val) := by
    rw [val_add', ea, eb]
  have hv2 : BitVec.ofNat 32 ((a + q - b) * zv % q) =
      BitVec.ofNat 32 ((z * (G[j]! - G[j + len]!)).val) := by
    rw [val_mul, sub_val, ez, ea, eb, Nat.mul_comm zv, Nat.mod_mul_mod]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)
  · rw [hv1, hv2]
    refine polyIs_two h.poly hj hjl ?_ ?_ fun i hi h1 h2 => ?_
    · rw [bflyInv_get _ hl hjl _ hj, ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! + G[j + len]!); omega)
    · rw [bflyInv_get _ hl hjl _ hjl, ite_eq_right (by omega), ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (z * (G[j]! - G[j + len]!)); omega)
    · rw [bflyInv_get _ hl hjl _ hi, ite_eq_right h1, ite_eq_right h2]

end VG.Proof.MlDsa.X86.Arith
