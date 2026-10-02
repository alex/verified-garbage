import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.MlKem.Ntt

/-!
# ML-KEM on x86 (32-bit): the butterflies

With `esi` at coefficient `j` and `edi` at coefficient `j + len` of a
polynomial `G` stored at `p` and `ebp` at a zeta `z` (`BIn`), `bflyBody`
leaves `bfly G j len z` there and `ibflyBody` leaves `bflyInv G j len z`
(`BOut`), both advancing `esi` and `edi` by 4 and counting `ecx` down.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- A butterfly's inputs. -/
structure BIn (s : State) (p : Addr) (G : Poly) (j len : Nat) (zA : Addr) (z : Nat) : Prop where
  ea_i : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p j
  ea_d : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p (j + len)
  ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = zA
  in_i : InRegions s.wr (coeffAddr p j) 4
  in_d : InRegions s.wr (coeffAddr p (j + len)) 4
  in_z : InRegions (s.rd ++ s.wr) zA 4
  z_v : s.mem.readW zA 32 = BitVec.ofNat 32 z
  z_lt : z < q
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

theorem bfly_set (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    bfly G j len z = (G.set! (j + len) (G[j]! - z * G[j + len]!)).set! j (G[j]! + z * G[j + len]!) := by
  simp only [bfly]
  rw [getElem!_set!_ne _ (by omega) (by omega)]

theorem bflyInv_set (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    bflyInv G j len z = (G.set! j (G[j]! + G[j + len]!)).set! (j + len) (z * (G[j + len]! - G[j]!)) := by
  simp only [bflyInv]
  rw [getElem!_set!_ne _ (by omega) (by omega)]

theorem sub_val_eq (a t : Zq) : (a - t).val = (a.val + q - t.val) % q := by
  rw [val_sub, condSub_eq (by have := a.isLt; have := t.isLt; omega)]

theorem add_val_eq (a t : Zq) : (a + t).val = (a.val + t.val) % q := by
  rw [val_add, condSub_eq (by have := a.isLt; have := t.isLt; omega)]

theorem bfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat}
    (h : BIn s p G j len zA z) : WP isa (.block bflyBody) s (BOut s p (bfly G j len (ofNat z))) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := h.z_lt
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have lz' : z < 3329 := q_eq ▸ h.z_lt
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 z).toNat = z := toNat_ofNat32 (by omega)
  have hbz : b * z < 2 ^ 32 := by rw [q_eq] at lz; have := Nat.mul_lt_mul_of_lt_of_lt lb lz; omega
  rw [bflyBody, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movm ?_ (wp_movm ?_ (wp_mul (wp_movr (red_spec (r := .ebx) (by decide) (by decide) _ _ _
    (x := b * z) ?_ ?_ fun s₂ o₂ v₂ => ?_))))
  · rw [State.ea, at_]; exact h.ea_d ▸ inRd h.in_d
  · simp only [State.ea, at_, State.setReg, show Reg.ebp ≠ Reg.eax by decide, ite_false, h.ea_z]
    exact h.in_z
  · simp (config := {decide := true}) only [State.setReg, execMul_eax, ite_true, ite_false, State.ea,
      at_, h.ea_d, h.ea_z, hb, h.z_v]
    rw [hb', hz', toNat_ofNat32 hbz]
  · simp (config := {decide := true}) only [State.setReg, execMul_eax, ite_true, ite_false, State.ea,
      at_, h.ea_d, h.ea_z, hb, h.z_v]
    rw [hb', hz', toNat_ofNat32 hbz]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [State.setReg, h3, ite_false]
    rw [execMul_other _ _ h1 h2]
    simp only [h1, h2, ite_false]
  have m₁ : s₂.mem = s.mem := o₂.mem
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := m₁
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (b * z % q) := eq_ofNat_of_toNat v₂
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p (j + len)) V).readW (coeffAddr p j) 32 =
      s.mem.readW (coeffAddr p j) 32 := fun V => coeffAt_writeW_ne _ _ hj hjl (by omega) V
  have inI := h.in_i
  have inD := h.in_d
  have inI' := inRd h.in_i
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32, State.store32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, esi₂, edi₂, ecx₂, m₂,
    rd₂, wr₂, bx₂, ea_i, ea_d, inI, inD, inI', hrw, ha, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have lt := Nat.mod_lt (b * z) (show q > 0 by rw [q_eq]; decide)
  rw [q_eq] at lt
  have e1 : (BitVec.ofNat 32 a + Q - BitVec.ofNat 32 (b * z % q)).toNat = a + q - b * z % q := by
    have hQ : (BitVec.ofNat 32 a + Q).toNat = a + 3329 := by
      rw [BitVec.toNat_add, toNat_ofNat32 (by omega), show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, toNat_ofNat32 (by rw [q_eq]; omega)]; rw [q_eq]; omega),
      hQ, toNat_ofNat32 (by rw [q_eq]; omega), q_eq]
  have e2 : (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * z % q)).toNat = a + b * z % q := by
    rw [BitVec.toNat_add, toNat_ofNat32 (by omega), toNat_ofNat32 (by rw [q_eq]; omega),
      Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
  rw [csub_eq (BitVec.ofNat 32 a + Q - BitVec.ofNat 32 (b * z % q)) _ (by rw [e1, q_eq]; omega),
    csub_eq (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * z % q)) _ (by rw [e2, q_eq]; omega), e1, e2]
  have ht : (ofNat z * G[j + len]!).val = b * z % q := by
    rw [val_mul, ofNat_of_lt h.z_lt, eb, Nat.mul_comm]
  have hv1 : BitVec.ofNat 32 ((a + q - b * z % q) % q) = BitVec.ofNat 32 ((G[j]! - ofNat z * G[j + len]!).val) := by
    rw [sub_val_eq, ht, ea]
  have hv2 : BitVec.ofNat 32 ((a + b * z % q) % q) = BitVec.ofNat 32 ((G[j]! + ofNat z * G[j + len]!).val) := by
    rw [add_val_eq, ht, ea]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h1, h2, h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)
  · rw [hv1, hv2, bfly_set G hl hjl]
    exact polyIs_writeW (polyIs_writeW h.poly hjl _) hj _

theorem ibflyBody_eq : ibflyBody =
    (([.mov .ebx (.mem (at_ .edi 0)), .alu .add .ebx (.imm Q), .alu .sub .ebx (.mem (at_ .esi 0)),
      .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] : List Instr) ++ csub .eax .edx ++
      ([.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx,
        .mov .ebx (.reg .eax)] : List Instr)) ++
    (red .ebx ++ ([.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .ecx (.imm 1)] : List Instr)) := rfl

theorem ibfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat}
    (h : BIn s p G j len zA z) : WP isa (.block ibflyBody) s (BOut s p (bflyInv G j len (ofNat z))) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := polyIs_coeffAt h.poly hj
  have hb := polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have lz' : z < 3329 := q_eq ▸ h.z_lt
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 z).toNat = z := toNat_ofNat32 (by omega)
  have hbz : (b + 3329 - a) * z < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show b + 3329 - a < 6658 by omega) lz'
    omega
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p j) V).readW (coeffAddr p (j + len)) 32 =
      s.mem.readW (coeffAddr p (j + len)) 32 := fun V => coeffAt_writeW_ne _ _ hjl hj (by omega) V
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
  have zv := h.z_v
  rw [ibflyBody_eq, WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.ea, at_, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, ea_i, ea_d,
    ea_z, inI, inI', inD', inZ, ha, hb, hrz, zv, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hsub : (BitVec.ofNat 32 b + Q - BitVec.ofNat 32 a).toNat = b + 3329 - a := by
    have hQ : (BitVec.ofNat 32 b + Q).toNat = b + 3329 := by
      rw [BitVec.toNat_add, hb', show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, ha']; omega), hQ, ha']
  have hsum : (BitVec.ofNat 32 a + BitVec.ofNat 32 b).toNat = a + b := by
    rw [BitVec.toNat_add, ha', hb', Nat.mod_eq_of_lt (by omega)]
  refine red_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := (b + 3329 - a) * z) ?_ ?_
    fun s₂ o₂ v₂ => ?_
  · simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz', toNat_ofNat32 hbz]
  · simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz', toNat_ofNat32 hbz]
  have m₂ := o₂.mem
  rw [csub_eq _ _ (by rw [hsum, q_eq]; omega), hsum] at m₂
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [h1, h2, h3, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 ((b + 3329 - a) * z % q) := eq_ofNat_of_toNat v₂
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, edi₂, ecx₂, m₂, rd₂, wr₂, bx₂, ea_d, inD, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hv1 : BitVec.ofNat 32 ((a + b) % q) = BitVec.ofNat 32 ((G[j]! + G[j + len]!).val) := by
    rw [add_val_eq, ea, eb]
  have hv2 : BitVec.ofNat 32 ((b + 3329 - a) * z % q) =
      BitVec.ofNat 32 ((ofNat z * (G[j + len]! - G[j]!)).val) := by
    rw [val_mul, sub_val_eq, ofNat_of_lt h.z_lt, ea, eb, q_eq, Nat.mul_comm z, Nat.mul_mod,
      Nat.mod_eq_of_lt (a := z) lz']
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)
  · rw [hv1, hv2, bflyInv_set G hl hjl]
    exact polyIs_writeW (polyIs_writeW h.poly hj _) hjl _

end VG.Proof.MlKem.X86
