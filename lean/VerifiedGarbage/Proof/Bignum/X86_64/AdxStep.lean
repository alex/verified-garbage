import VerifiedGarbage.Impl.Bignum.X86_64.Adx
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Multiword arithmetic on x86-64: the steps of the BMI2/ADX multiplication

The instructions of a block of `montMulAdx` (`Impl/Bignum/X86_64/Adx.lean`),
each run symbolically once, for any registers: `mulx`, `adcx` and `adox`
(`mulx_ok`, `adcx_ok`, `adox_ok`), and the shapes made of them, a word of
the block's first half (`wordA_ok`) and of its second (`wordB_ok`), and the
end of a chain (`close_ok`). Each states what it computes as an equation on
numbers, the carries in and out included, which `omega` composes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs' s₂ s₃) :
    Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r fun h => hr (List.mem_append_right _ h)).trans (h₁.1 r fun h => hr (List.mem_append_left _ h)),
    h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.gpr {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

/-- A memory operand reads the same after registers other than its own change. -/
theorem Keeps.readMem {rs : List Reg} {s s' : State} (h : Keeps rs s s') {m : MemOp} (hb : m.base ∉ rs)
    (hi : ∀ i, m.index = some i → i ∉ rs) : readSrc s' (.mem m) = readSrc s (.mem m) := by
  have hea : s'.ea m = s.ea m := by
    unfold State.ea
    cases e : m.index with
    | none => simp only [h.gpr hb]
    | some i => simp only [h.gpr hb, h.gpr (hi i e)]
  simp only [readSrc, State.load64, hea, h.2.1, h.2.2.1, h.2.2.2]

theorem toNat_ofBool64 (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

/-- The halves of a product of two words: `lo + 2⁶⁴ hi`. -/
theorem mulx_arith (d v : BitVec 64) :
    (BitVec.ofNat 64 (d.toNat * v.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (d.toNat * v.toNat / 2 ^ 64)).toNat = d.toNat * v.toNat := by
  have hd := d.isLt; have hv := v.isLt
  have hp : d.toNat * v.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hd hv
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ofBool64]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `mulx hi, lo, src`: `lo + 2⁶⁴ hi = rdx · src`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo src]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  have he : execMulx hi lo src s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execMulx, hsrc, Option.map_some]
    | mem m => simp only [execMulx, hsrc, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), Option.some.injEq, exists_eq_left']
  refine ⟨mulx_arith _ _, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adcx dst, src`: `dst + 2⁶⁴ CF' = dst + src + CF`, OF unchanged. -/
theorem adcx_ok (s : State) {dst : Reg} {src : Src} {v : BitVec 64} {c : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c) :
    WP isa (.block [.adcx dst src]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧ s'.of = s.of ∧
      (s'.gpr dst).toNat + 2 ^ 64 * c'.toNat = (s.gpr dst).toNat + v.toNat + c.toNat ∧ Keeps [dst] s s' := by
  have he : execAdcx dst src s = some ((s.setFlags (some (2 ^ 64 ≤ (s.gpr dst).toNat + v.toNat + c.toNat))
      s.of s.zf s.sf).setReg dst (s.gpr dst + v + (BitVec.ofBool c).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, Option.some.injEq, exists_eq_left']
  refine ⟨_, rfl, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    exact adc_carry _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adox dst, src`: `dst + 2⁶⁴ OF' = dst + src + OF`, CF unchanged. -/
theorem adox_ok (s : State) {dst : Reg} {src : Src} {v : BitVec 64} {o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (ho : s.of = some o) :
    WP isa (.block [.adox dst src]) s fun s' => ∃ o' : Bool, s'.of = some o' ∧ s'.cf = s.cf ∧
      (s'.gpr dst).toNat + 2 ^ 64 * o'.toNat = (s.gpr dst).toNat + v.toNat + o.toNat ∧ Keeps [dst] s s' := by
  have he : execAdox dst src s = some ((s.setFlags s.cf (some (2 ^ 64 ≤ (s.gpr dst).toNat + v.toNat + o.toNat))
      s.zf s.sf).setReg dst (s.gpr dst + v + (BitVec.ofBool o).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, Option.some.injEq, exists_eq_left']
  refine ⟨_, rfl, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    exact adc_carry _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `mov32 r, 0`: the flags unchanged. -/
theorem movZero_ok (s : State) (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun s' =>
      s'.gpr r = 0 ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- A word of a block's first half: `col := lo(rdx · b_k) + T_k + CF`, then
`+ prev + OF`, the product's high half into `hi`. -/
theorem wordA_ok (s : State) {k : Nat} {hi col prev : Reg} {vb vt : BitVec 64} {c o : Bool}
    (hb : readSrc s (.mem (ix .r9 .r14 (8 * k))) = some vb) (ht : readSrc s (.mem (ix .r8 .r14 (8 * k))) = some vt)
    (hc : s.cf = some c) (ho : s.of = some o) (d1 : hi ≠ col) (d2 : prev ≠ hi) (d3 : prev ≠ col)
    (d4 : hi ≠ .r8) (d5 : col ≠ .r8) (d6 : hi ≠ .r14) (d7 : col ≠ .r14) :
    WP isa (.block (wordA k hi col prev)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr col).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (s.gpr .rdx).toNat * vb.toNat + vt.toNat + c.toNat + (s.gpr prev).toNat + o.toNat ∧
      Keeps [hi, col] s s' := by
  rw [show wordA k hi col prev = ([.mulx hi col (.mem (ix .r9 .r14 (8 * k)))] : List Instr) ++
    (([.adcx col (.mem (ix .r8 .r14 (8 * k)))] : List Instr) ++ ([.adox col (.reg prev)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (mulx_ok s hb (fun _ h => nomatch h) d1) fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have ht₁ : readSrc s₁ (.mem (ix .r8 .r14 (8 * k))) = some vt := by
    rw [k₁.readMem (by simp [ix]; exact ⟨Ne.symm d4, Ne.symm d5⟩) (by
      intro i hi'; simp only [ix, Option.some.injEq] at hi'; subst hi'; simp; exact ⟨Ne.symm d6, Ne.symm d7⟩)]
    exact ht
  refine WP.mono (adcx_ok s₁ ht₁ (fun _ h => nomatch h) (c₁.trans hc)) fun s₂ ⟨c', hc₂, ho₂, e₂, k₂⟩ => ?_
  refine WP.mono (adox_ok s₂ (src := .reg prev) rfl (fun _ h => nomatch h) (ho₂.trans (o₁.trans ho)))
    fun s₃ ⟨o', ho₃, hc₃, e₃, k₃⟩ => ⟨c', o', hc₃.trans hc₂, ho₃, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have p₂ : s₂.gpr prev = s.gpr prev := (k₂.gpr (by simpa using d3)).trans (k₁.gpr (by simp [d2, d3]))
  have h₃ : s₃.gpr hi = s₁.gpr hi := (k₃.gpr (by simpa using d1)).trans (k₂.gpr (by simpa using d1))
  rw [h₃]
  rw [p₂] at e₃
  omega

/-- A word of a block's second half: `col += lo(rdx · m_k) + CF`, then
`+ prev + OF`, the product's high half into `hi`. -/
theorem wordB_ok (s : State) {k : Nat} {hi col prev : Reg} {vm : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (ix .r10 .r14 (8 * k))) = some vm)
    (hc : s.cf = some c) (ho : s.of = some o) (d1 : hi ≠ col) (d2 : prev ≠ hi) (d3 : prev ≠ col)
    (d4 : hi ≠ .rsi) (d5 : col ≠ .rsi) (d6 : prev ≠ .rsi) :
    WP isa (.block (wordB k hi col prev)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr col).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (s.gpr col).toNat + (s.gpr .rdx).toNat * vm.toNat + c.toNat + (s.gpr prev).toNat + o.toNat ∧
      Keeps [hi, .rsi, col] s s' := by
  rw [show wordB k hi col prev = ([.mulx hi .rsi (.mem (ix .r10 .r14 (8 * k)))] : List Instr) ++
    (([.adcx col (.reg .rsi)] : List Instr) ++ ([.adox col (.reg prev)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) d4) fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s₁ (src := .reg .rsi) rfl (fun _ h => nomatch h) (c₁.trans hc))
    fun s₂ ⟨c', hc₂, ho₂, e₂, k₂⟩ => ?_
  refine WP.mono (adox_ok s₂ (src := .reg prev) rfl (fun _ h => nomatch h) (ho₂.trans (o₁.trans ho)))
    fun s₃ ⟨o', ho₃, hc₃, e₃, k₃⟩ => ⟨c', o', hc₃.trans hc₂, ho₃, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have p₂ : s₂.gpr prev = s.gpr prev := (k₂.gpr (by simpa using d3)).trans (k₁.gpr (by simp [d2, d6]))
  have h₃ : s₃.gpr hi = s₁.gpr hi := (k₃.gpr (by simpa using d1)).trans (k₂.gpr (by simpa using d1))
  have r₁ : s₁.gpr col = s.gpr col := k₁.gpr (by simp [Ne.symm d1, d5])
  have i₂ : s₂.gpr .rsi = s₁.gpr .rsi := k₂.gpr (by simpa using Ne.symm d5)
  rw [h₃]
  rw [p₂] at e₃
  rw [r₁] at e₂
  omega

/-- The end of both chains: `h += OF + CF`. -/
theorem close_ok (s : State) {h : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) (hh : h ≠ .rsi) :
    WP isa (.block (close h)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr h).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat = (s.gpr h).toNat + c.toNat + o.toNat ∧
      Keeps [.rsi, h] s s' := by
  rw [show close h = ([.mov32 .rsi (.imm 0)] : List Instr) ++
    (([.adox h (.reg .rsi)] : List Instr) ++ ([.adcx h (.reg .rsi)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rsi) fun s₁ ⟨z₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s₁ (src := .reg .rsi) rfl (fun _ h => nomatch h) (o₁.trans ho))
    fun s₂ ⟨o', ho₂, hc₂, e₂, k₂⟩ => ?_
  refine WP.mono (adcx_ok s₂ (src := .reg .rsi) rfl (fun _ h => nomatch h) (hc₂.trans (c₁.trans hc)))
    fun s₃ ⟨c', hc₃, ho₃, e₃, k₃⟩ => ⟨c', o', hc₃, ho₃.trans ho₂, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have r₁ : s₁.gpr h = s.gpr h := k₁.gpr (by simpa using hh)
  have z₂ : s₂.gpr .rsi = 0 := (k₂.gpr (by simpa using Ne.symm hh)).trans z₁
  rw [r₁, z₁] at e₂
  rw [z₂] at e₃
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at e₂ e₃
  omega

/-- `xor esi, esi`: CF and OF clear. -/
theorem xorRsi_ok (s : State) :
    WP isa (.block [.alu32 .xor .rsi (.reg .rsi)]) s fun s' =>
      s'.gpr .rsi = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `mov dst, [m]`: the flags unchanged. -/
theorem movMem_ok (s : State) {dst : Reg} {m : MemOp} {v : BitVec 64} (hsrc : readSrc s (.mem m) = some v) :
    WP isa (.block [.mov dst (.mem m)]) s fun s' =>
      s'.gpr dst = v ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [dst] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hsrc, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨RegUpd.gpr_setReg_self .., rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

end VG.Proof.Bignum.X86_64
