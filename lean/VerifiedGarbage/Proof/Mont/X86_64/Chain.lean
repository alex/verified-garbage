import VerifiedGarbage.Proof.Mont.X86_64.Csub

/-!
# Montgomery arithmetic on x86-64: loads, stores and carry chains

`loads ts a` and `stores ts o` move words between registers and the working
space; `chain` adds (`add`, then `adc`) or subtracts (`sub`, then `sbb`) the
words at `b` to or from registers, with the carry or borrow out in `CF`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

theorem loads_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Scr s base size → a + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (loads ts a)) s fun s' =>
      regsVal s' ts = wordsVal s.mem base a ts.length ∧ Keeps ts s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, hs, ha, hf => by
    simp only [List.length_cons] at ha
    rw [loads, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov t (.mem (sc a))]) s
        (fun s₁ => s₁.gpr t = word s.mem base a ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := a) (by omega),
        Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2.2 h.symm)
    refine WP.mono (loads_ok ts hs₁ (a := a + 8) (by omega) hf.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [List.length_cons, regsVal, wordsVal, ht, e₁, e₂, k₁.2.1]

theorem stores_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {o : Nat},
    Scr s base size → o + 8 * ts.length ≤ size → ts.Nodup →
    WP isa (.block (stores ts o)) s fun s' =>
      wordsVal s'.mem base o ts.length = regsVal s ts ∧ KeepRegs [] s s' ∧
      Outside base o (8 * ts.length) s.mem s'.mem
  | [], s, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, o, hs, ho, hd => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ho
    rw [stores, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.store (sc o) t]) s
        (fun s₁ => s₁.mem = s.mem.writeW (off base o) (s.gpr t) ∧ KeepRegs [] s s₁ ∧
          s₁.gpr = s.gpr) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs (d := o) (by omega),
        Option.some.injEq, exists_eq_left']
      exact ⟨trivial, ⟨fun _ _ => rfl, rfl, rfl⟩, trivial⟩)
      fun s₁ ⟨m₁, k₁, g₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (stores_ok ts hs₁ (o := o + 8) (by omega) (List.nodup_cons.mp hd).2)
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => ?_⟩
    · rw [List.length_cons, wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, e₂, regsVal,
        regsVal_congr (s := s) fun q _ => congrFun g₁ q]
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

/-- `ts += [b] + c`, `adc` throughout, with the carry `c` in and out. -/
theorem chainAdc_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    Scr s base size → s.cf = some c → b + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (chain .adc .adc ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat =
        regsVal s ts + wordsVal s.mem base b ts.length + c.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.mem (sc b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat +
          c.toNat)).toNat = (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat ∧
        s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_sc hs (d := b) (by omega), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨adc_carry _ _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2.2 h.symm)
    refine WP.mono (chainAdc_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `ts += [b]`, with the carry out. -/
theorem chainAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : Fresh (t :: ts)) :
    WP isa (.block (chain .add .adc (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat =
        regsVal s (t :: ts) + wordsVal s.mem base b (t :: ts).length ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chain, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .add t (.mem (sc b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat +
        (word s.mem base b).toNat)).toNat = (s.gpr t).toNat + (word s.mem base b).toNat ∧
      s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_sc hs (d := b) (by omega), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨add_carry _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2.2 h.symm)
  refine WP.mono (chainAdc_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega

/-- `ts -= [b] + c`, `sbb` throughout, with the borrow `c` in and out. -/
theorem chainSbb_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    Scr s base size → s.cf = some c → b + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (chain .sbb .sbb ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + wordsVal s.mem base b ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * c'.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .sbb t (.mem (sc b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + (word s.mem base b).toNat + c.toNat = (s.gpr t).toNat +
          2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)).toNat ∧
        s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_sc hs (d := b) (by omega), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      · have := sbb_borrow (s.gpr t) (word s.mem base b) c
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2.2 h.symm)
    refine WP.mono (chainSbb_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `ts -= [b]`, with the borrow out. -/
theorem chainSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : Fresh (t :: ts)) :
    WP isa (.block (chain .sub .sbb (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + wordsVal s.mem base b (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chain, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .sub t (.mem (sc b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + (word s.mem base b).toNat = (s.gpr t).toNat +
        2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat)).toNat ∧
      s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_sc hs (d := b) (by omega), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨sub_borrow _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2.2 h.symm)
  refine WP.mono (chainSbb_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega

end VG.Proof.Mont.X86_64
