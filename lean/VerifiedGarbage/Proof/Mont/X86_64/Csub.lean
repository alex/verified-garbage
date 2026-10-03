import VerifiedGarbage.Proof.Mont.X86_64.Rounds

/-!
# Montgomery arithmetic on x86-64: the conditional subtraction

`csub M ts top` reduces `V = ts + 2^(64 n) top < 2m` below `m`
(`csub_ok`): the difference `V - m` is computed word by word into the
temporary area (`diffs`), its borrow becomes a mask (`rax`, all ones if
`V ≥ m`), and the mask selects the difference (`selects`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 sub_borrow sbb_borrow toNat_ofBool)

/-- The registers but `rs` and the regions are unchanged (memory may change). -/
structure KeepRegs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem KeepRegs.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepRegs rs s₁ s₂)
    (h₂ : KeepRegs rs s₂ s₃) : KeepRegs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem KeepRegs.mono {rs rs' : List Reg} {s s' : State} (h : KeepRegs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeepRegs rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Keeps.regs {rs : List Reg} {s s' : State} (h : Keeps rs s s') : KeepRegs rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem Scr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : KeepRegs rs s s') (hr : .rdi ∉ rs) : Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-! ## The differences -/

/-- One word of the difference: `[tmp] = t - [mo] - c` (`op` is `sub`, with
no borrow in, or `sbb`). -/
theorem diff1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    {op : AluOp} {c : Bool}
    (hop : (op = .sub ∧ c = false) ∨ (op = .sbb ∧ s.cf = some c)) {mo tmp : Nat}
    (hmo : mo + 8 ≤ size) (htmp : tmp + 8 ≤ size) :
    WP isa (.block [.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax]) s
      fun s' => (word s'.mem base tmp).toNat + (word s.mem base mo).toNat + c.toNat =
          (s.gpr t).toNat + 2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base mo).toNat +
            c.toNat)).toNat ∧
        s'.cf = some (decide ((s.gpr t).toNat < (word s.mem base mo).toNat + c.toNat)) ∧
        KeepRegs [.rax] s s' ∧ s'.mem = s.mem.writeW (off base tmp) (word s'.mem base tmp) := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, ld_sc hs hmo, st_sc hs htmp]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      word_writeW_self, Bool.toNat_false, Nat.add_zero]
    refine ⟨sub_borrow _ _, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
      ite_false, hs.rdi, ld_sc hs hmo, st_sc hs htmp, RegUpd.cf_setReg, hc]
    simp only [Option.some.injEq, exists_eq_left', RegUpd.cf_arithFlags, word_writeW_self]
    refine ⟨?_, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    · have := sbb_borrow (s.gpr t) (word s.mem base mo) c
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`c` in, into the words at `tmp`, and its borrow out. -/
theorem diffsSbb_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {c : Bool}
    {mo tmp : Nat}, Scr s base size → s.cf = some c → mo + 8 * ts.length ≤ size →
    tmp + 8 * ts.length ≤ size → (mo + 8 * ts.length ≤ tmp ∨ tmp + 8 * ts.length ≤ mo) → Fresh ts →
    WP isa (.block (diffs .sbb ts mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp ts.length + wordsVal s.mem base mo ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * b.toNat ∧
      KeepRegs [.rax] s s' ∧ Outside base tmp (8 * ts.length) s.mem s'.mem
  | [], s, _, c, _, _, _, hc, _, _, _, _ => WP.block_nil ⟨c, hc, by simp [wordsVal, regsVal],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, c, mo, tmp, hs, hc, hmo, htmp, hsep, hf => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hmo htmp hsep
    rw [diffs, WP.block_append_iff]
    refine WP.mono (diff1_ok hs t (.inr ⟨rfl, hc⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
      fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
      (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
    have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
      O₁.wordsVal (by omega) (by omega)
    have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
    rw [hR, hM] at e₂
    refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
    · simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hT]
      rw [Nat.mul_assoc]
      omega
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

/-- The difference of the words `ts` and the words at `mo` into the words at
`tmp`, and its borrow. -/
theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {mo tmp : Nat} (hmo : mo + 8 * (t :: ts).length ≤ size)
    (htmp : tmp + 8 * (t :: ts).length ≤ size)
    (hsep : mo + 8 * (t :: ts).length ≤ tmp ∨ tmp + 8 * (t :: ts).length ≤ mo)
    (hf : Fresh (t :: ts)) :
    WP isa (.block (diffs .sub (t :: ts) mo tmp)) s fun s' => ∃ b : Bool, s'.cf = some b ∧
      wordsVal s'.mem base tmp (t :: ts).length + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * b.toNat ∧
      KeepRegs [.rax] s s' ∧ Outside base tmp (8 * (t :: ts).length) s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.length_cons] at hmo htmp hsep ⊢
  rw [diffs, WP.block_append_iff]
  refine WP.mono (diff1_ok hs t (.inl ⟨rfl, rfl⟩) (mo := mo) (tmp := tmp) (by omega) (by omega))
    fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have O₁ : Outside base tmp 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (diffsSbb_ok ts hs₁ c₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
    (by omega) hf.tail) fun s₂ ⟨b, c₂, e₂, k₂, O₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.tail.2 q hq).1)
  have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
    O₁.wordsVal (by omega) (by omega)
  have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
  rw [hR, hM] at e₂
  refine ⟨b, c₂, ?_, k₁.trans k₂, fun x hx => ?_⟩
  · simp only [wordsVal, regsVal, pow64_succ, hT]
    simp only [Bool.toNat_false, Nat.add_zero] at e₁ e₂ ⊢
    rw [Nat.mul_assoc]
    omega
  · rw [O₂ x (by omega), O₁ x (by omega)]

/-! ## The mask and the selection -/

theorem mask_val (x : BitVec 64) (c : Bool) :
    (x - x - (BitVec.ofBool c).setWidth 64) ^^^ BitVec.signExtend 64 (-1 : BitVec 32) =
      if c then 0 else BitVec.allOnes 64 := by
  cases c <;> simp

/-- The top word less the borrow `b`, and its borrow as a mask: all ones if
it does not borrow. -/
theorem mask_ok (s : State) (top : Reg) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.mov .rax (.reg top), .alu .sbb .rax (.imm 0), .alu .sbb .rax (.reg .rax),
      .alu .xor .rax (.imm (-1))]) s fun s' =>
      s'.gpr .rax = (if (s.gpr top).toNat < b.toNat then 0 else BitVec.allOnes 64) ∧
      Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, ite_true, hb, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [mask_val]
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [h0, Nat.zero_add, decide_eq_true_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem select_val (t d : BitVec 64) (k : Bool) :
    t ^^^ ((d ^^^ t) &&& (if k then 0 else BitVec.allOnes 64)) = if k then t else d := by
  cases k
  · simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.and_allOnes, BitVec.xor_comm d t, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]
  · simp

/-- Each word of `ts` replaced by the word at `tmp` if the mask `rax` is all
ones (`k` false), and kept if it is zero (`k` true). -/
theorem selects_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {tmp : Nat} (k : Bool),
    Scr s base size → tmp + 8 * ts.length ≤ size → Fresh ts →
    s.gpr .rax = (if k then 0 else BitVec.allOnes 64) →
    WP isa (.block (selects ts tmp)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else wordsVal s.mem base tmp ts.length) ∧
      Keeps (.rdx :: ts) s s'
  | [], s, _, _, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, tmp, k, hs, htmp, hf, hk => by
    obtain ⟨htn, hta, -, htd, -, -⟩ := hf.head
    simp only [List.length_cons] at htmp
    rw [selects, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc tmp)), .alu .xor .rdx (.reg t),
        .alu .and .rdx (.reg .rax), .alu .xor t (.reg .rdx)]) s (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else word s.mem base tmp) ∧ Keeps [.rdx, t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
        Option.map_some, Option.bind_some, load_sc hs (d := tmp) (by omega), RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', htd, ite_false, hk,
        reduceCtorEq]
      refine ⟨select_val _ _ k, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, fun h => hf.head.2.2.2.2.2 h.symm⟩)
    have hk₁ : s₁.gpr .rax = (if k then 0 else BitVec.allOnes 64) := by
      rw [k₁.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, Ne.symm hta⟩), hk]
    refine WP.mono (selects_ok ts k hs₁ (tmp := tmp + 8) (by omega) hf.tail hk₁) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(hf.tail.2 q hq).2.2.1, fun h => htn (h ▸ hq)⟩)
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t (by simp [htn, htd])
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [regsVal, ht₂, e₁, e₂, hR, k₁.2.1]
    cases k <;> rfl

/-! ## The conditional subtraction -/

/-- What `csub` computes: the number `T + X top < 2m` below `m`, given its
difference with `m`, `D + m = T + X b`, and the selection by the borrow. -/
theorem csub_arith {T D top X m : Nat} {b : Bool} (hX : m < X) (hD : D < X)
    (hV : T + X * top < 2 * m) (he : D + m = T + X * b.toNat) :
    (if top < b.toNat then T else D) = (T + X * top) % m := by
  have htop : top ≤ 1 := by
    rcases Nat.lt_or_ge top 2 with h | h
    · omega
    · have : X * 2 ≤ X * top := Nat.mul_le_mul_left _ h
      omega
  rcases (by omega : top = 0 ∨ top = 1) with rfl | rfl <;> cases b <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at he hV ⊢
  · simp only [Nat.lt_irrefl, ite_false]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Nat.zero_lt_one, ite_true]
    rw [Nat.mod_eq_of_lt (by omega)]
  · omega
  · simp only [Nat.lt_irrefl, ite_false]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- `csub`: `ts + 2^(64 n) top < 2m` reduced modulo `m`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (hf : Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hsep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo) {m : Nat}
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csub M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      KeepRegs (.rax :: .rdx :: ts) s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csub, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffs_ok hs (mo := M.mo) (tmp := M.tmp) (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [hlen]; omega) hft) fun s₁ ⟨b, c₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok s₁ top c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by simp [htop.2.1])
  rw [htop₁] at x₂
  refine WP.mono (selects_ok _ (decide ((s.gpr top).toNat < b.toNat)) hs₂ (tmp := M.tmp)
    (by rw [hlen]; omega) hft (by rw [x₂]; simp only [decide_eq_true_eq]))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.1 q (by simp [(hft.2 q hq).1])]
    exact regsVal_congr fun q hq => k₁.gpr q (by simp [(hft.2 q hq).1])
  rw [hlen] at e₁ e₃
  rw [hm] at e₁
  rw [k₂.2.1] at e₃
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (((Keeps.regs k₂).mono (by sub_regs)).trans
    ((Keeps.regs k₃).mono (by sub_regs))), fun x hx => ?_⟩
  · rw [e₃, hR₂]
    simp only [decide_eq_true_eq]
    exact csub_arith (b := b) hmX (wordsVal_lt _ _ _ _) hV e₁
  · rw [k₃.2.1, k₂.2.1, O₁ x (by rw [hlen]; exact hx)]

end VG.Proof.Mont.X86_64
