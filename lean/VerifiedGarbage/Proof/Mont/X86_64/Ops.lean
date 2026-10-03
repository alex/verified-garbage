import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-!
# Montgomery arithmetic on x86-64: the operations

For a modulus `m` in the working space (`ModOk`): `mul o a b` writes
`[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes `[a] + [b] mod m`
(`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`), for `[a]`, `[b]`
below `m`. Each changes only the registers `clob n`, the result and the
temporary area (`OpKeep`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the operations change. -/
def clob (n : Nat) : List Reg := .rax :: .rcx :: .rdx :: .rbp :: acc n

/-- The modulus `m`: its `n` words at `M.mo`, the temporary area at `M.tmp`,
in the working space and apart, and `M.minv = -m⁻¹ mod 2⁶⁴`. -/
structure ModOk (M : Mod) (size m : Nat) (mem : Mem) (base : Addr) : Prop where
  n0 : 0 < M.n
  n7 : M.n < 7
  mo : M.mo + 8 * M.n ≤ size
  tmp : M.tmp + 8 * M.n ≤ size
  sep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  val : wordsVal mem base M.mo M.n = m
  inv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, and the memory but `[o]` and the temporary area. -/
structure OpKeep (M : Mod) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (ofs base x < o ∨ o + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem m_pos {m B : Nat} (hB : B < m) : 0 < m := by omega

theorem fresh_low (n : Nat) (hn : n < 7) :
    Fresh (win n n n :: (List.range n).map (win n n)) := by
  have h := fresh_wins hn n
  rw [wins_split] at h
  refine ⟨?_, fun t ht => h.2 t ?_⟩
  · have hd := h.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hd
    exact List.nodup_cons.mpr ⟨fun hm => hd.2.2 _ hm _ (by simp) rfl, hd.1⟩
  · simp only [List.mem_cons, List.mem_append] at ht ⊢
    grind

theorem fresh_low' (n : Nat) (hn : n < 7) : Fresh ((List.range n).map (win n n)) :=
  (fresh_low n hn).tail

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  rw [mul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeros_ok s (acc M.n)) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (acc_regs_lt _ hM.n7 _ h).2.2.2.2 rfl)
  have h0 : regsVal s₁ (wins M.n 0) = 0 := regsVal_zero fun r hr => z₁ r (wins_sub_acc hM.n7 0 r hr)
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok hM.n7 ha hb hM.mo hM.inv M.n (Nat.le_refl _) hs₁
    (by rw [k₁.2.1]; exact hM.val) (by rw [k₁.2.1]; exact hB) h0) fun s₂ ⟨⟨U, eU⟩, hT, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (acc_regs_lt _ hM.n7 _ h).2.2.2.2 rfl)
  have hmem₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  rw [k₁.2.1] at eU
  -- The accumulator's value as `csub` sees it: its top word is zero.
  have hsplit := wins_split M.n M.n
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hlowlen : ((List.range M.n).map (win M.n M.n)).length = M.n := by simp
  have hV : regsVal s₂ ((List.range M.n).map (win M.n M.n)) +
      2 ^ (64 * M.n) * (s₂.gpr (win M.n M.n M.n)).toNat = regsVal s₂ (wins M.n M.n) := by
    rw [hsplit, regsVal_append, hlowlen]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [hsplit, regsVal_append, hlowlen] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₂.gpr (win M.n M.n (M.n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * ((s₂.gpr (win M.n M.n M.n)).toNat +
          2 ^ 64 * (s₂.gpr (win M.n M.n (M.n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₂ (M := M) (m := m) hlowlen hM.n0 (fresh_low M.n hM.n7) hM.mo hM.tmp hM.sep
    (by rw [hmem₂]; exact hM.val) (by rw [hV]; exact hT)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (fresh_low' M.n hM.n7).2 _ h |>.2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₃ (o := o) (by rw [hlowlen]; omega) (fresh_low' M.n hM.n7).1)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hlowlen] at e₄ O₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · rw [k₄.gpr r (by simp), k₃.gpr r (fun h => hr (by
      simp only [clob, List.mem_cons] at h ⊢
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hM.n7 M.n r (by
          rw [hsplit]; simp only [List.mem_append]; exact Or.inl h))))))),
      k₂.1 r (fun h => hr (by simpa [clob] using h)), k₁.1 r (fun h => hr (by
        simp only [clob, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr h)))))]
  · rw [k₄.rd, k₃.rd, k₂.2.2.1, k₁.2.2.1]
  · rw [k₄.wr, k₃.wr, k₂.2.2.2, k₁.2.2.2]
  · rw [O₄ x hx, O₃ x hx', hmem₂]
  · rw [e₄, e₃, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, e₃, hV, Nat.mod_mul_mod, Nat.mul_comm, eU, ← hmem₂]
    simp only [Nat.add_mul_mod_self_right]

/-! ## Addition and subtraction -/

theorem low_len_lt : ∀ n < 7, (low n).length = n := by decide

theorem low_nodup_lt : ∀ n < 7, (top n :: low n).Nodup := by decide

theorem low_regs_lt : ∀ n < 7, ∀ t ∈ top n :: low n, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx := by decide

theorem low_regs_lt' : ∀ n < 7, ∀ t ∈ top n :: low n, t ≠ .rbp ∧ t ≠ .rdi := by decide

theorem low_sub_acc_lt : ∀ n < 7, ∀ t ∈ top n :: low n, t ∈ acc n := by decide

theorem fresh_top_low {n : Nat} (hn : n < 7) : Fresh (top n :: low n) :=
  ⟨low_nodup_lt n hn, fun t ht =>
    have h := low_regs_lt n hn t ht
    have h' := low_regs_lt' n hn t ht
    ⟨h.1, h.2.1, h.2.2, h'.1, h'.2⟩⟩

theorem low_ne_nil {n : Nat} (hn : n < 7) (h0 : 0 < n) : ∃ t ts, low n = t :: ts := by
  have := low_len_lt n hn
  cases h : low n with
  | nil => rw [h] at this; simp at this; omega
  | cons t ts => exact ⟨t, ts, rfl⟩

theorem mov32zero_ok (s : State) (t : Reg) :
    WP isa (.block [.mov32 t (.imm 0)]) s fun s' => s'.gpr t = 0 ∧ s'.cf = s.cf ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.cf_setReg]
  refine ⟨rfl, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem adcZero_ok (s : State) (t : Reg) {c : Bool} (hc : s.cf = some c) (h0 : s.gpr t = 0) :
    WP isa (.block [.alu .adc t (.imm 0)]) s fun s' => (s'.gpr t).toNat = c.toNat ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left',
    VG.Proof.X25519.X86_64.se0, h0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have hf := fresh_top_low hM.n7
  have hl := low_len_lt M.n hM.n7
  obtain ⟨t, ts, hts⟩ := low_ne_nil hM.n7 hM.n0
  have hsub : ∀ r ∈ top M.n :: low M.n, r ∈ clob M.n := fun r hr => by
    simp only [clob, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (low_sub_acc_lt _ hM.n7 r hr))))
  rw [Impl.Mont.X86_64.add, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs (a := a) (by omega) hf.tail) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (mov32zero_ok s₁ (top M.n)) fun s₂ ⟨z₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by simp [(hf.2 _ (List.mem_cons_self ..)).2.2.2.2.symm])
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdd_ok hs₂ (b := b) (by rw [← hts]; omega) (hts ▸ hf.tail))
    fun s₃ ⟨c, c₃, e₃, k₃⟩ => ?_
  rw [← hts] at e₃ k₃ ⊢
  have hs₃ := hs₂.of_keeps k₃ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  have ht₃ : s₃.gpr (top M.n) = 0 := by
    rw [k₃.1 _ (List.nodup_cons.mp hf.1).1, z₂]
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₃ (top M.n) c₃ ht₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by simp [(hf.2 _ (List.mem_cons_self ..)).2.2.2.2.symm])
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₃ (low M.n) :=
    regsVal_congr fun q hq => k₄.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hR₂ : regsVal s₂ (low M.n) = regsVal s₁ (low M.n) :=
    regsVal_congr fun q hq => k₂.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hmem₄ : s₄.mem = s.mem := by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  rw [hl, hR₂, e₁, k₂.2.1, k₁.2.1] at e₃
  have hV : regsVal s₄ (low M.n) + 2 ^ (64 * M.n) * (s₄.gpr (top M.n)).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [hR₄, e₄, e₃, hl]
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₄ (M := M) (m := m) hl hM.n0 hf hM.mo hM.tmp hM.sep
    (by rw [hmem₄]; exact hM.val) (by rw [hV]; exact hAB)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hf.tail.2 _ h).2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega) hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₆ O₆
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · have hr' : r ∉ top M.n :: low M.n := fun h => hr (hsub r h)
    rw [k₆.gpr r (by simp), k₅.gpr r (fun h => hr (by
        simp only [List.mem_cons] at h
        rcases h with h | h | h
        · simp [clob, h]
        · simp [clob, h]
        · exact hsub r (List.mem_cons_of_mem _ h))),
      k₄.1 r (fun h => hr' (by simp at h; simp [h])), k₃.1 r (fun h => hr' (List.mem_cons_of_mem _ h)),
      k₂.1 r (fun h => hr' (by simp at h; simp [h])), k₁.1 r (fun h => hr' (List.mem_cons_of_mem _ h))]
  · rw [k₆.rd, k₅.rd, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.wr, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x hx, O₅ x hx', hmem₄]
  · rw [e₆, e₅, hV]

theorem sbbMask_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .rax (.reg .rax)]) s fun s' =>
      s'.gpr .rax = (if c then BitVec.allOnes 64 else 0) ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by cases c <;> simp, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[tmp] = [mo]` masked with `rax` (all ones if `c`, else zero), `k` words. -/
theorem masked_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {mo tmp : Nat} (c : Bool),
    Scr s base size → mo + 8 * k ≤ size → tmp + 8 * k ≤ size →
    (mo + 8 * k ≤ tmp ∨ tmp + 8 * k ≤ mo) → s.gpr .rax = (if c then BitVec.allOnes 64 else 0) →
    WP isa (.block (masked k mo tmp)) s fun s' =>
      wordsVal s'.mem base tmp k = (if c then wordsVal s.mem base mo k else 0) ∧
      KeepRegs [.rdx] s s' ∧ Outside base tmp (8 * k) s.mem s'.mem
  | 0, s, _, _, _, c, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, mo, tmp, c, hs, hmo, htmp, hsep, hx => by
    have hn := hs.nowrap
    rw [masked, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc mo)), .alu .and .rdx (.reg .rax),
        .store (sc tmp) .rdx]) s (fun s₁ => s₁.mem = s.mem.writeW (off base tmp)
          (if c then word s.mem base mo else 0) ∧ KeepRegs [.rdx] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs.rdi, ld_sc hs (d := mo) (by omega), st_sc hs (d := tmp) (by omega), hx,
        Option.some.injEq, exists_eq_left']
      refine ⟨by cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_allOnes,
        BitVec.and_zero, BitVec.ofNat_eq_ofNat], ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (masked_ok k c hs₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
      (by omega) (by rw [k₁.gpr _ (by decide), hx])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    rw [wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, e₂,
      O₁.wordsVal (by omega) (by omega)]
    cases c <;> simp [wordsVal]

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have hf := fresh_top_low hM.n7
  have hl := low_len_lt M.n hM.n7
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have htmp := hM.tmp
  obtain ⟨t, ts, hts⟩ := low_ne_nil hM.n7 hM.n0
  have hsub : ∀ r ∈ low M.n, r ∈ clob M.n := fun r hr => by
    simp only [clob, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (low_sub_acc_lt _ hM.n7 r (List.mem_cons_of_mem _ hr)))))
  rw [Impl.Mont.X86_64.sub, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs (a := a) (by omega) hf.tail) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainSub_ok hs₁ (b := b) (by rw [← hts]; omega) (hts ▸ hf.tail))
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  rw [← hts] at e₂ k₂ ⊢
  have hs₂ := hs₁.of_keeps k₂ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masked_ok M.n c hs₃ (mo := M.mo) (tmp := M.tmp) hM.mo hM.tmp hM.sep x₃)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdd_ok hs₄ (b := M.tmp) (by rw [← hts]; omega) (hts ▸ hf.tail))
    fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  rw [← hts] at e₅ k₅ ⊢
  have hs₅ := hs₄.of_keeps k₅ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega) hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₂ e₅ e₆ O₆
  have hmem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₂ (low M.n) := by
    rw [regsVal_congr fun q hq => k₄.gpr q (by simp [(hf.tail.2 q hq).2.2.1]),
      regsVal_congr fun q hq => k₃.1 q (by simp [(hf.tail.2 q hq).1])]
  rw [hR₄, e₄, hmem₃, hM.val] at e₅
  rw [e₁, k₁.2.1] at e₂
  have hmem₄ : ∀ x, (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s₄.mem x = s.mem x :=
    fun x hx => by rw [O₄ x hx, hmem₃]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · have hr' : r ∉ low M.n := fun h => hr (hsub r h)
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.gpr r (fun h => hr (by simp at h; simp [clob, h])),
      k₃.1 r (fun h => hr (by simp at h; simp [clob, h])), k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x hx, k₅.2.1, hmem₄ x hx']
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low M.n)
    have hR₅ := regsVal_lt s₅ (low M.n)
    rw [hl] at hR₂ hR₅
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅
    · rw [show wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n =
        (wordsVal s.mem base a M.n - wordsVal s.mem base b M.n) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega

end VG.Proof.Mont.X86_64
