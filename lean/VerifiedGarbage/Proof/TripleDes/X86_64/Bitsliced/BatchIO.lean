import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Copy
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Transpose

/-!
# The start and end of a batch

The batch's size (`batchSize`), the copies of its blocks into and out of
the state words (`copyIn`, `copyOut`), counting the passes
(`passesStart`), and the advance of the data pointer and the count of
blocks left (`batchEnd`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-! ## Storing registers in scratch slots -/

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < 128)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => st p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, sl s' p.1 = s.gpr p.2) ∧ (∀ x < 128, (∀ p ∈ l, p.1 ≠ x) → sl s' x = sl s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := { s with mem := stMem s p.1 (s.gpr p.2) }
    have h₁ : Room s₁ := h.congr rfl rfl
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', zf', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', zf', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)),
          sl_st s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)),
        sl_st s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-! ## The batch's size -/

theorem batchSize_ok {s : State} (h : Room s) :
    WP isa batchSize s (fun s' => sl s' batchSlot = BitVec.ofNat 64 (min (sl s leftSlot).toNat 64) ∧
      (∀ x < 128, x ≠ batchSlot → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
  let m := sl s leftSlot
  let s₁ := s.setReg .rax m
  have e₁ : exec (ld .rax leftSlot) s = some s₁ := exec_ld h (by decide) .rax
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (64 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((64 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((64 : BitVec 32).signExtend 64) (s₁.gpr .rax - (64 : BitVec 32).signExtend 64))
  have run₁ : runBlock isa [ld .rax leftSlot, .alu .cmp .rax (.imm 64)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, cmp_run]
  have rax₁ : t₁.gpr .rax = m := by simp [t₁, s₁, gpr_setReg]
  have cf₁ : t₁.cf = some (decide (m.toNat < 64)) := by
    simp only [t₁, cf_arithFlags, s₁, gpr_setReg_self]; rfl
  have ht₁ : Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg]) (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  -- the value of `rax` after the branch, and the rest
  have finish : ∀ t : State, Room t → t.gpr .rax = BitVec.ofNat 64 (min m.toNat 64) →
      (∀ x < 128, sl t x = sl s x) → t.gpr .rcx = s.gpr .rcx → t.gpr .rsp = s.gpr .rsp →
      t.rd = s.rd → t.wr = s.wr → Frame [scratchR s] s.mem t.mem →
      WP isa (.block [st batchSlot .rax]) t (fun s' =>
        sl s' batchSlot = BitVec.ofNat 64 (min (sl s leftSlot).toNat 64) ∧
        (∀ x < 128, x ≠ batchSlot → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
        s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
    intro t ht hrax hsl hc hsp hrd hwr hf
    have e := exec_st (r := Reg.rax) ht (by decide : batchSlot < 128)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine ⟨?_, fun x hx hne => ?_, hc, hsp, hrd, hwr, ?_⟩
    · rw [sl_st t (by decide) _ (by decide)]; simp [hrax, m]
    · rw [sl_st t (by decide) _ hx]; simp [hne, hsl x hx]
    · have f := stMem_frame (s := t) (by decide : batchSlot < 128) (t.gpr .rax)
      rw [show scratchR t = scratchR s by simp only [scratchR, hc]] at f
      exact hf.trans f
  have sl₁ : ∀ x < 128, sl t₁ x = sl s x := by
    intro x _; simp only [t₁, sl_arithFlags, s₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  have c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  have sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  have rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  have wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  have f₁ : Frame [scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  apply WP.seq
  apply WP.ite (decide (m.toNat < 64)) cf₁
  · intro hlt
    apply WP.block_nil
    refine finish t₁ ht₁ ?_ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    rw [rax₁]
    have : m.toNat < 64 := by simpa using hlt
    rw [Nat.min_eq_left (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro hge
    have : ¬ m.toNat < 64 := by simpa using hge
    have e := exec_movImm t₁ .rax 64
    let t₂ := t₁.setReg .rax ((64 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨t₂, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine finish t₂ (ht₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])) ?_
      (fun x hx => by simp only [t₂, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]; exact sl₁ x hx)
      (by simp [t₂, gpr_setReg, c₁]) (by simp [t₂, gpr_setReg, sp₁]) (by simp [t₂, rd_setReg, rd₁])
      (by simp [t₂, wr_setReg, wr₁]) (by simp only [t₂, mem_setReg]; exact f₁)
    rw [Nat.min_eq_right (by omega)]
    simp [t₂, gpr_setReg]

/-! ## Copying the batch in and out -/

/-- The state words' area. -/
abbrev stateA (s : State) : Addr := wAt (s.gpr .rcx) 8

theorem wAt_stateA (c : Addr) (j : Nat) : wAt (wAt c 8) j = wordAddr c (stSlot j) := by
  simp only [wAt, wordAddr, stSlot, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

/-- What the prologue of the copies leaves: the public words in `r8`–`r11`,
the data pointer in `rsi`, the state's in `rdi`, the count in `rdx`. -/
structure KeepPost (s t : State) : Prop where
  r8 : t.gpr .r8 = sl s schedSlot
  r9 : t.gpr .r9 = sl s dataSlot
  r10 : t.gpr .r10 = sl s leftSlot
  r11 : t.gpr .r11 = sl s batchSlot
  rsi : t.gpr .rsi = sl s dataSlot
  rdi : t.gpr .rdi = stateA s
  rdx : t.gpr .rdx = sl s batchSlot
  rcx : t.gpr .rcx = s.gpr .rcx
  rsp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem keep_ok {s : State} (h : Room s) :
    ∃ t, runBlock isa (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]) s
      = some t ∧ KeepPost s t := by
  let t₁ := s.setReg .r8 (sl s schedSlot)
  let t₂ := t₁.setReg .r9 (sl s dataSlot)
  let t₃ := t₂.setReg .r10 (sl s leftSlot)
  let t₄ := t₃.setReg .r11 (sl s batchSlot)
  let t₅ := t₄.setReg .rsi (sl s dataSlot)
  let t₆ := t₅.setReg .rdi (s.gpr .rcx)
  have e₁ : exec (ld .r8 schedSlot) s = some t₁ := exec_ld h (by decide) .r8
  have h₁ : Room t₁ := h.congr (by simp [t₁, gpr_setReg]) (by simp [t₁, wr_setReg])
  have e₂ : exec (ld .r9 dataSlot) t₁ = some t₂ := by
    rw [exec_ld h₁ (by decide) .r9, sl_setReg _ (by decide)]
  have h₂ : Room t₂ := h₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])
  have e₃ : exec (ld .r10 leftSlot) t₂ = some t₃ := by
    rw [exec_ld h₂ (by decide) .r10, sl_setReg _ (by decide), sl_setReg _ (by decide)]
  have h₃ : Room t₃ := h₂.congr (by simp [t₃, gpr_setReg]) (by simp [t₃, wr_setReg])
  have e₄ : exec (ld .r11 batchSlot) t₃ = some t₄ := by
    rw [exec_ld h₃ (by decide) .r11, sl_setReg _ (by decide), sl_setReg _ (by decide),
      sl_setReg _ (by decide)]
  have e₅ : exec (rr .rsi .r9) t₄ = some t₅ := by
    simp only [rr, exec, readSrc, Option.map_some, t₅]
    simp [t₄, t₃, t₂, gpr_setReg]
  have e₆ : exec (rr .rdi .rcx) t₅ = some t₆ := by
    simp only [rr, exec, readSrc, Option.map_some, t₆]
    simp [t₅, t₄, t₃, t₂, t₁, gpr_setReg]
  have e₇ := exec_addImm t₆ .rdi 64
  let t₇ := (arithFlags t₆ (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (t₆.gpr .rdi).toNat + ((64 : BitVec 32).signExtend 64).toNat))
      (addOverflow (t₆.gpr .rdi) ((64 : BitVec 32).signExtend 64)
        (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64))).setReg .rdi
      (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
  let t₈ := t₇.setReg .rdx (t₇.gpr .r11)
  have e₈ : exec (rr .rdx .r11) t₇ = some t₈ := rfl
  refine ⟨t₈, ?_, ?_⟩
  · simp only [keepIn, List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
        mem_arithFlags, rd_arithFlags, wr_arithFlags, stateA, wAt]

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

/-- The data words of the batch: readable and writable, apart from the scratch buffer. -/
structure DataOk (s : State) (D : Addr) (k : Nat) : Prop where
  read : ∀ i < k, InRegions (s.rd ++ s.wr) (wAt D i) 8
  write : ∀ i < k, InRegions s.wr (wAt D i) 8
  sep : (⟨D, 8 * k⟩ : Region).Disjoint (scratchR s)
  fit : 8 * k < 2 ^ 64

theorem state_in (s : State) {k : Nat} (hk : k ≤ 64) :
    Region.Sub ⟨stateA s, 8 * k⟩ (scratchR s) := by
  simp only [stateA, wAt, scratchR]
  exact Offset.sub_base _ (by omega)

theorem copyIn_ok {s : State} (h : Room s) {k : Nat} (hk : sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : DataOk s (sl s dataSlot) k) :
    WP isa copyIn s (fun s' => (∀ j < k, words s' j = s.mem.readW (wAt (sl s dataSlot) j) 64) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
  obtain ⟨t, run, kp⟩ := keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  apply WP.seq
  have pre : CopyPre (sl s dataSlot) (stateA s) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr]; exact hd.read i hi
    · rw [kp.wr, stateA, wAt_stateA]
      exact ⟨scratchR s, h.scratch, slot_in_scratch s (by unfold stSlot; omega)⟩
    · exact (hd.sep.sub_right (state_in s h64))
  have inv : CopyInv .rsi .rdi (sl s dataSlot) (stateA s) k t 0 t := by
    refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rsi, wAt_zero]
    · rw [kp.rdi, wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (copy_ok (Or.inl ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  have hu : Room u := h.congr (by rw [pu.regs _ (by decide) (by decide) (by decide) (by decide), kp.rcx])
    (by rw [pu.wr, kp.wr])
  have r8 := pu.regs .r8 (by decide) (by decide) (by decide) (by decide)
  have r9 := pu.regs .r9 (by decide) (by decide) (by decide) (by decide)
  have r10 := pu.regs .r10 (by decide) (by decide) (by decide) (by decide)
  have r11 := pu.regs .r11 (by decide) (by decide) (by decide) (by decide)
  have rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  have rsp := pu.regs .rsp (by decide) (by decide) (by decide) (by decide)
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ := stores_ok hu
    [(schedSlot, .r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)] (by decide) (by decide)
  refine WP.of_runBlock ⟨v, runv, ?_⟩
  have ufr : Frame [scratchR s] s.mem u.mem := by
    rw [← kp.mem]
    exact pu.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scratchR s, List.mem_singleton_self _, state_in s h64⟩
  have slu : ∀ x < 128, 72 ≤ x → sl u x = sl s x := by
    intro x hx hl
    simp only [sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [stateA, wAt, wordAddr]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have wu : ∀ j < k, words u j = s.mem.readW (wAt (sl s dataSlot) j) 64 := by
    intro j hj
    have e := pu.copied j hj
    rw [stateA, wAt_stateA, kp.mem] at e
    simp only [words, sl, rcx, kp.rcx]
    exact e
  have notIn : ∀ x, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → x ≠ batchSlot →
      ∀ p ∈ [(schedSlot, Reg.r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)], p.1 ≠ x := by
    intro x a b c d p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b;
      exact Ne.symm c; exact Ne.symm d]
  have cu : u.gpr .rcx = s.gpr .rcx := rcx.trans kp.rcx
  refine ⟨fun j hj => ?_, fun x hx hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [words]
    rw [keepv _ (by unfold stSlot; omega) (notIn _ (by unfold stSlot schedSlot; omega)
      (by unfold stSlot dataSlot; omega) (by unfold stSlot leftSlot; omega)
      (by unfold stSlot batchSlot; omega))]
    exact wu j hj
  · by_cases a : x = schedSlot
    · subst a; rw [setv (schedSlot, .r8) (by simp), r8, kp.r8]
    by_cases b : x = dataSlot
    · subst b; rw [setv (dataSlot, .r9) (by simp), r9, kp.r9]
    by_cases c : x = leftSlot
    · subst c; rw [setv (leftSlot, .r10) (by simp), r10, kp.r10]
    by_cases d : x = batchSlot
    · subst d; rw [setv (batchSlot, .r11) (by simp), r11, kp.r11]
    rw [keepv x hx (notIn x a b c d), slu x hx hl]
  · rw [gv, cu]
  · rw [gv, rsp, kp.rsp]
  · rw [rdv, pu.rd, kp.rd]
  · rw [wrv, pu.wr, kp.wr]
  · rw [show scratchR u = scratchR s by simp only [scratchR, cu]] at fv
    exact ufr.trans fv

structure OutPost (s : State) (k : Nat) (s' : State) : Prop where
  data : ∀ j < k, s'.mem.readW (wAt (sl s dataSlot) j) 64 = words s j
  slots : ∀ x < 128, sl s' x = sl s x
  r8 : s'.gpr .r8 = sl s schedSlot
  r10 : s'.gpr .r10 = sl s leftSlot
  r11 : s'.gpr .r11 = sl s batchSlot
  rsi : s'.gpr .rsi = wAt (sl s dataSlot) k
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨sl s dataSlot, 8 * k⟩] s.mem s'.mem

theorem copyOut_ok {s : State} (h : Room s) {k : Nat} (hk : sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : DataOk s (sl s dataSlot) k) :
    WP isa copyOut s (OutPost s k) := by
  obtain ⟨t, run, kp⟩ := keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  have pre : CopyPre (stateA s) (sl s dataSlot) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr, stateA, wAt_stateA]
      exact ⟨scratchR s, List.mem_append_right _ h.scratch, slot_in_scratch s (by unfold stSlot; omega)⟩
    · rw [kp.wr]; exact hd.write i hi
    · exact (hd.sep.sub_right (state_in s h64)).symm
  have inv : CopyInv .rdi .rsi (stateA s) (sl s dataSlot) k t 0 t := by
    refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rdi, wAt_zero]
    · rw [kp.rsi, wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (copy_ok (Or.inr ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  have rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun j hj => ?_, fun x hx => ?_, ?_, ?_, ?_, pu.dst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pu.copied j hj, kp.mem, stateA, wAt_stateA]; rfl
  · simp only [sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sep.sub_right (Offset.sub_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 1024)
      (by omega))).symm
  · rw [pu.regs .r8 (by decide) (by decide) (by decide) (by decide), kp.r8]
  · rw [pu.regs .r10 (by decide) (by decide) (by decide) (by decide), kp.r10]
  · rw [pu.regs .r11 (by decide) (by decide) (by decide) (by decide), kp.r11]
  · rw [rcx, kp.rcx]
  · rw [pu.regs .rsp (by decide) (by decide) (by decide) (by decide), kp.rsp]
  · rw [pu.rd, kp.rd]
  · rw [pu.wr, kp.wr]
  · rw [← kp.mem]; exact pu.frame

/-! ## The end of a batch -/

theorem batchEnd_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa batchEnd s = some s' ∧ sl s' schedSlot = s.gpr .r8 ∧
      sl s' dataSlot = s.gpr .rsi ∧ sl s' leftSlot = s.gpr .r10 - s.gpr .r11 ∧
      s'.zf = some (s.gpr .r10 - s.gpr .r11 == 0) ∧
      (∀ x < 128, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → sl s' x = sl s x) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ :=
    stores_ok h [(schedSlot, .r8), (dataSlot, .rsi)] (by decide) (by decide)
  have hv : Room v := h.congr (by rw [gv]) wrv
  let d := s.gpr .r10 - s.gpr .r11
  let v₁ := v.setReg .rax (v.gpr .r10)
  have e₁ : exec (rr .rax .r10) v = some v₁ := rfl
  let v₂ := (arithFlags v₁ (v₁.gpr .rax - v₁.gpr .r11) (decide ((v₁.gpr .rax).toNat < (v₁.gpr .r11).toNat))
    (subOverflow (v₁.gpr .rax) (v₁.gpr .r11) (v₁.gpr .rax - v₁.gpr .r11))).setReg .rax
    (v₁.gpr .rax - v₁.gpr .r11)
  have e₂ : exec (.alu .sub .rax (.reg .r11)) v₁ = some v₂ := rfl
  have h₂ : Room v₂ := hv.congr (by simp [v₂, v₁, gpr_setReg]) (by simp [v₂, v₁, wr_setReg, wr_arithFlags])
  have e₃ := exec_st (r := Reg.rax) h₂ (by decide : leftSlot < 128)
  have rax₂ : v₂.gpr .rax = d := by simp [v₂, v₁, gpr_setReg, gv, d]
  refine ⟨{ v₂ with mem := stMem v₂ leftSlot (v₂.gpr .rax) }, ?_, ?_, ?_, ?_, ?_, fun x hx a b c => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show runBlock isa ([st schedSlot .r8, st dataSlot .rsi] ++
      ([rr .rax .r10, .alu .sub .rax (.reg .r11), st leftSlot .rax] : List Instr)) s = _
    exact runBlock_cat_some runv (by
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
        runStep_some, runBlock_nil])
  · rw [sl_st v₂ (by decide) _ (by decide)]
    simp only [show schedSlot ≠ leftSlot by decide, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      sl_arithFlags]
    rw [setv (schedSlot, .r8) (by simp)]
  · rw [sl_st v₂ (by decide) _ (by decide)]
    simp only [show dataSlot ≠ leftSlot by decide, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      sl_arithFlags]
    rw [setv (dataSlot, .rsi) (by simp)]
  · rw [sl_st v₂ (by decide) _ (by decide)]; simp only [ite_true, rax₂, d]
  · simp [v₂, v₁, gpr_setReg, gv]
  · rw [sl_st v₂ (by decide) _ hx]
    simp only [c, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx), sl_arithFlags]
    exact keepv x hx (by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b])
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, rd_setReg, rd_arithFlags, rdv]
  · simp [v₂, v₁, wr_setReg, wr_arithFlags, wrv]
  · have f := stMem_frame (s := v₂) (by decide : leftSlot < 128) (v₂.gpr .rax)
    rw [show scratchR v₂ = scratchR s by simp [scratchR, v₂, v₁, gpr_setReg, gv]] at f
    have m₂ : v₂.mem = v.mem := by simp [v₂, v₁, mem_setReg, mem_arithFlags]
    rw [m₂] at f
    exact fv.trans f

end VG.Proof.TripleDes.X86_64.Bitsliced
