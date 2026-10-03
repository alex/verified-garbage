import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy

/-!
# Short Weierstrass curves on x86-64: numbers to and from big-endian bytes

`loadBE n o src` reads the `8 n` bytes at `src`, big-endian, into `[o]`
(`loadBE_ok`), and `storeBE n dst d a` writes `[a]` masked with `rcx`, so the
number or zeros, big-endian, to the `8 n` bytes at `dst + d` (`storeBE_ok`):
a word at a time, each byte-reversed (`bswap`), from the last.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64

theorem ea_disp (s : State) (r : Reg) (e : Nat) :
    s.ea { base := r, disp := (e : Int) } = s.gpr r + BitVec.ofNat 64 e := by
  simp only [State.ea, BitVec.ofInt_natCast]

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 8 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 8 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

/-! ## Loads -/

/-- One word of `loadBE`. -/
def ldStep (n o : Nat) (src : Reg) (j : Nat) : List Instr :=
  [.mov .rax (.mem { base := src, disp := ((8 * (n - 1 - j) : Nat) : Int) }), .bswap .rax,
    .store (sc (o + 8 * j)) .rax]

theorem loadBE_eq (n o : Nat) (src : Reg) : loadBE n o src = (List.range n).flatMap (ldStep n o src) := rfl

theorem ldSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .rax) (ho : o + 8 * n ≤ size)
    (hr : ∀ d, d + 8 ≤ 8 * n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, 8 * n⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStep n o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) =
        bswap64 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - j))) 64)) ∧
      KeepRegs [.rax] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldSteps_ok hs hsrc ho hr hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 8 := by
      rw [k₁.rd, k₁.wr, hp₁]; exact hr _ (by omega)
    have hw : s₁.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 64 :=
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (show WP isa (.block (ldStep n o src k)) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (o + 8 * k))
          (bswap64 (s₁.mem.readW (s₁.gpr src + BitVec.ofNat 64 (8 * (n - 1 - k))) 64)) ∧
          KeepRegs [.rax] s₁ s₂) by
      apply WP.of_runBlock
      simp only [ldStep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        State.load64, State.store64, ea_disp, ea_sc, hr₁, RegUpd.gpr_setReg, RegUpd.wr_setReg,
        RegUpd.mem_setReg, reduceCtorEq, ite_true, ite_false, hs₁.rdi, st_sc hs₁ (d := o + 8 * k) (by omega),
        Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self, hp₁, hw]

/-- `[o] = ` the `8 n` bytes at `src`, big-endian. -/
theorem loadBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .rax) (ho : o + 8 * n ≤ size)
    (hr : ∀ d, d + 8 ≤ 8 * n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, 8 * n⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBE n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) (8 * n)) ∧
      KeepRegs [.rax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBE_eq]
  exact WP.mono (ldSteps_ok hs hsrc ho hr hd n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_eq_ofBytes _ _ _ _ o n e, k, O⟩

/-! ## Stores -/

/-- One word of `storeBE`. -/
def stStep (n : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx), .bswap .rax,
    .store { base := dst, disp := ((d + 8 * (n - 1 - j) : Nat) : Int) } .rax]

theorem storeBE_eq (n : Nat) (dst : Reg) (d a : Nat) :
    storeBE n dst d a = (List.range n).flatMap (stStep n dst d a) := rfl

theorem stSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .rax) {c : Bool} (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0))
    (ha : a + 8 * n ≤ size)
    (hw : ∀ e, e + 8 ≤ 8 * n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (stStep n dst d a))) s fun s' =>
      (∀ j < k, s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - j))) 64 =
        bswap64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      KeepRegs [.rax] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (8 * (n - k)) (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stSteps_ok hs hdst hc ha hw hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .rcx = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hq : s.gpr dst + BitVec.ofNat 64 (d + 8 * (n - 1 - k)) =
        s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - k)) := (Offset.add_add _ _ _).symm
    have hw₁ : InRegions s₁.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - k))) 8 := by
      rw [k₁.wr]; exact hw _ (by omega)
    have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (show WP isa (.block (stStep n dst d a k)) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * (n - 1 - k)))
          (bswap64 (word s₁.mem base (a + 8 * k) &&& (if c then BitVec.allOnes 64 else 0))) ∧
          KeepRegs [.rax] s₁ s₂) by
      apply WP.of_runBlock
      simp only [stStep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some, State.load64, State.store64, ea_disp, ea_sc, hs₁.rdi, ld_sc hs₁ (d := a + 8 * k) (by omega),
        RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
        RegUpd.mem_setReg, RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false, hdst, hq₁, hc₁, hq, hw₁,
        Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (8 * (n - 1 - k)) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, Mem.readW_writeW_self64, hword]

/-- The `8 n` bytes at `dst + d` are `[a]` big-endian if the mask `rcx` is all
ones (`c`), zeros if it is zero. -/
theorem storeBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .rax) (c : Bool) (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0))
    (ha : a + 8 * n ≤ size)
    (hw : ∀ e, e + 8 ≤ 8 * n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, 8 * n⟩) :
    WP isa (.block (storeBE n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) (8 * n) =
        (if c then Spec.Weierstrass.toBytes (8 * n) (wordsVal s.mem base a n)
          else List.replicate (8 * n) 0) ∧
      KeepRegs [.rax] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 (8 * n) s.mem s'.mem := by
  rw [storeBE_eq]
  refine WP.mono (stSteps_ok hs hdst hc ha hw hd n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨bytesAt_eq_toBytes _ _ _ _ c e, k, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero] at O
  exact O

end VG.Proof.Weierstrass.X86_64
