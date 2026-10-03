import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Impl.AesGcm.X86_64.Blocks

/-!
# AES-GCM on whole blocks, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `C`, `Y`, `D`, `n`, `S`), their regions, and the facts of
`blocksPre` by name (`BP`); the entry, which keeps the arguments in
`scratch` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev C : Addr := s.gpr .rdx
abbrev Y : Addr := s.gpr .rcx
abbrev D : Addr := s.gpr .r8
abbrev n : Nat := (s.gpr .r9).toNat
abbrev S : Addr := stackArg s 0
abbrev SP : Addr := s.gpr .rsp
abbrev kR : Region := ⟨K s, 256⟩
abbrev cR : Region := ⟨C s, 16⟩
abbrev yR : Region := ⟨Y s, 16⟩
abbrev dR : Region := ⟨D s, n s * 16⟩
abbrev sR : Region := ⟨S s, 2112⟩
/-- The stack argument `scratch`. -/
abbrev aR : Region := ⟨SP s + BitVec.ofNat 64 8, 8⟩
/-- What the code writes: the counter, `Y`, the data and `scratch`. -/
abbrev wR : List Region := [cR s, yR s, dR s, sR s]

end

/-- `blocksPre`, by name. -/
structure BP (s : State) : Prop where
  rd : s.rd = [kR s, aR s]
  wr : s.wr = wR s
  k_c : (kR s).Disjoint (cR s)
  k_y : (kR s).Disjoint (yR s)
  k_d : (kR s).Disjoint (dR s)
  k_s : (kR s).Disjoint (sR s)
  c_y : (cR s).Disjoint (yR s)
  c_d : (cR s).Disjoint (dR s)
  c_s : (cR s).Disjoint (sR s)
  c_a : (cR s).Disjoint (aR s)
  y_d : (yR s).Disjoint (dR s)
  y_s : (yR s).Disjoint (sR s)
  y_a : (yR s).Disjoint (aR s)
  d_s : (dR s).Disjoint (sR s)
  d_a : (dR s).Disjoint (aR s)
  s_a : (sR s).Disjoint (aR s)
  r_c : (⟨SP s, 8⟩ : Region).Disjoint (cR s)
  r_y : (⟨SP s, 8⟩ : Region).Disjoint (yR s)
  r_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  r_s : (⟨SP s, 8⟩ : Region).Disjoint (sR s)
  t_k : (below (SP s) 8).Disjoint (kR s)
  t_c : (below (SP s) 8).Disjoint (cR s)
  t_y : (below (SP s) 8).Disjoint (yR s)
  t_d : (below (SP s) 8).Disjoint (dR s)
  t_s : (below (SP s) 8).Disjoint (sR s)
  w_k : (K s).toNat + 256 ≤ 2 ^ 64
  w_c : (C s).toNat + 16 ≤ 2 ^ 64
  w_y : (Y s).toNat + 16 ≤ 2 ^ 64
  w_d : (D s).toNat + n s * 16 ≤ 2 ^ 64
  w_s : (S s).toNat + 2112 ≤ 2 ^ 64
  w_sp : (SP s).toNat + 16 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

theorem BP.of {s : State} (h : Proof.AesGcm.blocksPre s) : BP s := by
  simp only [Proof.AesGcm.blocksPre, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at h
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩ := h
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩

/-! ## The arguments kept -/

/-- The arguments kept in `scratch` at `S`: the data and the number of blocks
of what is left after `q` blocks. -/
structure Kept (s : State) (q : Nat) (m : Mem) : Prop where
  ctx : m.readW (S s) 64 = K s
  rounds : m.readW (S s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  ctr : m.readW (S s + BitVec.ofNat 64 16) 64 = C s
  y : m.readW (S s + BitVec.ofNat 64 24) 64 = Y s
  data : m.readW (S s + BitVec.ofNat 64 32) 64 = D s + BitVec.ofNat 64 (16 * q)
  n : m.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s - q)

/-- The slots of the arguments kept. -/
abbrev kR' (s : State) : Region := ⟨S s, 48⟩

section
variable {s : State} (hp : BP s)
include hp

theorem s_in {d k : Nat} (h : d + k ≤ 2112) : InRegions s.wr (S s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem s_in' {d k : Nat} (h : d + k ≤ 2112) : InRegions (s.rd ++ s.wr) (S s + BitVec.ofNat 64 d) k :=
  in_left (s_in hp h)

theorem a_in : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 8) 8 :=
  ⟨aR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩

omit hp in
/-- The slots of the arguments are in `scratch`, apart from the powers. -/
theorem kR'_sub : (kR' s).Sub (sR s) := Region.sub_prefix (by decide)

/-- What a frame of the regions written keeps: the stack argument and the
return address. -/
theorem keep_a {m m' : Mem} (hf : Frame (wR s) m m') : m'.readW (SP s + BitVec.ofNat 64 8) 64 =
    m.readW (SP s + BitVec.ofNat 64 8) 64 :=
  hf.readW (r := aR s) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.y_a.symm
    · exact hp.d_a.symm
    · exact hp.s_a.symm) (by decide)

theorem keep_r {m m' : Mem} (hf : Frame (wR s) m m') : m'.readW (SP s) 64 = m.readW (SP s) 64 :=
  hf.readW (r := ⟨SP s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.r_c
    · exact hp.r_y
    · exact hp.r_d
    · exact hp.r_s) (by decide)

/-- The key context, through a frame of the regions written. -/
theorem keep_k {m m' : Mem} (hf : Frame (wR s) m m') {d k : Nat} (h : d + k ≤ 256) :
    Spec.Aes.bytesAt m' (K s + BitVec.ofNat 64 d) k = Spec.Aes.bytesAt m (K s + BitVec.ofNat 64 d) k :=
  bytesAt_frame hf (fun r hr => by
    have hs : Region.Sub ⟨K s + BitVec.ofNat 64 d, k⟩ (kR s) := Offset.sub_base _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_c.sub_left hs
    · exact hp.k_y.sub_left hs
    · exact hp.k_d.sub_left hs
    · exact hp.k_s.sub_left hs) (by omega)

omit hp in
theorem arg_eq : s.mem.readW (SP s + BitVec.ofNat 64 8) 64 = S s := rfl

/-- The entry: the arguments kept, with `scratch` in `r11`. -/
theorem entry_ok : WP isa (.block entry) s fun s₁ => s₁.gpr .r11 = S s ∧ (∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) ∧
    Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w₁ := s_in hp (show 0 + 8 ≤ 2112 by decide)
  have w₂ := s_in hp (show 8 + 8 ≤ 2112 by decide)
  have w₃ := s_in hp (show 16 + 8 ≤ 2112 by decide)
  have w₄ := s_in hp (show 24 + 8 ≤ 2112 by decide)
  have w₅ := s_in hp (show 32 + 8 ≤ 2112 by decide)
  have w₆ := s_in hp (show 40 + 8 ≤ 2112 by decide)
  have a₀ := a_in hp
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have s₁₂ := sep 0 8 (by decide) (by decide) (by decide)
  have s₁₃ := sep 0 16 (by decide) (by decide) (by decide)
  have s₁₄ := sep 0 24 (by decide) (by decide) (by decide)
  have s₁₅ := sep 0 32 (by decide) (by decide) (by decide)
  have s₁₆ := sep 0 40 (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at s₁₂ s₁₃ s₁₄ s₁₅ s₁₆
  have s₂₃ := sep 8 16 (by decide) (by decide) (by decide)
  have s₂₄ := sep 8 24 (by decide) (by decide) (by decide)
  have s₂₅ := sep 8 32 (by decide) (by decide) (by decide)
  have s₂₆ := sep 8 40 (by decide) (by decide) (by decide)
  have s₃₄ := sep 16 24 (by decide) (by decide) (by decide)
  have s₃₅ := sep 16 32 (by decide) (by decide) (by decide)
  have s₃₆ := sep 16 40 (by decide) (by decide) (by decide)
  have s₄₅ := sep 24 32 (by decide) (by decide) (by decide)
  have s₄₆ := sep 24 40 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have hn : BitVec.ofNat 64 (n s - 0) = s.gpr .r9 := by simp
  apply WP.of_runBlock
  refine ⟨_, by simp only [entry, argCtx, argRounds, argCtr, argY, argData, argN]; xrun [a₀, arg_eq, w₁, w₂, w₃, w₄, w₅, w₆],
    ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals try simp (disch := first | decide | assumption) only [gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte,
    Mem.readW_writeW_self64, Mem.readW_writeW_sep, Nat.mul_zero, BitVec.add_zero, hn]
  · have c : ∀ d, 0 ≤ d → d + 8 ≤ 48 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d _ h₂ => Offset.contains_base _ h₂ (by omega)
    have c0 : (kR' s).Contains (S s) (64 / 8) := by simpa using c 0 (by decide) (by decide)
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide) (by decide))

end

end VG.Proof.AesGcm.X86_64.Blocks
