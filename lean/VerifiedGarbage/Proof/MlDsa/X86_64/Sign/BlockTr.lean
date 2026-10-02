import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks

/-!
# ML-DSA signing on x86-64: blocks that leak only their pointers

Untrusted: everything here is checked by Lean. A block of moves, arithmetic
and stores whose memory operands are `[b + disp]` with `b` among registers
`rs` that it never writes leaks the same from two states that agree on `rs`
(`block_tr`). Unlike the taint analysis, which evaluates the code, this
holds for code with immediates and displacements that are variables, such
as the pieces of the function indexed by a polynomial or an entry of `Â`;
`blockOk` is checked by `rfl`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64

/-- The base register of a memory operand without an index. -/
def mBase (m : MemOp) : Option (List Reg) := if m.index = none then some [m.base] else none

/-- The registers the address of an operand uses. -/
def srcBase : Src → Option (List Reg)
  | .mem m => mBase m
  | _ => some []

/-- The registers the address an instruction accesses uses, for the moves,
arithmetic, shifts and stores; `none` for any other instruction. -/
def memBase : Instr → Option (List Reg)
  | .mov _ src => srcBase src
  | .store m _ => mBase m
  | .alu _ _ src => srcBase src
  | .mov32 _ src => srcBase src
  | .store32 m _ => mBase m
  | .alu32 _ _ src => srcBase src
  | .shift .. => some []
  | .shift32 .. => some []
  | .movzx8 _ m => mBase m
  | .store8 m _ => mBase m
  | _ => none

/-- Every instruction's addresses use only `rs`, which none writes. -/
def blockOk (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (match memBase i with | some l => l.all (rs.contains ·) | none => false) &&
    rs.all fun r => !Taint.clobbers i r

theorem ea_agree {rs : List Reg} {m : MemOp} {l : List Reg} (h : mBase m = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : s.ea m = s'.ea m := by
  unfold mBase at h
  split at h
  · rename_i hi
    cases h
    simp only [State.ea, hi, hs m.base (hl _ (List.mem_singleton_self _))]
  · cases h

theorem srcAddrs_agree {rs : List Reg} {src : Src} {l : List Reg} (h : srcBase src = some l)
    (hl : ∀ r ∈ l, r ∈ rs) {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    srcAddrs s src = srcAddrs s' src := by
  cases src with
  | mem m => simp only [srcAddrs, ea_agree h hl hs]
  | _ => rfl

theorem addrs_agree {rs : List Reg} {i : Instr} {l : List Reg} (h : memBase i = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : isa.addrs i s = isa.addrs i s' := by
  cases i <;> simp only [memBase, reduceCtorEq] at h
  all_goals first
    | exact srcAddrs_agree h hl hs
    | (show [State.ea _ _] = [State.ea _ _]; rw [ea_agree h hl hs])
    | rfl

theorem blockOk_cons {rs : List Reg} {i : Instr} {is : List Instr} (h : blockOk rs (i :: is) = true) :
    (∃ l, memBase i = some l ∧ ∀ r ∈ l, r ∈ rs) ∧ (∀ r ∈ rs, Taint.clobbers i r = false) ∧
      blockOk rs is = true := by
  simp only [blockOk, List.all_cons, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hm, hc⟩, hr⟩ := h
  refine ⟨?_, hc, by simpa [blockOk] using hr⟩
  revert hm
  cases memBase i with
  | some l => intro hm; simp only [List.all_eq_true, List.contains_iff_mem] at hm; exact ⟨l, rfl, hm⟩
  | none => intro hm; cases hm

theorem execBlock_tr {rs : List Reg} : ∀ {is : List Instr}, blockOk rs is = true →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, _, _, _, _, hs, e₁, e₂ => by
    obtain ⟨⟨l, hm, hl⟩, hc, h'⟩ := blockOk_cons h
    simp only [execBlock] at e₁ e₂
    split at e₁
    · cases e₁
    · rename_i u₁ x₁
      split at e₂
      · cases e₂
      · rename_i u₂ x₂
        obtain ⟨⟨a₁, b₁⟩, f₁, g₁⟩ := Option.map_eq_some_iff.mp e₁
        obtain ⟨⟨a₂, b₂⟩, f₂, g₂⟩ := Option.map_eq_some_iff.mp e₂
        simp only [Prod.mk.injEq] at g₁ g₂
        rw [← g₁.2, ← g₂.2, show addrs i s₁ = addrs i s₂ from addrs_agree hm hl hs,
          execBlock_tr h' (fun r hr => by rw [exec_gpr (hc r hr) x₁, exec_gpr (hc r hr) x₂, hs r hr]) f₁ f₂]

/-- A block that `blockOk` accepts leaks the same from states that agree on `rs`. -/
theorem block_tr {rs : List Reg} {is : List Instr} (h : blockOk rs is = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_tr h (hP _ _ hp) e₁ e₂, trivial⟩

end VG.Proof.MlDsa.X86_64.Sign

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Impl.MlKem.X86_64 (at_)

/-! ## Copies -/

theorem execBlock_snoc : ∀ {is : List Instr} {i : Instr} {s s' : State} {t : List Leak},
    execBlock isa (is ++ [i]) s = some (s', t) →
      ∃ s₀ t₀, execBlock isa is s = some (s₀, t₀) ∧ isa.exec i s₀ = some s'
  | [], i, s, s', t, h => by
    simp only [List.nil_append, execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨s, [], rfl, h.1 ▸ e⟩
  | j :: is, i, s, s', t, h => by
    simp only [List.cons_append, execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨s₀, t₀, h0, h1⟩ := execBlock_snoc h2
      refine ⟨s₀, (isa.addrs j s).map Leak.addr ++ t₀, ?_, heq.1 ▸ h1⟩
      simp only [execBlock, e, h0, Option.map_some]

/-- The body of a copy's loop. -/
abbrev cbody : List Instr := [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rdi (.imm 8),
  .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]

theorem cbody_rcx {s s' : State} {t : List Leak} (h : execBlock isa cbody s = some (s', t)) :
    s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨s₀, t₀, h0, h1⟩ := execBlock_snoc (is := [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax,
    .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8)]) h
  have e := execBlock_gpr (r := .rcx) (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) h0
  simp only [isa, exec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at h1
  subst h1
  constructor <;> simp [State.setReg, arithFlags, State.setFlags, e]

theorem cbody_taint : ((taint.check (Taint.ofRegs [.rdi, .rsi, .rcx]) (.block cbody)
    (Taint.hintOf taint (Taint.ofRegs [.rdi, .rsi, .rcx]) (.block cbody))).map fun τ' =>
      (RegSet.ofList [Reg.rdi, .rsi, .rcx]).subset τ'.regs) = some true := by decide

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (h0 : 0 < n ∧ n % 8 = 0) (hn : n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  let I : Nat → State → State → Prop := fun m x y =>
    (∀ r ∈ [Reg.rdi, .rsi, .rcx], x.gpr r = y.gpr r) ∧ (x.gpr .rcx).toNat = m + 1
  have pro : ∀ s, WP isa (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8)))])) s
      fun s' => s'.gpr .rdi = pa s dst ∧ s'.gpr .rsi = pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 (n / 8) := fun s => by
    unfold lea
    xrun [sx_ofNat hd, sx_ofNat hs, hsr, List.cons_append, List.nil_append,
      sw_ofNat (show n / 8 < 2 ^ 32 by omega)]
  unfold copy
  refine RelCT.seq (R := I (n / 8 - 1)) (VG.Proof.MlKem.X86_64.RelCT.postDep (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _)
    (lea_nomem _ _)) fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
    (fun x y _ => ⟨pro x, pro y⟩) fun x y x' y' hp ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ?_) ?_
  · refine RelCT.loop (M := isa) I (fun m => ?_) (n / 8 - 1)
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hr, hc⟩ e₁ e₂
    obtain ⟨ht, hr'⟩ := RelCT.taintRegs (P := fun x y => ∀ r ∈ [Reg.rdi, .rsi, .rcx], x.gpr r = y.gpr r)
      (fun _ _ h => Taint.agree_ofRegs h) [.rdi, .rsi, .rcx] cbody_taint _ _ _ _ _ _ hr e₁ e₂
    rw [Exec.block_iff] at e₁ e₂
    obtain ⟨c₁, z₁⟩ := cbody_rcx e₁
    obtain ⟨c₂, z₂⟩ := cbody_rcx e₂
    have ec : s₁.gpr .rcx = s₂.gpr .rcx := hr .rcx (by simp)
    have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
    refine ⟨ht, by rw [hev, hev, z₁, z₂, ec], fun _ => trivial, fun hcont => ?_⟩
    rw [hev, z₁] at hcont
    have hne : s₁.gpr .rcx - 1 ≠ 0 := by
      intro h0; rw [h0] at hcont; simp at hcont
    have h1 : (s₁.gpr .rcx - 1).toNat = m := by
      rw [BitVec.toNat_sub, hc]
      have : (1 : BitVec 64).toNat = 1 := rfl
      rw [this]; omega
    refine ⟨m - 1, ?_, hr', ?_⟩
    · have : m ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
      omega
    · have : m ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
      rw [c₁, h1]; omega
  · obtain ⟨e1, e2⟩ := hP x y hp
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a1, b1, pa, pa, e1]
      · rw [a2, b2, pa, pa, e2]
      · rw [a3, b3]
    · rw [a3, BitVec.toNat_ofNat]; omega

end VG.Proof.MlDsa.X86_64.Sign
