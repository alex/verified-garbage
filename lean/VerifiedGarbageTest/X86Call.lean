import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# A verified call on x86 (32-bit)

A caller that pushes its two arguments in a frame, calls a verified function
adding them, and pops the frame: its correctness from the callee's (`WP.frame`,
`WP.call`), its stack use (`Exec.frameSp`), and its constant-time check,
which follows the frame and the call into the callee (`taint_decide`).
-/

namespace VG.Test.X86Call

open VG VG.X86

/-- `add2(a, b)`: `a + b`. -/
def add2 : Prog isa :=
  .block [.mov .eax (.mem ⟨.esp, 4⟩), .mov .ecx (.mem ⟨.esp, 8⟩), .alu .add .eax (.reg .ecx)]

/-- `f(out, a, b)`: `*out = add2(a, b)`, calling `add2` with the arguments
pushed last to first. -/
def f : Prog isa :=
  .seq (.block [.mov .ecx (.mem ⟨.esp, 8⟩), .mov .edx (.mem ⟨.esp, 12⟩)])
    (.seq (.frame (.push [.edx, .ecx]) (.call "vg_add2" add2) (.pop .ecx 2))
      (.block [.mov .ecx (.mem ⟨.esp, 4⟩), .store ⟨.ecx, 0⟩ .eax]))

/-- `add2`: two read-only 4-byte arguments; `stack` bytes of stack below `esp`. -/
def add2K : Contract isa where
  pre s := s.rd = [⟨argAddr s 0, 8⟩] ∧ s.wr = [] ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' := s'.gpr .eax = arg s 0 + arg s 1
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp

/-- `out`, where `f` writes. -/
def out (s : State) : Region := ⟨(arg s 0).setWidth 64, 4⟩

/-- `f`: three read-only arguments, the 4 bytes at `out` writable, and 12
bytes of stack below `esp`, which neither they nor the arguments overlap. -/
def fK : Contract isa where
  pre s := s.rd = [⟨argAddr s 0, 12⟩] ∧ s.wr = [out s] ∧ 12 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 0).toNat + 4 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 8⟩ (out s) ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩ (out s)
  post s s' := s'.mem.readW (out s).base 32 = arg s 1 + arg s 2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

theorem stackUse_f : stackUse f = 12 := rfl

theorem argAddr_succ (s : State) {j : Nat} (h : (s.gpr .esp).toNat + 4 * j + 8 < 2 ^ 32) :
    argAddr s (j + 1) = argAddr s 0 + BitVec.ofNat 64 (4 * (j + 1)) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (j + 1))).setWidth 64 =
      addr (s.gpr .esp) (4 + 4 * (j + 1)) from rfl,
    show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4 from rfl,
    addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The `j`-th of `n` read-only arguments is readable. -/
theorem args_in {s : State} {n : Nat} (hrd : s.rd = [⟨argAddr s 0, 4 * n⟩])
    (h : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (j : Nat) (hj : j < n) :
    InRegions (s.rd ++ s.wr) (argAddr s j) 4 := by
  refine ⟨⟨argAddr s 0, 4 * n⟩, by simp [hrd], ?_⟩
  simp only [Region.Contains]
  cases j with
  | zero => simp; omega
  | succ j =>
    rw [argAddr_succ s (by omega), BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem wp_movm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp}
    (hin : InRegions (s.rd ++ s.wr) (s.ea m) 4)
    (k : WP isa (.block is) (s.setReg d (s.mem.readW (s.ea m) 32)) Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, by simp [exec, readSrc, State.load32, hin], k⟩

theorem wp_store {is : List Instr} {s : State} {Q : State → Prop} {m : MemOp} {r : Reg} {a : Addr}
    (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.gpr r) } Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, by simp [exec, State.store32, ha, hout], k⟩

theorem add2_correct {s : State} (hp : add2K.pre s) :
    WP isa add2 s fun s' => abiPreserved s s' ∧ add2K.post s s' := by
  obtain ⟨hrd, -, hfit⟩ := hp
  refine wp_movm (args_in (n := 2) hrd hfit 0 (by omega)) (wp_movm ?_ (WP.block_cons_iff.mpr ⟨_, rfl,
    WP.block_nil ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩⟩))
  · have := args_in (n := 2) hrd hfit 1 (by omega); exact this
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem add2_ok : ∀ s, add2K.pre s → ∃ t s', Exec isa add2 s t s' ∧ abiPreserved s s' ∧ add2K.post s s' :=
  fun _ hs => add2_correct hs

theorem noSp_add2 : NoSp add2 := by decide
theorem noSp_f : NoSp f := by decide

/-- Bytes above `esp` are not among the `n` below it. -/
theorem above_below {sp : BitVec 32} {n : Nat} (hn : n ≤ sp.toNat) {d w : Nat}
    (h : sp.toNat + d + w ≤ 2 ^ 32) :
    Region.Disjoint ⟨sp.setWidth 64 + BitVec.ofNat 64 d, w⟩ (below sp n) := by
  intro x hx hx'
  simp only [Region.Contains] at hx hx'
  rw [VG.X86.Taint.sub_setWidth hn] at hx'
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem f_correct {s : State} (hp : fK.pre s) :
    WP isa f s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ fK.post s s' := by
  obtain ⟨hrd, hwr, h12, hfit, hout, -, -⟩ := hp
  refine WP.seq (wp_movm (args_in (n := 3) hrd hfit 1 (by omega)) (wp_movm ?_ (WP.block_nil ?_)))
  · have := args_in (n := 3) hrd hfit 2 (by omega); exact this
  set s₂ := (s.setReg .ecx (s.mem.readW (argAddr s 1) 32)).setReg .edx
    (s.mem.readW (argAddr s 2) 32) with hs₂
  have e₂ : s₂.gpr .esp = s.gpr .esp := rfl
  have hn : 4 * [Reg.edx, .ecx].length ≤ (s₂.gpr .esp).toNat := by rw [e₂]; simp; omega
  refine WP.seq (WP.frame (by simp) (by decide) (by decide) hn noSp_add2 ?_)
  set p := pushed [.edx, .ecx] s₂ with hp
  have ep : p.gpr .esp = s.gpr .esp - 8 := by rw [hp, pushed_esp, e₂]; rfl
  have ep' : (p.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by rw [ep]; bv_omega
  -- The callee reads its arguments from the frame.
  have hfr : (⟨argAddr p.callEntry 0, 8⟩ : Region) = below (s₂.gpr .esp) 8 := by
    rw [argAddr_callEntry, ep, e₂]; simp
  refine WP.call add2_ok noSp_add2 (by rw [ep']; show 0 + 4 ≤ _; omega)
    (rd := [⟨argAddr p.callEntry 0, 8⟩]) (wr := []) ⟨rfl, rfl, ?_⟩ ?_
    (fun _ _ h => absurd h (by simp [InRegions])) ?_
  · show ((p.gpr .esp) - 4).toNat + 12 ≤ 2 ^ 32
    rw [ep]; bv_omega
  · intro a n ⟨r, hr, hc⟩
    simp only [List.append_nil, List.mem_singleton] at hr
    subst hr
    rw [hfr] at hc
    exact ⟨_, List.mem_append_right _ (by rw [hp, pushed_wr]; exact List.mem_cons_self), hc⟩
  intro s' hrd' hwr' hcs hf _ ⟨s₃, _, hg₃, hpost⟩
  have hpop := popReg_eq s' .ecx 2
  set q := popped .ecx 2 s' with hq
  have eq : q.gpr .esp = s.gpr .esp := by
    show (popReg s' .ecx 2).gpr .esp = _
    rw [hpop.2.2.1, hcs .esp (by simp [calleeSaved]), ep]
    bv_omega
  have hcs' : ∀ r ∈ calleeSaved, q.gpr r = s.gpr r := by
    intro r hr
    by_cases h : r = .esp
    · subst h; exact eq
    · have hc : r ≠ .ecx := by
        rintro rfl; simp [calleeSaved] at hr
      show (popReg s' .ecx 2).gpr r = _
      rw [hpop.2.2.2 r h hc, hcs r hr, hp, pushed_gpr _ _ h, hs₂]
      simp [State.setReg, hc, show r ≠ .edx by rintro rfl; simp [calleeSaved] at hr]
  have hsum : q.gpr .eax = arg s 1 + arg s 2 := by
    show (popReg s' .ecx 2).gpr .eax = _
    rw [hpop.2.2.2 .eax (by decide) (by decide), ← hg₃ .eax (by decide), hpost]
    show arg p.callEntry 0 + arg p.callEntry 1 = _
    have h4 : 4 ≤ (p.gpr .esp).toNat := by omega
    rw [arg_callEntry h4 (by omega), arg_callEntry h4 (by omega),
      pushed_word (by decide) hn (by decide), pushed_word (by decide) hn (by decide)]
    rfl
  have hrdq : q.rd = s.rd := by
    show (popReg s' .ecx 2).rd = _; rw [hpop.1, hrd', hp, pushed_rd]; rfl
  have hwrq : q.wr = s.wr := by
    show s'.wr.tail = _; rw [hwr', hp, pushed_wr]; rfl
  -- The frame and the call change only the 12 bytes below `esp`.
  have hmem : Frame [below (s.gpr .esp) 12] s.mem q.mem := by
    show Frame _ s.mem (popReg s' .ecx 2).mem
    rw [(popReg_rest s' .ecx 2).1]
    refine Frame.trans (Frame.sub (pushed_frame (s := s₂) (by decide) hn) fun r hr => ?_)
      (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [e₂]; exact below_sub (by simp) h12⟩
    · simp only [List.nil_append, List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [ep]
      exact below_inner (k := 8) (by decide) h12
  have harg : q.mem.readW (q.ea ⟨.esp, 4⟩) 32 = arg s 0 := by
    rw [show q.ea ⟨.esp, 4⟩ = argAddr s 0 by simp only [State.ea, eq]; rfl]
    refine hmem.readW (r := ⟨argAddr s 0, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton]
    rintro r rfl
    rw [show argAddr s 0 = addr (s.gpr .esp) 4 from rfl, addr_eq (by omega)]
    exact above_below h12 (by omega)
  change WP isa _ q _
  refine wp_movm ?_ (wp_store (a := (out s).base) ?_ ?_ (WP.block_nil ⟨fun r hr => ?_, ?_⟩))
  · rw [show q.ea ⟨.esp, 4⟩ = argAddr s 0 by simp only [State.ea, eq]; rfl, hrdq, hwrq]
    exact args_in (n := 3) hrd hfit 0 (by omega)
  · simp only [State.ea, State.setReg, ite_true, out, BitVec.add_zero]
    exact congrArg _ harg
  · exact ⟨out s, by simp [State.setReg, hwrq, hwr], Region.contains_self _ _⟩
  · have hc : r ≠ .ecx := by rintro rfl; simp [calleeSaved] at hr
    simp only [State.setReg, hc, ite_false]
    exact hcs' r hr
  · show (Mem.writeW _ _ _).readW _ 32 = _
    rw [Mem.readW_writeW_self32]
    simp only [State.setReg, show (Reg.eax = Reg.ecx) = False by decide, ite_false, hsum]

theorem f_verified_correct : ∀ s, fK.pre s →
    ∃ t s', Exec isa f s t s' ∧ abiPreserved s s' ∧ fK.post s s' := by
  intro s hs
  obtain ⟨t, s', he, hcs, hpost⟩ := f_correct hs
  obtain ⟨-, hwr, h12, hfit, -, hA, -⟩ := hs
  -- The return address is neither at `out` nor in the stack `f` uses.
  have hf := Exec.frameSp he noSp_f (by rw [stackUse_f]; exact h12)
  rw [hwr, stackUse_f] at hf
  refine ⟨t, s', he, ⟨hcs, hf.readW (Region.contains_self _ _) ?_ (by decide)⟩, hpost⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact fun x hx => hA x (by simp only [Region.Contains] at hx ⊢; omega)
  · have := above_below (d := 0) h12 (w := 4) (by omega)
    simpa using this

/-- The initial taint: `esp` and `out` are public, `a` and `b` secret, and
the 12 bytes below `esp` are free for the frame and the call. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [4], argLen := 8, room := 12 }

theorem agree₀ {s₁ s₂ : State} (h₁ : fK.pre s₁) (h₂ : fK.pre s₂) (hpub : fK.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, fK.pre s → VG.X86.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, h12, hfit, hout, hA, hR⟩ := hs
    refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hw, out, τ₀], by simp [hw], ?_⟩,
      fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨by simp only [τ₀]; omega, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
      fun _ => ⟨h12, ?_⟩
    · simp only [hw, List.mem_singleton]
      rintro r rfl
      simp only [out, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by omega)]; exact hout
    · simp only [hw, List.mem_singleton]; rintro r rfl; exact hA
    · simp only [hw, List.mem_singleton]; rintro r rfl; exact hR
  have hwr : s₁.wr = s₂.wr := by rw [h₁.2.1, h₂.2.1, out, out, a0]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => hwr, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 8) (by have := h₁.2.2.2.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (n := 8) (by have := h₂.2.2.2.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show (k - 4) / 4 = 0 by omega]
    exact congrArg _ a0

/-- Memory holding `out = 0x1000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

theorem f_verified : Verified X86.target f fK := by
  refine ⟨f_verified_correct, ?_, ⟨⟨fun r => if r = .esp then 0x4000 else 0, none, none, none, none,
    (fun _ => 0), satMem, [⟨0x4004, 12⟩], [⟨0x1000, 4⟩], fun _ => 0⟩, ?_⟩⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide)
  · have a0 : arg ⟨fun r => if r = .esp then 0x4000 else 0, none, none, none, none,
        (fun _ => 0), satMem, [⟨0x4004, 12⟩], [⟨0x1000, 4⟩], fun _ => 0⟩ 0 = 0x1000 := by decide
    refine ⟨by decide, by simp only [out, a0]; rfl, by decide, by decide, by rw [a0]; decide, ?_, ?_⟩ <;>
    · intro x h₁ h₂
      simp only [Region.Contains, out, a0, ite_true] at h₁ h₂
      bv_omega

end VG.Test.X86Call
