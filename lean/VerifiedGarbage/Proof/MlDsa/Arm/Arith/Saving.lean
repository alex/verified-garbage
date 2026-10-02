import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: registers saved in frames

`saving rs body` pushes each register of `rs` in a frame of its own, runs
`body`, and restores each with the pop of its frame. If `body` writes memory
only in regions `W` that do not overlap the `4 · |rs|` bytes below the stack
pointer, the frames hold the registers until they are popped (`wp_saving`):
the registers `rs` are restored, the others are what `body` left, and so are
memory and `rd`, while `sp` and `wr` are back as on entry. `body` runs from a
state with the same registers and `rd`, more writable regions (the frames, at
the head of `wr`), and memory changed only below the stack pointer (`Entry`).

`ct_saving`: the push and pop of a frame leak only addresses computed from
the stack pointer, so `saving rs body` is constant time if `body` is, by the
taint analysis, from the registers `ps` public.
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith

/-- What the state `s₁` in which `body` starts keeps of the state `s` on
entry to `saving rs body`. -/
structure Entry (n : Nat) (s s₁ : State) : Prop where
  gpr : s₁.gpr = s.gpr
  rd : s₁.rd = s.rd
  wr : ∀ R ∈ s.wr, R ∈ s₁.wr
  frame : Frame [belowA s.sp n] s.mem s₁.mem

theorem entry_refl (s : State) : Entry 0 s s :=
  ⟨rfl, rfl, fun _ h => h, Frame.refl _ _⟩

/-- The word at `sp - 4` of the push of `r`. -/
theorem pushed_word (r : Reg) (s : State) :
    (pushed [r] s).mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r :=
  Mem.readW_writeW_self32 _ _ _

theorem word_region (sp : BitVec 32) {n : Nat} (h : 4 + n ≤ sp.toNat) :
    (belowA sp (4 + n)).Contains (State.addr (sp - 4)) 4 := by
  have := addr_toNat' sp
  have := addr_toNat' (sp - 4)
  simp only [belowA, Region.Contains]
  bv_omega

theorem word_disj (sp : BitVec 32) {n : Nat} (h : 4 + n ≤ sp.toNat) :
    (⟨State.addr (sp - 4), 4⟩ : Region).Disjoint (belowA (sp - 4) n) := by
  intro x hx hy
  have := addr_toNat' sp
  have := addr_toNat' (sp - 4)
  simp only [belowA, Region.Contains] at hx hy
  bv_omega

theorem wp_saving (rs : List Reg) (body : Prog isa) {W : List Region} :
    ∀ (Q : State → Prop) (s : State), 4 * rs.length ≤ s.sp.toNat → (∀ R ∈ W, (belowA s.sp (4 * rs.length)).Disjoint R) →
    (∀ s₁, Entry (4 * rs.length) s s₁ → WP isa body s₁ fun s₂ => Frame W s₁.mem s₂.mem ∧ Q s₂) →
    WP isa (saving rs body) s fun s' => ∃ s₂, Q s₂ ∧ s'.mem = s₂.mem ∧ s'.rd = s₂.rd ∧
      s'.sp = s.sp ∧ s'.wr = s.wr ∧ ∀ r, s'.gpr r = if r ∈ rs then s.gpr r else s₂.gpr r := by
  induction rs with
  | nil =>
    intro Q s _ _ hb
    obtain ⟨t, s₂, he, -, hq⟩ := hb s (entry_refl s)
    obtain ⟨-, hw, hsp⟩ := Exec.rdwr he
    exact ⟨t, s₂, he, s₂, hq, rfl, rfl, hsp, hw, fun r => by simp⟩
  | cons r rs ih =>
    intro Q s hsp hW hb
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hsp hW hb
    have hs4 : 4 ≤ s.sp.toNat := by omega
    have e4 : (4 : BitVec 32) = BitVec.ofNat 32 (4 * [r].length) := rfl
    have hsp' : (s.sp - 4).toNat = s.sp.toNat - 4 := by bv_omega
    have hsub : Region.Sub (belowA (s.sp - 4) (4 * rs.length)) (belowA s.sp (4 * rs.length + 4)) := by
      have := belowA_push (sp := s.sp) (k := 4) (a := 4 * rs.length) (by omega)
      rwa [Nat.add_comm] at this
    have hwd := word_region s.sp (n := 4 * rs.length) (by omega)
    rw [Nat.add_comm] at hwd
    refine WP.frame (rs := [r]) (r := r) rfl (by simp; omega) (by simp) ?_
    have ih' := ih (fun s₂ => Q s₂ ∧ s₂.mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r) (pushed [r] s)
      (by rw [pushed_sp, ← e4, hsp']; omega)
      (fun R hR => (hW R hR).sub_left (by rw [pushed_sp, ← e4]; exact hsub)) (fun s₁ hE => ?_)
    · refine WP.mono ih' fun s' ⟨s₂, ⟨hq, hword⟩, hm, hrd, hsp₂, hwr, hg⟩ => ⟨s₂, hq, ?_, ?_, ?_, ?_, ?_⟩
      · exact hm
      · exact hrd
      · simp only [popped_sp, hsp₂, pushed_sp]; rw [← e4]; exact BitVec.sub_add_cancel _ _
      · simp only [popped_wr, hwr, pushed_wr, List.tail_cons]
      · intro r'
        by_cases e : r' = r
        · subst e
          simp only [popped, State.setReg, ite_true, List.mem_cons, true_or]
          rw [hm, hsp₂, pushed_sp, ← e4]; exact hword
        · rw [popped_gpr e, hg r', pushed_gpr]
          simp only [List.mem_cons, e, false_or]
    · -- The body, from the state after all the pushes.
      have hE' : Entry (4 * rs.length + 4) s s₁ := by
        refine ⟨hE.gpr.trans (pushed_gpr _ _), hE.rd.trans (pushed_rd _ _),
          fun R hR => hE.wr R (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hR), ?_⟩
        have f₀ : Frame [⟨State.addr (s.sp - 4), 4⟩] s.mem (pushed [r] s).mem := by
          have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 (4 * [r].length)) [s.gpr r]
            (by simp; bv_omega)
          simp only [List.length_singleton] at this
          exact this
        refine (f₀.sub fun R hR => ?_).trans (hE.frame.sub fun R hR => ?_)
        · rw [List.mem_singleton] at hR; subst hR
          refine ⟨_, List.mem_singleton_self _, fun x hx => hwd.byte ?_⟩
          simp only [Region.Contains] at hx ⊢
          omega
        · rw [List.mem_singleton] at hR; subst hR
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          rw [pushed_sp, ← e4]; exact hsub
      refine WP.mono (hb s₁ hE') fun s₂ ⟨hf, hq⟩ => ⟨hf, hq, ?_⟩
      have hw₁ : s₁.mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r := by
        rw [hE.frame.readW (r := ⟨State.addr (s.sp - 4), 4⟩) (Region.contains_self _ _)
          (fun R hR => by
            rw [List.mem_singleton] at hR; subst hR
            rw [pushed_sp, ← e4]; exact word_disj s.sp (by omega)) (by decide)]
        exact pushed_word r s
      rw [hf.readW (r := belowA s.sp (4 * rs.length + 4)) hwd (fun R hR => hW R hR) (by decide), hw₁]

/-- `saving rs body` is constant time if the taint analysis proves `body`
constant time from the registers `ps` public. -/
theorem ct_saving (rs : List Reg) (body : Prog isa) (ps : List Reg) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs ps) body hc).isSome = true) :
    ∀ P : State → State → Prop, (∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r) →
      RelCT isa P (saving rs body) fun _ _ => True := by
  induction rs with
  | nil =>
    intro P hP
    exact RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs ps)
      (fun s₁ s₂ hp => Taint.agree_ofRegs (hP s₁ s₂ hp).2) h
  | cons r rs ih =>
    intro P hP
    refine RelCT.frame (fun s₁ s₂ hp => (hP s₁ s₂ hp).1) (ih _ fun a b ⟨s₁, s₂, hp, h₁, h₂⟩ => ?_)
    obtain ⟨rfl, -⟩ := push_pushed' h₁
    obtain ⟨rfl, -⟩ := push_pushed' h₂
    obtain ⟨hsp, hg⟩ := hP s₁ s₂ hp
    exact ⟨by rw [pushed_sp, pushed_sp, hsp], fun r hr => by rw [pushed_gpr, pushed_gpr]; exact hg r hr⟩


/-- Constant time of `saving rs body` for a contract whose public data
include the stack pointer and the registers `ps`. -/
theorem ct_of_saving {k : Contract isa} (rs : List Reg) (body : Prog isa) (ps : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.Arm.taint.T} (h : (VG.Arm.taint.check (Taint.ofRegs ps) body hc).isSome = true) :
    ConstantTime isa k.pre k.pub (saving rs body) :=
  RelCT.constantTime (ct_saving rs body ps h _ fun s₁ s₂ hp => hpub s₁ s₂ hp.2.2)

/-- The callee-saved registers after `saving rs body`, if `rs` and the
registers `body` keeps cover them. -/
theorem preserved_of_saving {rs : List Reg} {s s' s₂ : State}
    (hg : ∀ r, s'.gpr r = if r ∈ rs then s.gpr r else s₂.gpr r)
    (hk : ∀ r ∈ preserved, r ∉ rs → s₂.gpr r = s.gpr r) : ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  intro r hr
  rw [hg r]
  split
  · rfl
  · exact hk r hr ‹_›

end VG.Proof.MlDsa.Arm.Arith
