import VerifiedGarbage.Proof.Argon2.X86.Derive.Frame
import VerifiedGarbage.Proof.Argon2.X86.Derive.Regions
import VerifiedGarbage.Proof.Argon2.X86.Divide

/-!
# Argon2 on x86 (32-bit): the state of the derivation's body

`Inv s₀ s`: in the body, `esp` and `ebp` point to the locals (`E s₀`), the
permissions are those of the body's entry, and memory has changed only in
the memory matrix, `scratch`, the output, the locals and the 84 bytes of
stack below them. The arguments, the inputs, the saved registers and the
return address are therefore kept (`Inv.arg`, `Inv.done`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

section
variable (s₀ : State)

/-- The locals. -/
abbrev locR : Region := ⟨(E s₀).setWidth 64, 144⟩

/-- The stack below the locals. -/
abbrev callR : Region := below (E s₀) 84

/-- The regions the body may write. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, locR s₀, callR s₀]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_toNat : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_toNat (by have := hp.esp_lo; omega)

end

theorem entry_esp (s₀ : State) : (entry s₀).gpr .esp = E s₀ := by
  simp only [entry, pushed_esp, List.length_singleton, List.length_replicate, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem entry_gpr (s₀ : State) {r : Reg} (h : r ≠ .esp) : (entry s₀).gpr r = s₀.gpr r := by
  simp only [entry, pushed_gpr _ _ h]

theorem entry_rd (s₀ : State) : (entry s₀).rd = s₀.rd := by simp [entry]


/-! ## The pushes -/

theorem pushed_esp_nat {rs : List Reg} {s : State} (h : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
  rw [pushed_esp, sub_nat h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem entry_frame : Frame [below (E0 s₀) 160] s₀.mem (entry s₀).mem := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE := (s₀.gpr .esp).isLt
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  -- Each push writes within the 160 bytes below `esp` on entry.
  have step : ∀ {rs : List Reg} {s : State}, .esp ∉ rs → 4 * rs.length ≤ (s.gpr .esp).toNat →
      (s₀.gpr .esp).toNat - 160 ≤ (s.gpr .esp).toNat - 4 * rs.length →
      (s.gpr .esp).toNat ≤ (s₀.gpr .esp).toNat → Frame [below (E0 s₀) 160] s.mem (pushed rs s).mem :=
    fun {rs s} hrs hn h₁ h₂ => (pushed_frame hrs hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, sub32 ?_ ?_⟩
      · rw [sub_nat hn, sub_nat (by omega)]; omega
      · rw [sub_nat hn, sub_nat (by omega)]; omega
  have n₁ := pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton] at n₁ n₂ n₃ n₄
  exact (((((step (by decide) (by simp only [List.length_singleton]; omega)
    (by simp only [List.length_singleton]; omega) (Nat.le_refl _))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_replicate]; omega)
      (by simp only [List.length_replicate]; omega) (by omega))

end


/-- A word above the frame a push writes is kept. -/
theorem push_keep {rs : List Reg} {s : State} (hrs : .esp ∉ rs) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {a : BitVec 32} (ha : (s.gpr .esp).toNat ≤ a.toNat) (ha' : a.toNat + 4 ≤ 2 ^ 32) :
    (pushed rs s).mem.readW (a.setWidth 64) 32 = s.mem.readW (a.setWidth 64) 32 := by
  refine (pushed_frame hrs hn).readW (r := ⟨a.setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inr (by rw [sub_nat hn]; omega)) ha' (by rw [sub_nat hn]; have := (s.gpr .esp).isLt; omega)

/-- The word a one-register push writes. -/
theorem push_word {r : Reg} {s : State} (hr : r ≠ .esp) (hn : 4 ≤ (s.gpr .esp).toNat) {a : BitVec 32}
    (ha : a = s.gpr .esp - BitVec.ofNat 32 4) :
    (pushed [r] s).mem.readW (a.setWidth 64) 32 = s.gpr r := by
  have := pushed_word (rs := [r]) (s := s) (by simpa using hr.symm) (by simpa using hn) (i := 0) (by simp)
  rw [pushed_esp] at this
  simp only [List.length_singleton, Nat.mul_zero, BitVec.add_zero] at this
  rw [ha]; exact this

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem entry_saved {j : Nat} (hj : j < 4) : (entry s₀).mem.readW (slot s₀ j) 32 = savedVal s₀ j := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE := (s₀.gpr .esp).isLt
  have hi : (s₀.gpr .esp).toNat + 76 ≤ 2 ^ 32 := hp.esp_hi
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have n₁ := pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton] at n₁ n₂ n₃ n₄
  have sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (s₀.gpr .esp).toNat - 16 + 4 * j := by
    rw [add_nat (by rw [sub_nat (by omega)]; omega), sub_nat (by omega)]; omega
  have eq : ∀ (x : BitVec 32), x.toNat = (s₀.gpr .esp).toNat - 16 + 4 * j →
      E s₀ + BitVec.ofNat 32 (144 + 4 * j) = x := fun x hx => BitVec.eq_of_toNat_eq (by rw [sl, hx])
  unfold entry slot
  rw [push_keep (by decide) (by simp only [List.length_replicate]; omega) (by rw [n₄, sl]; omega)
    (by rw [sl]; omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [push_word (by decide) (by omega) (eq _ (by rw [sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)]; rfl
  · rw [push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      push_word (by decide) (by omega) (eq _ (by rw [sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide)]; rfl
  · rw [push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₂, sl]; omega)
      (by rw [sl]; omega),
      push_word (by decide) (by omega) (eq _ (by rw [sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide)]
    rfl
  · rw [push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₂, sl]; omega)
      (by rw [sl]; omega),
      push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₁, sl]; omega)
      (by rw [sl]; omega),
      push_word (by decide) (by omega) (eq _ (by rw [sub_nat (by omega)]; omega))]
    rfl

end


theorem loc_mem (s₀ : State) : locR s₀ ∈ (entry s₀).wr := by
  simp [entry, pushed_wr, pushed_esp, BitVec.sub_sub, BitVec.ofNat_add_ofNat, below]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (entry s₀).wr := by
  simp only [entry, pushed_wr, List.mem_cons]
  exact .inr (.inr (.inr (.inr (.inr h))))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (entry s₀).mem s.mem

/-- A step that writes registers other than `esp` and `ebp`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (he : t.gpr .esp = s.gpr .esp)
    (hb : t.gpr .ebp = s.gpr .ebp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨he.trans h.esp, hb.trans h.ebp, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .esp) (h₂ : r ≠ .ebp) : Inv s₀ t :=
  h.step (u.other _ h₁.symm) (u.other _ h₂.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_hi : (E s₀).toNat + 236 ≤ 2 ^ 32 := by
  have := hp.esp_hi; have := hp.esp_lo; rw [sub_nat (by omega)]; omega

/-- The locals and the stack below them lie in the stack the contract reserves. -/
theorem loc_stk {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  have h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by omega), hE]
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

theorem call_stk : Region.Sub (callR s₀) (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  have h1 : (E s₀ - BitVec.ofNat 32 84).toNat = (E0 s₀).toNat - 244 := by rw [sub_nat (by omega), hE]; omega
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]) (by rw [h1, h2]; omega)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (addr (E s₀) d) 4 := by
  have := E_hi hp
  rw [h.wr]
  exact ⟨locR s₀, loc_mem s₀, contains32 (by rw [add_nat (by omega)]; omega)
    (by rw [add_nat (by omega)]; omega)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_nat : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by have := hp.esp_lo; omega)

/-- A range within the 160 bytes the frames use. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 160) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by rw [E_nat hp]; omega), E_nat hp]
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (E0 s₀).toNat + 76)
    (hm : Region.Disjoint ⟨a.setWidth 64, n⟩ (memR s₀)) (hs : Region.Disjoint ⟨a.setWidth 64, n⟩ (scrR s₀))
    (ho : Region.Disjoint ⟨a.setWidth 64, n⟩ (outR s₀)) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨a.setWidth 64, n⟩ r := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact disj32 (.inr (by omega)) (by omega) (by omega)
  · exact disj32 (.inr (by rw [sub_nat (by omega)]; omega)) (by omega)
      (by rw [sub_nat (by omega)]; omega)

theorem Inv.done {s : State} (h : Inv s₀ s) : BodyDone s₀ s := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have hE' : (E0 s₀ - BitVec.ofNat 32 160).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  refine ⟨h.esp, fun j hj => ?_, ?_⟩
  · have sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (E s₀).toNat + (144 + 4 * j) :=
      add_nat (by have := E_hi hp; omega)
    have st := frame_stk hp (d := 144 + 4 * j) (n := 4) (by omega)
    rw [h.frame.readW (r := ⟨slot s₀ j, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact entry_saved hp hj
    refine above_disj hp (by rw [sl]; omega) (by rw [sl]; omega) ?_ ?_ ?_
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
  · rw [h.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)]
    · refine entry_frame hp |>.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact disj32 (.inr (by rw [sub_nat (by omega)]; omega)) (by omega) (by rw [sub_nat (by omega)]; omega)
    refine above_disj hp (by omega) (by omega) ?_ ?_ ?_
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)

/-- The arguments' addresses, from `ebp`. -/
theorem arg_addr {i : Nat} (hi : i < 18) :
    addr (E s₀) (Impl.Argon2.X86.Derive.argOff i) = argAddr s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  simp only [addr, argAddr, Impl.Argon2.X86.Derive.argOff, Impl.Argon2.X86.Derive.locals]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [add_nat (by omega), add_nat (by omega)]
  show (E0 s₀ - BitVec.ofNat 32 160).toNat + _ = (E0 s₀).toNat + _
  rw [sub_nat (by omega)]; omega

theorem arg_word {i : Nat} (hi : i < 18) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  exact sub32 (by rw [add_nat (by omega), add_nat (by omega)]; omega)
    (by rw [add_nat (by omega), add_nat (by omega)]; omega)

theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 4 := by
  rw [arg_addr hp hi, h.rd, hp.rd]
  exact ⟨argR s₀, by simp, arg_word hp hi (argAddr s₀ i) |> fun _ => by
    have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    exact contains32 (by rw [add_nat (by omega), add_nat (by omega)]; omega)
      (by rw [add_nat (by omega), add_nat (by omega)]; omega)⟩

theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 32 = arg s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have ai : (E0 s₀ + BitVec.ofNat 32 (4 + 4 * i)).toNat = (E0 s₀).toNat + 4 + 4 * i := by
    rw [add_nat (by omega)]; omega
  rw [arg_addr hp hi]
  have sub := arg_word hp hi
  rw [h.frame.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · refine (entry_frame hp).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact disj32 (.inr (by rw [sub_nat (by omega), ai]; omega)) (by rw [ai]; omega)
      (by rw [sub_nat (by omega)]; omega)
  refine above_disj hp (by rw [ai]; omega) (by rw [ai]; omega) ?_ ?_ ?_
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : Inv s₀ s) {R : Region}
    (hR : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hR' : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have hS : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have stk := (hp.stk_all R hS).symm
  have hl : R.len ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (frame_stk hp (d := 0) (n := 160) (by decide) |> fun hs => by
        simpa using hs)) hl hi
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (call_stk hp)

end

end VG.Proof.Argon2.X86.Derive
