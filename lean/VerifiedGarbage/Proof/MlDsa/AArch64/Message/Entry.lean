import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: entry and exit

Untrusted: everything here is checked by Lean. Stores of registers at
distinct offsets that are multiples of 8 from a base (`strs_ok`). The entry:
the address of `X` in `x9` and then `x28`, the caller's `x28` and `x30`
saved at `X + 904` and `X + 912`, the arguments at `X + 920 + 8j` and
`0 ‖ ctx_len` at `X + 984`, give `Ctx` (`enter_ok`). The exit restores
`x30` and `x28` (`leave_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only MemTo wp_nil wp_strx wp_strb wp_ldrx wp_movz wp_add wp_addImm wp_movImm)
open VG.Spec.Sha3 (bytesAt)

/-- Registers, permissions, stack pointer and SIMD registers unchanged. -/
structure Same (t t' : State) : Prop where
  gpr : t'.gpr = t.gpr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  vcs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem Same.of_memTo {a b : State} {m : Mem} (h : MemTo a b m) : Same a b := ⟨h.gpr, h.rd, h.wr, h.sp, h.vcs⟩

/-- Stores of registers at distinct offsets, multiples of 8, from `B` in `b`. -/
theorem strs_ok (b : Reg) (B : Addr) : ∀ (as : List (Reg × Nat)) (t : State), t.gpr b = B →
    (∀ a ∈ as, a.2 % 8 = 0 ∧ a.2 + 8 ≤ 4096 ∧ InRegions t.wr (B + BitVec.ofNat 64 a.2) 8) →
    (as.map (·.2)).Nodup →
    WP isa (.block (as.map fun a => .str .x a.1 b a.2)) t fun t' => Same t t' ∧
      (∀ a ∈ as, t'.mem.readW (B + BitVec.ofNat 64 a.2) 64 = t.gpr a.1) ∧
      Frame (as.map fun a => ⟨B + BitVec.ofNat 64 a.2, 8⟩) t.mem t'.mem
  | [], t, _, _, _ => wp_nil ⟨Same.refl t, fun _ h => by simp at h, Frame.refl _ _⟩
  | (r, f) :: as, t, hb, ha, hn => by
    have h0 := ha (r, f) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine wp_strx ⟨h0.1, by omega⟩ (by rw [hb]) h0.2.2 fun s1 m1 => ?_
    have hs1 := Same.of_memTo m1
    refine WP.mono (strs_ok b B as s1 (by rw [hs1.gpr, hb]) (fun a h => by
      rw [hs1.wr]; exact ha a (List.mem_cons_of_mem _ h)) hn.2) fun t' ⟨hs, hr, hf⟩ => ⟨hs1.trans hs, ?_, ?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [hf.readW (r := ⟨B + BitVec.ofNat 64 f, 8⟩) (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_map] at hr'
            obtain ⟨a', ha', rfl⟩ := hr'
            have := ha a' (List.mem_cons_of_mem _ ha')
            have hne : f ≠ a'.2 := fun e => hn.1 ⟨a', ha', e.symm⟩
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
          m1.mem, Mem.readW_writeW_self64]
      · rw [hr a h, hs1.gpr]
    · have f1 : Frame [⟨B + BitVec.ofNat 64 f, 8⟩] t.mem s1.mem := by
        rw [m1.mem]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine (f1.mono fun r h => ?_).trans (hf.mono fun r h => ?_)
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ h

theorem byte_writeW_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  have h := Mem.readW_writeW_self m a 1 v (by decide)
  have h1 := Proof.MlKem.AArch64.read_one (m.writeW a v) a
  simp only [Mem.readW, BitVec.setWidth_eq] at h
  rw [← h1]
  exact h

theorem byte_writeW_other {m : Mem} {a x : Addr} (v : BitVec 8) (h : x ≠ a) : (m.writeW a v) x = m x := by
  simp only [Mem.writeW]
  refine Mem.write_apply fun hl => h ?_
  have : (x - a).toNat = 0 := by simp only [Nat.reduceDiv] at hl; omega
  have e := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [this]; rfl)
  rw [← BitVec.sub_add_cancel x a, e]
  simp

/-- The values the entry saves at `X + 920 + 8j`, and the registers they are in. -/
theorem saves_ok {as : List (Reg × Nat)} (hf : as.map (·.2) = [920, 928, 936, 944, 952, 960, 968, 976]) :
    ∀ a ∈ as, a.2 % 8 = 0 ∧ 920 ≤ a.2 ∧ a.2 + 8 ≤ 984 := by
  intro a ha
  have : a.2 ∈ as.map (·.2) := List.mem_map_of_mem ha
  rw [hf] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-- The entry, from a state whose registers hold the layout's values. -/
theorem enter_ok {L : Lay} (hL : L.Ok) {p : Spec.MlDsa.Params} (hE : oE p = L.E) {sr : Reg}
    (hsr : sr ≠ .x9) {as : List (Reg × Nat)} (hf : as.map (·.2) = [920, 928, 936, 944, 952, 960, 968, 976])
    {s : State} (hs : s.gpr sr = L.scr) (hsp : s.sp = L.SP) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (h4 : s.gpr .x4 = L.ctxLen) (hv : ∀ j (hj : j < as.length), s.gpr (as[j]'hj).1 = L.vals.getD j 0)
    (hreg : ∀ a ∈ as, a.1 ≠ .x9 ∧ a.1 ≠ .x28) :
    WP isa (.block (enter sr p as)) s fun t => Ctx L s.gpr s.v s.mem t := by
  have hlen : as.length = 8 := by rw [← List.length_map (f := (·.2)), hf]; rfl
  have hsv := saves_ok hf
  unfold enter
  simp only [List.append_assoc]
  refine wp_movImm fun s1 o1 e1 => ?_
  rw [List.singleton_append]
  refine wp_add fun s2 o2 e2 => ?_
  rw [o1.get sr (by simpa using hsr), e1, hs] at e2
  -- `X` in `x9`.
  have eX : s2.gpr .x9 = L.X := by rw [e2, hE]
  rw [WP.block_append_iff]
  have hw2 : s2.wr = L.wr := by rw [o2.wr, o1.wr, hwr]
  refine WP.mono (strs_ok .x9 L.X [(.x28, 904), (.x30, 912)] s2 eX (fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by decide, by decide, by rw [hw2]; exact hL.inW (by omega) (by omega)⟩
    · exact ⟨by decide, by decide, by rw [hw2]; exact hL.inW (by omega) (by omega)⟩) (by decide))
    fun s3 ⟨q3, r3, f3⟩ => ?_
  refine wp_addImm (by decide) fun s4 o4 e4 => ?_
  rw [q3.gpr, eX, BitVec.add_zero] at e4
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  have hw4 : s4.wr = L.wr := by rw [o4.wr, q3.wr, hw2]
  refine WP.mono (strs_ok .x28 L.X as s4 e4 (fun a ha => ⟨(hsv a ha).1, by have := hsv a ha; omega,
    by rw [hw4]; have := hsv a ha; exact hL.inW (by omega) (by omega)⟩) (by rw [hf]; decide))
    fun s5 ⟨q5, r5, f5⟩ => ?_
  have hw5 : s5.wr = L.wr := by rw [q5.wr, hw4]
  have e5 : s5.gpr .x28 = L.X := by rw [q5.gpr, e4]
  refine wp_movz fun s6 o6 e6 => wp_strb (a := L.X + BitVec.ofNat 64 984) (by decide) (by rw [o6.get .x28, e5]; rfl)
    (by rw [o6.wr, hw5]; exact hL.inW (by omega) (by omega)) fun s7 m7 => ?_
  have q7 := Same.of_memTo m7
  refine wp_strb (a := L.X + BitVec.ofNat 64 985) (by decide) (by rw [q7.gpr, o6.get .x28, e5]; rfl)
    (by rw [q7.wr, o6.wr, hw5]; exact hL.inW (by omega) (by omega)) fun s8 m8 => wp_nil ?_
  have q8 := Same.of_memTo m8
  -- The registers.
  have g8 : ∀ r, r ≠ .x9 → r ≠ .x28 → s8.gpr r = s.gpr r := fun r h9 h28 => by
    rw [q8.gpr, q7.gpr, o6.get r (by simpa using h9), q5.gpr, o4.get r (by simpa using h28), q3.gpr,
      o2.get r (by simpa using h9), o1.get r (by simpa using h9)]
  have x48 : s8.gpr .x4 = L.ctxLen := by rw [g8 .x4 (by decide) (by decide), h4]
  -- The memory.
  have m8e : s8.mem = (s5.mem.writeW (L.X + BitVec.ofNat 64 984) ((s6.gpr .x9).setWidth 8)).writeW
      (L.X + BitVec.ofNat 64 985) ((s7.gpr .x4).setWidth 8) := by
    rw [m8.mem, m7.mem, o6.mem, q7.gpr]
  have hdr2 : ∀ d, d + 8 ≤ 80 → s8.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 =
      s5.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 := fun d hd => by
    rw [m8e, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
  -- Reads of the saves, from `s5`.
  have r5' : ∀ d, d + 8 ≤ 16 → s5.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 =
      s3.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 64 := fun d hd => by
    rw [f5.readW (r := ⟨L.X + BitVec.ofNat 64 (904 + d), 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := hsv a ha
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), o4.mem]
  have sx28 : s3.mem.readW (L.X + BitVec.ofNat 64 904) 64 = s.gpr .x28 := by
    rw [r3 (.x28, 904) (by simp), o2.get .x28, o1.get .x28]
  have sx30 : s3.mem.readW (L.X + BitVec.ofNat 64 912) 64 = s.gpr .x30 := by
    rw [r3 (.x30, 912) (by simp), o2.get .x30, o1.get .x30]
  have hX := hL.nX
  refine ⟨by rw [q8.rd, q7.rd, o6.rd, q5.rd, o4.rd, q3.rd, o2.rd, o1.rd, hrd],
    by rw [q8.wr, q7.wr, o6.wr, hw5], by rw [q8.sp, q7.sp, o6.sp, q5.sp, o4.sp, q3.sp, o2.sp, o1.sp, hsp],
    by rw [q8.gpr, q7.gpr, o6.get .x28, e5], fun r hr h28 _ => g8 r (fun e => by subst e; revert hr; decide) h28,
    fun r hr => by rw [q8.vcs r hr, q7.vcs r hr, o6.vcs r hr, q5.vcs r hr, o4.vcs r hr, q3.vcs r hr, o2.vcs r hr,
      o1.vcs r hr], ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [add_add, hdr2 0 (by omega), r5' 0 (by omega)]; exact sx28
  · rw [add_add, hdr2 8 (by omega), r5' 8 (by omega)]; exact sx30
  · have hj' : j < as.length := by omega
    have hm : as[j] ∈ as := List.getElem_mem hj'
    have hf2 : as[j].2 = 920 + 8 * j := by
      have := congrArg (·[j]?) hf
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some] at this
      have hj8 : j < 8 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using this
    rw [add_add, hdr2 (16 + 8 * j) (by omega), show 904 + (16 + 8 * j) = as[j].2 by omega, r5 _ hm,
      o4.get _ (by simpa using (hreg _ hm).2), q3.gpr, o2.get _ (by simpa using (hreg _ hm).1),
      o1.get _ (by simpa using (hreg _ hm).1)]
    exact hv j hj'
  · have n45 : L.X + BitVec.ofNat 64 984 ≠ L.X + BitVec.ofNat 64 985 :=
      Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    have x46 : s6.gpr .x4 = L.ctxLen := by rw [o6.get .x4, q5.gpr, o4.get .x4, q3.gpr, o2.get .x4, o1.get .x4, h4]
    rw [add_add, m8e, q7.gpr, x46, e6]
    generalize L.X = X at n45 ⊢
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
    rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · have hs1 : s.mem = s2.mem := by rw [o2.mem, o1.mem]
    have hxs : ∀ d n, d + n ≤ 1024 → Region.Sub ⟨L.X + BitVec.ofNat 64 d, n⟩ L.XS := fun d n h =>
      Offset.sub_base _ h
    have a3 : Frame [L.XS, L.STK] s2.mem s3.mem := Frame.sub f3 fun r hr => by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.XS, by simp, hxs 904 8 (by omega)⟩
      · exact ⟨L.XS, by simp, hxs 912 8 (by omega)⟩
    have a5 : Frame [L.XS, L.STK] s4.mem s5.mem := Frame.sub f5 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := hsv a ha
      exact ⟨L.XS, by simp, hxs a.2 8 (by omega)⟩
    have a8 : Frame [L.XS, L.STK] s5.mem s8.mem := by
      rw [m8e]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))).writeW
        (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))
    rw [hs1]
    exact a3.trans ((by rw [o4.mem] : Frame [L.XS, L.STK] s3.mem s4.mem ↔ _).mpr (Frame.refl _ _) |>.trans
      (a5.trans a8))

/-- What the exit needs: `x28` pointing at `X`, the callee-saved registers
but `x28` and `x30`, and the saves of those two. -/
structure Fin (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  x28 : t.gpr .x28 = L.X
  cs : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  s28 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 0) 64 = g .x28
  s30 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 8) 64 = g .x30

theorem Ctx.fin {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) : Fin L g vv t :=
  ⟨hc.rd, hc.wr, hc.sp, hc.x28, hc.cs, hc.vs, hc.s28, hc.s30⟩

/-- The exit: `x30`, then `x28`, from the saves. -/
theorem leave_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {t : State}
    (hc : Fin L g vv t) :
    WP isa (.block leave) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = L.SP ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64) ∧ t'.mem = t.mem ∧
      t'.gpr .x0 = t.gpr .x0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h30 := hc.s30
  have h28 := hc.s28
  rw [add_add] at h30 h28
  have hx : ∀ f, f + 8 ≤ 1024 → InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 f) 8 := fun f hf => by
    obtain ⟨R, hR, hc'⟩ := hL.inW (e := f) (k := 8) hf (by omega)
    exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩
  refine wp_ldrx (a := L.X + BitVec.ofNat 64 (904 + 8)) (by decide) (by rw [hc.x28]; rfl)
    (hx 912 (by omega)) fun t1 o1 e1 => ?_
  refine wp_ldrx (a := L.X + BitVec.ofNat 64 (904 + 0)) (by decide) (by rw [o1.get .x28, hc.x28]; rfl)
    (by rw [o1.rd, o1.wr]; exact hx 904 (by omega)) fun t2 o2 e2 => wp_nil ?_
  refine ⟨fun r hr => ?_, by rw [o2.sp, o1.sp, hc.sp], fun r hr => by rw [o2.vcs r hr, o1.vcs r hr, hc.vs r hr],
    by rw [o2.mem, o1.mem], by rw [o2.get .x0, o1.get .x0], by rw [o2.rd, o1.rd], by rw [o2.wr, o1.wr]⟩
  by_cases e28 : r = .x28
  · subst e28; rw [e2, o1.mem, h28]
  · by_cases e30 : r = .x30
    · subst e30; rw [o2.get .x30, e1, h30]
    · rw [o2.get r (by simpa using e28), o1.get r (by simpa using e30), hc.cs r hr e28 e30]

end VG.Proof.MlDsa.AArch64.Message
