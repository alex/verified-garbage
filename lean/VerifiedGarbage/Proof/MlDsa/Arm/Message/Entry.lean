import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: entry and exit

Untrusted: everything here is checked by Lean. Stores of registers at
distinct offsets that are multiples of 4 from a base (`strs_ok`), and loads
of words on the stack into distinct registers (`lds_ok`). The entry: the
caller's `r7` kept in the first word of `scratch`, the address of `X` in
`r7`, the caller's `r7` and `lr` saved at `X + 904` and `X + 908`, the
arguments at `X + 912 + 4j` and `0 ‖ ctx_len` at `X + 944`, give `Ctx`
(`enter_ok`). The exit restores `lr` and `r7` (`leave_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-- Registers, permissions and stack pointer unchanged. -/
structure Same (t t' : State) : Prop where
  gpr : t'.gpr = t.gpr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Same.of_memTo {a b : State} {m : Mem} (h : MemTo a b m) : Same a b := ⟨h.gpr, h.rd, h.wr, h.sp⟩

/-- Stores of registers at distinct offsets, multiples of 4, from `B` in `b`. -/
theorem strs_ok (b : Reg) (B : BitVec 32) (XB : Addr)
    (hB : ∀ o, o + 4 ≤ 1024 → State.addr (B + BitVec.ofNat 32 o) = XB + BitVec.ofNat 64 o) :
    ∀ (as : List (Reg × Nat)) (t : State), t.gpr b = B →
    (∀ a ∈ as, a.2 % 4 = 0 ∧ a.2 + 4 ≤ 1024 ∧ InRegions t.wr (XB + BitVec.ofNat 64 a.2) 4) →
    (as.map (·.2)).Nodup →
    WP isa (.block (as.map fun a => .str a.1 b a.2)) t fun t' => Same t t' ∧
      (∀ a ∈ as, t'.mem.readW (XB + BitVec.ofNat 64 a.2) 32 = t.gpr a.1) ∧
      Frame (as.map fun a => ⟨XB + BitVec.ofNat 64 a.2, 4⟩) t.mem t'.mem
  | [], t, _, _, _ => wp_nil ⟨Same.refl t, fun _ h => by simp at h, Frame.refl _ _⟩
  | (r, f) :: as, t, hb, ha, hn => by
    have h0 := ha (r, f) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have ea : State.addr (t.gpr b + BitVec.ofNat 32 f) = XB + BitVec.ofNat 64 f := by rw [hb]; exact hB f h0.2.1
    refine wp_str (by omega) (by rw [ea]; exact h0.2.2) fun s1 m1 => ?_
    have hs1 := Same.of_memTo m1
    refine WP.mono (strs_ok b B XB hB as s1 (by rw [hs1.gpr, hb]) (fun a h => by
      rw [hs1.wr]; exact ha a (List.mem_cons_of_mem _ h)) hn.2) fun t' ⟨hs, hr, hf⟩ => ⟨hs1.trans hs, ?_, ?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [hf.readW (r := ⟨XB + BitVec.ofNat 64 f, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_map] at hr'
            obtain ⟨a', ha', rfl⟩ := hr'
            have := ha a' (List.mem_cons_of_mem _ ha')
            have hne : f ≠ a'.2 := fun e => hn.1 ⟨a', ha', e.symm⟩
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
          m1.mem, ea, Mem.readW_writeW_self32]
      · rw [hr a h, hs1.gpr]
    · have f1 : Frame [⟨XB + BitVec.ofNat 64 f, 4⟩] t.mem s1.mem := by
        rw [m1.mem, ea]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine (f1.mono fun r h => ?_).trans (hf.mono fun r h => ?_)
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ h

/-- Loads of words on the stack into distinct registers. -/
theorem lds_ok : ∀ (ss : List (Reg × Nat)) (t : State), (ss.map (·.1)).Nodup →
    (∀ a ∈ ss, a.2 < 4096 ∧ InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 a.2)) 4) →
    WP isa (.block (ss.map fun a => .ldrSp a.1 a.2)) t fun t' => Only (ss.map (·.1)) t t' ∧
      ∀ a ∈ ss, t'.gpr a.1 = t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 a.2)) 32
  | [], t, _, _ => wp_nil ⟨Only.refl _ _, fun _ h => by simp at h⟩
  | (r, o) :: ss, t, hn, ha => by
    have h0 := ha (r, o) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine wp_ldrSp h0.1 h0.2 fun s1 o1 e1 => ?_
    refine WP.mono (lds_ok ss s1 hn.2 fun a h => by
      rw [o1.rd, o1.wr, o1.sp]; exact ha a (List.mem_cons_of_mem _ h)) fun t' ⟨o, hv⟩ => ⟨?_, ?_⟩
    · exact (o1.mono fun x hx => by simp only [List.mem_singleton] at hx; simp [hx]).trans
        (o.mono fun x hx => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx)
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [o.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact hn.1 ⟨x, hx', hx''⟩), e1]
      · rw [hv a h, o1.mem, o1.sp]

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  have e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e1, e2]; exact movw_movt _

theorem regSaves_ok : ∀ a ∈ regSaves, a.2 % 4 = 0 ∧ 904 ≤ a.2 ∧ a.2 + 4 ≤ 928 := by decide
theorem stkSaves_ok : ∀ a ∈ stkSaves, a.2 % 4 = 0 ∧ 928 ≤ a.2 ∧ a.2 + 4 ≤ 944 := by decide

/-- The entry, from a state whose registers and stack hold the layout's values. -/
theorem enter_ok {L : Lay} (hL : L.Ok) {p : Spec.MlDsa.Params} (hE : oE p = L.E) {so nA : Nat}
    {ss : List (Reg × Nat)} (hss : ss.map (·.1) = [.r0, .r1, .r2, .r3]) (hnA : nA ≤ 16) {s : State}
    (hsp : s.sp = L.SP) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (h0 : s.gpr .r0 = L.key) (h1 : s.gpr .r1 = L.msg) (h2 : s.gpr .r2 = L.len) (h3 : s.gpr .r3 = L.ctx)
    (hA : ∀ o, o + 4 ≤ nA → InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4)
    (hfA : s.sp.toNat + nA ≤ 2 ^ 32) (hdA : L.SC.Disjoint ⟨State.addr s.sp, nA⟩)
    (hso : so + 4 ≤ nA) (hscr : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 so)) 32 = L.scr)
    (hsa : ∀ a ∈ ss, a.2 + 4 ≤ nA)
    (hv : ∀ j (hj : j < ss.length), s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (ss[j]'hj).2)) 32 =
      L.vals.getD (4 + j) 0) :
    WP isa (.block (enter so p ss)) s fun t => Ctx L s.gpr s.mem t := by
  have hlen : ss.length = 4 := by rw [← List.length_map (f := (·.1)), hss]; rfl
  have hscL := hL.hE
  -- Words on the stack: in the arguments' region, apart from `scratch`.
  have estk : ∀ o, o + 4 ≤ nA → State.addr (s.sp + BitVec.ofNat 32 o) = State.addr s.sp + BitVec.ofNat 64 o :=
    fun o ho => addr_add (by omega)
  have dstk : ∀ o, o + 4 ≤ nA → L.SC.Disjoint ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩ := fun o ho => by
    rw [estk o ho]; exact hdA.sub_right (Offset.sub_base _ ho)
  have sc0 : State.addr (L.scr + BitVec.ofNat 32 0) = State.addr L.scr := by rw [BitVec.add_zero]
  have hsc4 : Region.Sub ⟨State.addr L.scr, 4⟩ L.SC := by
    have := Offset.sub_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega)
    simpa only [BitVec.add_zero] using this
  have csc : L.SC.Contains (State.addr L.scr) 4 := by
    simpa using (Offset.contains_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega) (by omega))
  have isc : InRegions L.wr (State.addr L.scr) 4 := ⟨L.SC, hL.inSC, csc⟩
  unfold enter
  simp only [List.append_assoc]
  -- `scratch` in `r12`, the caller's `r7` in its first word.
  refine wp_ldrSp (by omega) (hA so hso) fun s1 o1 e1 => ?_
  rw [hscr] at e1
  refine wp_str (by decide) (by rw [e1, sc0, o1.wr, hwr]; exact isc) fun s2 m2 => ?_
  have q2 := Same.of_memTo m2
  -- `X` in `r7`.
  refine wp_movw fun s3 o3 e3 => wp_movt fun s4 o4 e4 => wp_addReg fun s5 o5 e5 => ?_
  rw [o4.get .r12, o3.get .r12, q2.gpr, e1, e4, e3, movi_val, hE] at e5
  -- The caller's `r7` back in `r12`.
  have m5 : s5.mem = s1.mem.writeW (State.addr L.scr) (s.gpr .r7) := by
    rw [o5.mem, o4.mem, o3.mem, m2.mem, e1, sc0, o1.get .r7]
  have r12_5 : s5.gpr .r12 = L.scr := by rw [o5.get .r12, o4.get .r12, o3.get .r12, q2.gpr, e1]
  refine wp_ldr (by decide) (by
      rw [r12_5, sc0, o5.rd, o5.wr, o4.rd, o4.wr, o3.rd, o3.wr, q2.rd, q2.wr, o1.rd, o1.wr, hrd, hwr]
      exact ⟨L.SC, List.mem_append_right _ hL.inSC, csc⟩) fun s6 o6 e6 => ?_
  rw [r12_5, sc0, m5, Mem.readW_writeW_self32] at e6
  have e76 : s6.gpr .r7 = L.X32 := by rw [o6.get .r7, e5]
  have hw6 : s6.wr = L.wr := by rw [o6.wr, o5.wr, o4.wr, o3.wr, q2.wr, o1.wr, hwr]
  -- The registers.
  have g6 : ∀ r, r ≠ .r7 → r ≠ .r12 → s6.gpr r = s.gpr r := fun r h7 h12 => by
    rw [o6.get r (by simpa using h12), o5.get r (by simpa using h7), o4.get r (by simpa using h7),
      o3.get r (by simpa using h7), q2.gpr, o1.get r (by simpa using h12)]
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  have hxo : ∀ o, o + 4 ≤ 1024 → State.addr (L.X32 + BitVec.ofNat 32 o) = L.X + BitVec.ofNat 64 o :=
    fun o ho => hL.xo (by omega)
  refine WP.mono (strs_ok .r7 L.X32 L.X hxo regSaves s6 e76 (fun a ha => by
    have := regSaves_ok a ha; exact ⟨this.1, by omega, by rw [hw6]; exact hL.inW (by omega)⟩) (by decide))
    fun s7 ⟨q7, r7, f7⟩ => ?_
  rw [WP.block_append_iff]
  -- The arguments on the stack, unchanged since the entry.
  have m7 : ∀ o, o + 4 ≤ nA → s7.mem.readW (State.addr (s7.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun o ho => by
    have hs7 : s7.sp = s.sp := by rw [q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp]
    rw [hs7, f7.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := regSaves_ok a ha
      exact ((dstk o ho).sub_left (hL.sub_sc (e := a.2) (k := 4) (by omega))).symm) (by decide), o6.mem, m5,
      Mem.readW_writeW_sep (fun x h1 h2 => (dstk o ho).symm x h1 (hsc4 x h2)) (by decide), o1.mem]
  refine WP.mono (lds_ok ss s7 (by rw [hss]; decide) fun a ha => ⟨by have := hsa a ha; omega, by
    rw [q7.rd, q7.wr, q7.sp, o6.rd, o6.wr, o6.sp, o5.rd, o5.wr, o5.sp, o4.rd, o4.wr, o4.sp, o3.rd, o3.wr, o3.sp,
      q2.rd, q2.wr, q2.sp, o1.rd, o1.wr, o1.sp]; exact hA _ (hsa a ha)⟩) fun s8 ⟨o8, v8⟩ => ?_
  rw [hss] at o8
  -- The values loaded.
  have hl8 : ∀ j (hj : j < ss.length), s8.gpr (ss[j]'hj).1 = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [v8 _ (List.getElem_mem hj), m7 _ (hsa _ (List.getElem_mem hj)), hv j hj]
  have hreg : ∀ j (hj : j < ss.length), (ss[j]'hj).1 = [Reg.r0, .r1, .r2, .r3].getD j .r0 := fun j hj => by
    have := congrArg (·[j]?) hss
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at this
    rw [List.getD_eq_getElem?_getD, ← this, Option.getD_some]
  have l8 : ∀ j < 4, s8.gpr ([Reg.r0, .r1, .r2, .r3].getD j .r0) = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [← hreg j (by omega)]; exact hl8 j (by omega)
  have hw8 : s8.wr = L.wr := by rw [o8.wr, q7.wr, hw6]
  have e78 : s8.gpr .r7 = L.X32 := by rw [o8.get .r7, q7.gpr, e76]
  rw [WP.block_append_iff]
  refine WP.mono (strs_ok .r7 L.X32 L.X hxo stkSaves s8 e78 (fun a ha => by
    have := stkSaves_ok a ha; exact ⟨this.1, by omega, by rw [hw8]; exact hL.inW (by omega)⟩) (by decide))
    fun s9 ⟨q9, r9, f9⟩ => ?_
  -- `0 ‖ ctx_len`.
  have e79 : s9.gpr .r7 = L.X32 := by rw [q9.gpr, e78]
  simp only [oHdr, Nat.reduceAdd]
  refine wp_movImm (d := .r12) (v := 0) (by decide) fun s10 o10 e10 => ?_
  refine wp_strb (by decide) (by rw [o10.get .r7, e79, hxo 944 (by omega), o10.wr, q9.wr, hw8]; exact hL.inW (by omega))
    fun s11 m11 => ?_
  have q11 := Same.of_memTo m11
  refine wp_strb (by decide)
    (by rw [q11.gpr, o10.get .r7, e79, hxo 945 (by omega), q11.wr, o10.wr, q9.wr, hw8]; exact hL.inW (by omega))
    fun s12 m12 => wp_nil ?_
  have q12 := Same.of_memTo m12
  have x0_12 : s11.gpr .r0 = L.ctxLen := by
    rw [q11.gpr, o10.get .r0, q9.gpr]
    have := l8 0 (by omega); simpa [Lay.vals] using this
  have m12e : s12.mem = (s9.mem.writeW (L.X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
      (L.X + BitVec.ofNat 64 945) (L.ctxLen.setWidth 8) := by
    rw [m12.mem, m11.mem, o10.mem, q11.gpr, o10.get .r7, e79, e10, hxo 944 (by omega), hxo 945 (by omega),
      ← q11.gpr, x0_12]
  -- Reads of the saves.
  have hdr2 : ∀ d, d + 4 ≤ 40 → s12.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [m12e, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
  have r9' : ∀ d, d + 4 ≤ 24 → s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s7.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [f9.readW (r := ⟨L.X + BitVec.ofNat 64 (904 + d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := stkSaves_ok a ha
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), o8.mem]
  have hX := hL.x_toNat
  refine ⟨by rw [q12.rd, q11.rd, o10.rd, q9.rd, o8.rd, q7.rd, o6.rd, o5.rd, o4.rd, o3.rd, q2.rd, o1.rd, hrd],
    by rw [q12.wr, q11.wr, o10.wr, q9.wr, hw8],
    by rw [q12.sp, q11.sp, o10.sp, q9.sp, o8.sp, q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp, hsp],
    by rw [q12.gpr, q11.gpr, o10.get .r7, e79], fun r hr h7 hl => ?_, ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · have hn : r ∉ [Reg.r0, .r1, .r2, .r3, .r12] := fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> revert hr <;> decide
    rw [q12.gpr, q11.gpr, o10.get r (by simp at hn ⊢; exact hn.2.2.2.2), q9.gpr,
      o8.get r (by simp at hn ⊢; exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩), q7.gpr,
      g6 r h7 (by simp at hn; exact hn.2.2.2.2)]
  · rw [hdr2 0 (by omega), r9' 0 (by omega)]; exact (r7 (.r12, oR7) (by decide)).trans e6
  · rw [hdr2 4 (by omega), r9' 4 (by omega)]
    exact (r7 (.lr, oLR) (by decide)).trans (g6 .lr (by decide) (by decide))
  · rw [hdr2 _ (by omega)]
    rcases (by omega : j < 4 ∨ 4 ≤ j) with hj4 | hj4
    · rw [r9' _ (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · refine (r7 (.r0, fKey) (by decide)).trans ?_; rw [g6 .r0 (by decide) (by decide), h0]; rfl
      · refine (r7 (.r1, fMsg) (by decide)).trans ?_; rw [g6 .r1 (by decide) (by decide), h1]; rfl
      · refine (r7 (.r2, fLen) (by decide)).trans ?_; rw [g6 .r2 (by decide) (by decide), h2]; rfl
      · refine (r7 (.r3, fCtx) (by decide)).trans ?_; rw [g6 .r3 (by decide) (by decide), h3]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, j = 4 + k := ⟨j - 4, by omega⟩
      have hk : k < 4 := by omega
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · exact (r9 (.r0, fCtxLen) (by decide)).trans (l8 0 (by omega))
      · exact (r9 (.r1, fRnd) (by decide)).trans (l8 1 (by omega))
      · exact (r9 (.r2, fSig) (by decide)).trans (l8 2 (by omega))
      · exact (r9 (.r3, fScr) (by decide)).trans (l8 3 (by omega))
  · have n45 : L.X + BitVec.ofNat 64 944 ≠ L.X + BitVec.ofNat 64 945 :=
      Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    rw [show 904 + 40 = 944 from rfl, m12e]
    generalize L.X = X at n45 ⊢
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
    rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · -- Memory changed only in `scratch`.
    have a2 : Frame [L.SC, L.STK] s.mem s5.mem := by
      rw [m5, o1.mem]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ csc
    have a7 : Frame [L.SC, L.STK] s6.mem s7.mem := Frame.sub f7 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := regSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega)⟩
    have a9 : Frame [L.SC, L.STK] s8.mem s9.mem := Frame.sub f9 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := stkSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega)⟩
    have a12 : Frame [L.SC, L.STK] s9.mem s12.mem := by
      rw [m12e]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hL.sub_sc (e := 944) (k := 1) (by omega) _
          (Region.contains_self _ _))).writeW
        (List.mem_cons_self ..) _ (hL.sub_sc (e := 945) (k := 1) (by omega) _ (Region.contains_self _ _))
    rw [o6.mem] at a7
    rw [o8.mem] at a9
    exact a2.trans (a7.trans (a9.trans a12))

/-- What the exit needs: `r7` pointing at `X`, the callee-saved registers
but `r7` and `lr`, and the saves of those two. -/
structure Fin (L : Lay) (g : Reg → BitVec 32) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  r7 : t.gpr .r7 = L.X32
  cs : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → t.gpr r = g r
  s7 : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 0)) 32 = g .r7
  sLR : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 4)) 32 = g .lr

theorem Ctx.fin {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) : Fin L g t :=
  ⟨hc.rd, hc.wr, hc.sp, hc.r7, hc.cs, hc.s7, hc.sLR⟩

/-- The exit: `lr`, then `r7`, from the saves. -/
theorem leave_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {t : State} (hc : Fin L g t) :
    WP isa (.block leave) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = L.SP ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hx : ∀ f, f + 4 ≤ 1024 → InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 f) 4 := fun f hf => by
    obtain ⟨R, hR, hc'⟩ := hL.inW (e := f) (k := 4) hf
    exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩
  refine wp_ldr (by decide) (by rw [hc.r7, hL.xo (by decide)]; exact hx 908 (by omega)) fun t1 o1 e1 => ?_
  refine wp_ldr (by decide) (by rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.rd, o1.wr]; exact hx 904 (by omega))
    fun t2 o2 e2 => wp_nil ?_
  rw [hc.r7, hL.xo (by decide)] at e1
  rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.mem] at e2
  refine ⟨fun r hr => ?_, by rw [o2.sp, o1.sp, hc.sp], by rw [o2.mem, o1.mem], by rw [o2.get .r0, o1.get .r0],
    by rw [o2.rd, o1.rd], by rw [o2.wr, o1.wr]⟩
  by_cases e7 : r = .r7
  · subst e7; rw [e2]; exact hc.s7
  · by_cases el : r = .lr
    · subst el; rw [o2.get .lr, e1]; exact hc.sLR
    · rw [o2.get r (by simpa using e7), o1.get r (by simpa using el), hc.cs r hr e7 el]

end VG.Proof.MlDsa.Arm.Message
