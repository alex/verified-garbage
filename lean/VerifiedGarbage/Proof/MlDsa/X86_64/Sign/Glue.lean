import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Call

/-!
# ML-DSA signing on x86-64: the moves of a call's arguments

Untrusted: everything here is checked by Lean. `setArgs as` moves each
argument (a pointer or an immediate) into its register: afterwards each
argument register holds the argument's value in the state before the moves
(`setArgs_ok`), and nothing else changed but those registers. With it, a
call of verified code (`callP_ok`, `callP_tr`, `callPRet_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)
open VG.Spec.MlDsa

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => pa s p
  | .imm v => BitVec.ofNat 64 v

/-- A pointer in a register of `bases`, with an offset that is an
immediate; or an immediate of 32 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ bases) && decide (p.2 < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 32)

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => (s1.gpr d = a.val s ∧ s1.mem = s.mem) ∧ Keep [d] s s1 := by
  have hd' : d ∉ bases := fun h => by revert h hd; cases d <;> decide
  refine WP.keep [d] ?_ (by cases a <;> cases d <;> rfl)
  cases a with
  | ptr p =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    have hne : p.1 ≠ d := fun e => hd' (e ▸ ha.1)
    simp only [Arg.mov, lea, Arg.val]
    xrun [sx_ofNat ha.2]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, movi, Arg.val]
    xrun [sw_ofNat ha]

theorem Keep.of_sub {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' := h.mono hs

theorem setArgsGen_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs6) →
    as.all Arg.ok = true → ∀ s : State,
    WP isa (.block ((ds.zip as).flatMap fun (d, a) => a.mov d)) s fun s1 =>
      ((∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem) ∧ Keep ds s s1
  | [], _, _, _, _, s => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl⟩, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl⟩, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha.1 (hd d (List.mem_cons_self ..)) s) fun s1 ⟨⟨h1, hm1⟩, k1⟩ => ?_
    refine WP.mono (setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨⟨h2, hm2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1⟩, (k1.trans k2).mono fun r hr => by simpa using hr⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [Arg.val, pa]
        have hdb : d ∉ bases := fun h => by have := hd d (List.mem_cons_self ..); revert h this; cases d <;> decide
        rw [k1.gpr (by simp only [List.mem_singleton]; exact fun e => hdb (e ▸ hb.1))]
      | imm v => rfl
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · have := List.of_mem_zip hda
      rw [h2 da hda, hval da.2 (List.all_eq_true.mp ha.2 _ this.2)]

theorem argRegs6_nodup : argRegs6.Nodup := by decide


theorem argRegs6_sub : ∀ as : List Arg, ∀ r ∈ (argRegs6.zip as).map (·.1), r ∈ argRegs := by
  intro as r hr
  obtain ⟨⟨d, a⟩, hm, rfl⟩ := List.mem_map.mp hr
  have := (List.of_mem_zip hm).1
  simp only [argRegs6, argRegs, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases this with h | h | h | h | h | h <;> simp [h]

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.mono (setArgsGen_ok argRegs6 as argRegs6_nodup (fun _ h => h) ha s) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

theorem setArgs_nomem (as : List Arg) : ∀ i ∈ setArgs as, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a with
  | ptr p => exact lea_nomem d p i hi s
  | imm v => exact movi_nomem d v i hi s

/-! ## Calls -/

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem callP_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {as : List Arg} (ha : as.all Arg.ok = true)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → s1.mem = s.mem → Keep argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callP n c as) s fun s' => PostB D s s' wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, ArgsIn as s s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ :=
  glueCall_ok hv hsp hd hD (setArgs_ok as ha s) hpre hc hw

theorem callP_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep argRegs x x1 →
      (ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun _ _ => True :=
  glueCall_tr hv hct (block_nomem_tr (setArgs_nomem as)) (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩) hP

theorem callPRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep argRegs x x1 →
      (ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 :=
  glueCallRet_tr hv hr (block_nomem_tr (setArgs_nomem as)) (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩)
    hP

end VG.Proof.MlDsa.X86_64.Sign
