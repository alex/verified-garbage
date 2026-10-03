import VerifiedGarbage.Proof.X448.X86_64.Basic

/-!
# X448 on x86-64: carry chains, loads and stores

Proven once, by induction on the registers, for any number of words:

* `adcs_ok`, `add_chain_ok`: an `add` and `adc`s along registers, adding the
  values of stable sources, with the carry out;
* `sbbs_ok`, `sub_chain_ok`: the same for `sub` and `sbb`;
* `loads_ok`, `stores_ok`: words between registers and the working space;
* `fold_ok`, `unfold_ok`, `carryOut_ok`: `r15 · (1 + 2²²⁴)` added to (taken
  from) `r8–r14`, and the carry into `r15`;
* `mulStep_ok`: a multiply-accumulate step.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem toNat_ofBool (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

theorem add_carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ofBool]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sub_borrow (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat)).toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sbb_borrow (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, toNat_ofBool]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem Keeps.setFlagsReg {X : List Reg} {s₀ s : State} (h : Keeps X s₀ s) {r : Reg} (hr : r ∈ X)
    (v : BitVec 64) {w : Nat} (x : BitVec w) (c o : Bool) :
    Keeps X s₀ ((arithFlags s x c o).setReg r v) := by
  refine ⟨fun r' hr' => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => hr' (by rw [e]; exact hr)), RegUpd.gpr_arithFlags]
  exact h.1 r' hr'

theorem keeps_setFlagsReg (s : State) (r : Reg) (v : BitVec 64) {w : Nat} (x : BitVec w)
    (c o : Bool) : Keeps [r] s ((arithFlags s x c o).setReg r v) :=
  (Keeps.refl [r] s).setFlagsReg List.mem_cons_self v x c o

/-! ## Carry chains -/

/-- `adc`s along `rs`, adding the stable sources `ss` (values `vs`) and the
carry `c`. -/
theorem adcs_ok (X : List Reg) (s₀ : State) :
    ∀ (rs : List Reg) (ss : List Src) (vs : List (BitVec 64)) (s : State) (c : Bool),
      Keeps X s₀ s → (∀ r ∈ rs, r ∈ X) → rs.Nodup → rs.length = ss.length →
      List.Forall₂ (Stable X s₀) ss vs → s.cf = some c →
      WP isa (.block (chain .adc .adc rs ss)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
        rv s' rs + 2 ^ (64 * rs.length) * c'.toNat = rv s rs + wv vs + c.toNat ∧ Keeps rs s s'
  | [], ss, _, s, c, _, _, _, hl, hf, hc => by
    cases ss with
    | nil => cases hf; exact WP.block_nil ⟨c, hc, by simp [rv, wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | r :: rs, [], _, _, _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, src :: ss, vs, s, c, hk, hX, hnd, hl, hf, hc => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hrX : r ∈ X := hX r List.mem_cons_self
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hv' : readSrc s src = some v :=
      hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    let x := s.gpr r + v + (BitVec.ofBool c).setWidth 64
    let c1 := decide (2 ^ 64 ≤ (s.gpr r).toNat + v.toNat + c.toNat)
    let s1 := (arithFlags s x c1 (addOverflow (s.gpr r) v x)).setReg r x
    have he : exec (.alu .adc r src) s = some s1 := by
      simp only [exec, execAlu, hv', hc, Option.bind_some, Option.map_some]; rfl
    rw [chain, WP.block_cons_iff]
    refine ⟨s1, he, ?_⟩
    have hk1 : Keeps X s₀ s1 := hk.setFlagsReg hrX x x c1 _
    refine WP.mono (adcs_ok X s₀ rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 (by simpa using hl) hf
      (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
    have k1 : Keeps [r] s s1 := keeps_setFlagsReg s r x x c1 _
    refine ⟨c', hc', ?_, ?_⟩
    · have g1 : s'.gpr r = x := by
        rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
      have g2 : rv s1 rs = rv s rs :=
        rv_congr fun r' hr' => k1.1 r' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => hrs (e ▸ hr'))
      have ac : x.toNat + 2 ^ 64 * c1.toNat = (s.gpr r).toNat + v.toNat + c.toNat :=
        adc_carry (s.gpr r) v c
      rw [rv, g1, rv, List.length_cons, pow64_succ, wv, Nat.mul_assoc]
      rw [g2] at he'
      generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
      omega
    · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
        hk'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `add`, then `adc`s along `rs`, adding the stable sources `ss`. -/
theorem add_chain_ok (X : List Reg) (s : State) (r : Reg) (rs : List Reg) (src : Src) (ss : List Src)
    (v : BitVec 64) (vs : List (BitVec 64)) (hX : ∀ r' ∈ r :: rs, r' ∈ X) (hnd : (r :: rs).Nodup)
    (hl : rs.length = ss.length) (hv : Stable X s src v) (hf : List.Forall₂ (Stable X s) ss vs) :
    WP isa (.block (chain .add .adc (r :: rs) (src :: ss))) s fun s' => ∃ c' : Bool,
      s'.cf = some c' ∧ rv s' (r :: rs) + 2 ^ (64 * (r :: rs).length) * c'.toNat =
        rv s (r :: rs) + wv (v :: vs) ∧ Keeps (r :: rs) s s' := by
  have hrX : r ∈ X := hX r List.mem_cons_self
  have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
  let x := s.gpr r + v
  let c1 := decide (2 ^ 64 ≤ (s.gpr r).toNat + v.toNat)
  let s1 := (arithFlags s x c1 (addOverflow (s.gpr r) v x)).setReg r x
  have he : exec (.alu .add r src) s = some s1 := by
    simp only [exec, execAlu, hv.read, Option.bind_some]; rfl
  rw [chain, WP.block_cons_iff]
  refine ⟨s1, he, ?_⟩
  have hk1 : Keeps X s s1 := (Keeps.refl X s).setFlagsReg hrX x x c1 _
  refine WP.mono (adcs_ok X s rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
    (List.nodup_cons.mp hnd).2 hl hf
    (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
  have k1 : Keeps [r] s s1 := keeps_setFlagsReg s r x x c1 _
  refine ⟨c', hc', ?_, ?_⟩
  · have g1 : s'.gpr r = x := by
      rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    have g2 : rv s1 rs = rv s rs :=
      rv_congr fun r' hr' => k1.1 r' (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun e => hrs (e ▸ hr'))
    have ac : x.toNat + 2 ^ 64 * c1.toNat = (s.gpr r).toNat + v.toNat := add_carry (s.gpr r) v
    rw [rv, g1, rv, List.length_cons, pow64_succ, wv, Nat.mul_assoc]
    rw [g2] at he'
    generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
    omega
  · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
      hk'.2.2.2.trans k1.2.2.2⟩
    simp only [List.mem_cons, not_or] at hr'
    rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `sbb`s along `rs`, subtracting the stable sources `ss` (values `vs`) and
the borrow `c`. -/
theorem sbbs_ok (X : List Reg) (s₀ : State) :
    ∀ (rs : List Reg) (ss : List Src) (vs : List (BitVec 64)) (s : State) (c : Bool),
      Keeps X s₀ s → (∀ r ∈ rs, r ∈ X) → rs.Nodup → rs.length = ss.length →
      List.Forall₂ (Stable X s₀) ss vs → s.cf = some c →
      WP isa (.block (chain .sbb .sbb rs ss)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
        rv s' rs + wv vs + c.toNat = rv s rs + 2 ^ (64 * rs.length) * c'.toNat ∧ Keeps rs s s'
  | [], ss, _, s, c, _, _, _, hl, hf, hc => by
    cases ss with
    | nil => cases hf; exact WP.block_nil ⟨c, hc, by simp [rv, wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | r :: rs, [], _, _, _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, src :: ss, vs, s, c, hk, hX, hnd, hl, hf, hc => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hrX : r ∈ X := hX r List.mem_cons_self
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hv' : readSrc s src = some v :=
      hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    let x := s.gpr r - v - (BitVec.ofBool c).setWidth 64
    let c1 := decide ((s.gpr r).toNat < v.toNat + c.toNat)
    let s1 := (arithFlags s x c1 (subOverflow (s.gpr r) v x)).setReg r x
    have he : exec (.alu .sbb r src) s = some s1 := by
      simp only [exec, execAlu, hv', hc, Option.bind_some, Option.map_some]; rfl
    rw [chain, WP.block_cons_iff]
    refine ⟨s1, he, ?_⟩
    have hk1 : Keeps X s₀ s1 := hk.setFlagsReg hrX x x c1 _
    refine WP.mono (sbbs_ok X s₀ rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 (by simpa using hl) hf
      (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
    have k1 : Keeps [r] s s1 := keeps_setFlagsReg s r x x c1 _
    refine ⟨c', hc', ?_, ?_⟩
    · have g1 : s'.gpr r = x := by
        rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
      have g2 : rv s1 rs = rv s rs :=
        rv_congr fun r' hr' => k1.1 r' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => hrs (e ▸ hr'))
      have ac : x.toNat + v.toNat + c.toNat = (s.gpr r).toNat + 2 ^ 64 * c1.toNat :=
        sbb_borrow (s.gpr r) v c
      rw [rv, g1, rv, List.length_cons, pow64_succ, wv, Nat.mul_assoc]
      rw [g2] at he'
      generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
      omega
    · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
        hk'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `sub`, then `sbb`s along `rs`, subtracting the stable sources `ss`. -/
theorem sub_chain_ok (X : List Reg) (s : State) (r : Reg) (rs : List Reg) (src : Src) (ss : List Src)
    (v : BitVec 64) (vs : List (BitVec 64)) (hX : ∀ r' ∈ r :: rs, r' ∈ X) (hnd : (r :: rs).Nodup)
    (hl : rs.length = ss.length) (hv : Stable X s src v) (hf : List.Forall₂ (Stable X s) ss vs) :
    WP isa (.block (chain .sub .sbb (r :: rs) (src :: ss))) s fun s' => ∃ c' : Bool,
      s'.cf = some c' ∧ rv s' (r :: rs) + wv (v :: vs) =
        rv s (r :: rs) + 2 ^ (64 * (r :: rs).length) * c'.toNat ∧ Keeps (r :: rs) s s' := by
  have hrX : r ∈ X := hX r List.mem_cons_self
  have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
  let x := s.gpr r - v
  let c1 := decide ((s.gpr r).toNat < v.toNat)
  let s1 := (arithFlags s x c1 (subOverflow (s.gpr r) v x)).setReg r x
  have he : exec (.alu .sub r src) s = some s1 := by
    simp only [exec, execAlu, hv.read, Option.bind_some]; rfl
  rw [chain, WP.block_cons_iff]
  refine ⟨s1, he, ?_⟩
  have hk1 : Keeps X s s1 := (Keeps.refl X s).setFlagsReg hrX x x c1 _
  refine WP.mono (sbbs_ok X s rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
    (List.nodup_cons.mp hnd).2 hl hf
    (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
  have k1 : Keeps [r] s s1 := keeps_setFlagsReg s r x x c1 _
  refine ⟨c', hc', ?_, ?_⟩
  · have g1 : s'.gpr r = x := by
      rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    have g2 : rv s1 rs = rv s rs :=
      rv_congr fun r' hr' => k1.1 r' (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun e => hrs (e ▸ hr'))
    have ac : x.toNat + v.toNat = (s.gpr r).toNat + 2 ^ 64 * c1.toNat := sub_borrow (s.gpr r) v
    rw [rv, g1, rv, List.length_cons, pow64_succ, wv, Nat.mul_assoc]
    rw [g2] at he'
    generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
    omega
  · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
      hk'.2.2.2.trans k1.2.2.2⟩
    simp only [List.mem_cons, not_or] at hr'
    rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-! ## Loads and stores -/

/-- `loads o rs`: each register of `rs` holds its word of `[o]`. -/
theorem loads_ok {s : State} {base : Addr} (hs : Scr s base) :
    ∀ (o : Nat) (rs : List Reg), rs.Nodup → .rdi ∉ rs → o + 8 * rs.length ≤ 8192 →
      WP isa (.block (loads o rs)) s fun s' =>
        (∀ i < rs.length, ∀ d, s'.gpr (rs.getD i d) = word s.mem base (o + 8 * i)) ∧
        rv s' rs = mv s.mem base o rs.length ∧ Keeps rs s s'
  | _, [], _, _, _ => WP.block_nil ⟨fun _ h => by simp at h, rfl, Keeps.refl _ _⟩
  | o, r :: rs, hnd, hr, ho => by
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hrd : r ≠ .rdi := fun e => hr (e ▸ List.mem_cons_self)
    have hl : (r :: rs).length = rs.length + 1 := rfl
    rw [loads, WP.block_cons_iff]
    refine ⟨s.setReg r (word s.mem base o), by
      simp only [exec, readSrc_sc hs (d := o) (by omega), Option.map_some], ?_⟩
    have hs1 : Scr (s.setReg r (word s.mem base o)) base :=
      ⟨by rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrd)]; exact hs.rdi, hs.wr, hs.nowrap⟩
    refine WP.mono (loads_ok hs1 (o + 8) rs (List.nodup_cons.mp hnd).2
      (fun h => hr (List.mem_cons_of_mem _ h)) (by omega)) fun s' ⟨hw, hv, hk⟩ => ?_
    have g : s'.gpr r = word s.mem base o := by
      rw [hk.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    refine ⟨fun i hi d => ?_, ?_, ?_⟩
    · cases i with
      | zero => simpa using g
      | succ i =>
        rw [List.getD_cons_succ, hw i (by simpa using hi) d, RegUpd.mem_setReg,
          show o + 8 + 8 * i = o + 8 * (i + 1) by omega]
    · rw [rv, g, hv, List.length_cons, mv]; rfl
    · refine ⟨fun r' hr' => ?_, hk.2.1, hk.2.2.1, hk.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk.1 r' hr'.2, RegUpd.gpr_setReg_of_ne _ _ hr'.1]

/-- `stores o rs`: the words of `[o]` are the registers `rs`, and nothing
else changes. -/
theorem stores_ok {s : State} {base : Addr} (hs : Scr s base) :
    ∀ (o : Nat) (rs : List Reg), o + 8 * rs.length ≤ 8192 →
      WP isa (.block (stores o rs)) s fun s' =>
        mv s'.mem base o rs.length = rv s rs ∧ Outside base o (8 * rs.length) s.mem s'.mem ∧
        (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | _, [], _ => WP.block_nil ⟨rfl, Outside.refl _ _ _ _, fun _ => rfl, rfl, rfl⟩
  | o, r :: rs, ho => by
    rw [stores, WP.block_cons_iff]
    have hl : (r :: rs).length = rs.length + 1 := rfl
    let s1 : State := { s with mem := s.mem.writeW (off base o) (s.gpr r) }
    refine ⟨s1, by
      have hw := hs.write (d := o) (n := 8) (by omega)
      simp only [exec, ea_sc, hs.rdi, State.store64, hw, ite_true]; rfl, ?_⟩
    have hs1 : Scr s1 base := ⟨hs.rdi, hs.wr, hs.nowrap⟩
    refine WP.mono (stores_ok hs1 (o + 8) rs (by omega)) fun s' ⟨hv, ho', hg, hrd, hwr⟩ => ?_
    have o1 : Outside base o 8 s.mem s1.mem := writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, mv, hv, rv, ho'.word (by omega) (by omega)]
      simp only [s1, word_writeW_self]
      rw [rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (o1.mono (by omega) (by omega)).trans (ho'.mono (by omega) (by omega))

theorem stable_scs {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (Stable X s) (ds.map fun d => .mem (sc d)) (ds.map fun d => word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (stable_sc hs hX (h d List.mem_cons_self))
      (stable_scs hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-! ## Folding the top word -/

theorem len_W : 64 * W.length = 448 := rfl

theorem W_nodup : W.Nodup := by decide

theorem W_lit : [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14] = W := rfl

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

/-- `r15 = CF`. -/
theorem carryOut_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block carryOut) s fun s' => (s'.gpr .r15).toNat = c.toNat ∧ Keeps [.r15] s s' := by
  apply WP.of_runBlock
  simp only [carryOut, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, State.setReg32, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.cf_setReg, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem rotr32 (x : BitVec 64) (h : x.toNat < 2 ^ 32) :
    (x.rotateRight 32).toNat = x.toNat * 2 ^ 32 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt h, Nat.zero_or, Nat.mod_eq_of_lt (by omega)]

/-- `rax = r15 << 32`, for `r15 < 2³²`. -/
theorem shl32_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block [.mov .rax (.reg .r15), .shift .ror .rax 32]) s fun s' =>
      (s'.gpr .rax).toNat = (s.gpr .r15).toNat * 2 ^ 32 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  have h32 : (1 ≤ 32 ∧ 32 ≤ 63) = True := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, h32, ite_true,
    Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨rotr32 _ h, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

theorem Keeps.rv_eq {X rs : List Reg} {s s' : State} (h : Keeps X s s') (hd : ∀ r ∈ rs, r ∉ X) :
    rv s' rs = rv s rs := rv_congr fun r hr => h.1 r (hd r hr)

/-- The sources of `fold` and `unfold`: `r15` and `rax = r15 << 32` at words 0
and 3. -/
theorem fold_srcs (s : State) :
    List.Forall₂ (Stable W s) [.imm 0, .imm 0, .reg .rax, .imm 0, .imm 0, .imm 0]
      [0, 0, s.gpr .rax, 0, 0, 0] :=
  .cons (stable_imm0 _ _) <| .cons (stable_imm0 _ _) <| .cons (stable_reg s (by decide)) <|
    .cons (stable_imm0 _ _) <| .cons (stable_imm0 _ _) <| .cons (stable_imm0 _ _) .nil

/-- `fold`: `r8–r14 + r15 (1 + 2²²⁴)`, with the carry out. -/
theorem fold_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block fold) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      rv s' W + 2 ^ 448 * c.toNat = rv s W + (s.gpr .r15).toNat * (1 + 2 ^ 224) ∧
      Keeps (.rax :: W) s s' := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (shl32_ok s h) fun s1 ⟨h1, k1⟩ => ?_
  have r15 : s1.gpr .r15 = s.gpr .r15 := k1.1 _ (by decide)
  refine WP.mono (add_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] (.reg .r15) _
    (s1.gpr .r15) _ (fun _ h => h) W_nodup rfl (stable_reg s1 (by decide)) (fold_srcs s1))
    fun s' ⟨c, hc, he, hk⟩ => ⟨c, hc, ?_, (k1.mono (by decide)).trans (hk.mono (by decide))⟩
  have e1 : rv s1 W = rv s W := k1.rv_eq (by decide)
  rw [W_lit, len_W, e1] at he
  simp only [wv, r15, toNat_zero64] at he
  omega

/-- `unfold`: `r8–r14 - r15 (1 + 2²²⁴)`, with the borrow out. -/
theorem unfold_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block unfold) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      rv s' W + (s.gpr .r15).toNat * (1 + 2 ^ 224) = rv s W + 2 ^ 448 * c.toNat ∧
      Keeps (.rax :: W) s s' := by
  rw [unfold, WP.block_append_iff]
  refine WP.mono (shl32_ok s h) fun s1 ⟨h1, k1⟩ => ?_
  have r15 : s1.gpr .r15 = s.gpr .r15 := k1.1 _ (by decide)
  refine WP.mono (sub_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] (.reg .r15) _
    (s1.gpr .r15) _ (fun _ h => h) W_nodup rfl (stable_reg s1 (by decide)) (fold_srcs s1))
    fun s' ⟨c, hc, he, hk⟩ => ⟨c, hc, ?_, (k1.mono (by decide)).trans (hk.mono (by decide))⟩
  have e1 : rv s1 W = rv s W := k1.rv_eq (by decide)
  rw [W_lit, len_W, e1] at he
  simp only [wv, r15, toNat_zero64] at he
  omega

open VG.Spec.X448 (P) in
/-- `fold2`: `r8–r14 + 2⁴⁴⁸ r15` modulo `p`, in seven words. -/
theorem fold2_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block fold2) s fun s' =>
      rv s' W % P = (rv s W + 2 ^ 448 * (s.gpr .r15).toNat) % P ∧
      Keeps (.rax :: .r15 :: W) s s' := by
  rw [fold2, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fold_ok s h) fun s1 ⟨c1, hc1, e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s1 hc1) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.mono (fold_ok s2 (by rw [e2]; cases c1 <;> decide)) fun s3 ⟨c3, _, e3, k3⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  have w2 : rv s2 W = rv s1 W := k2.rv_eq (by decide)
  rw [w2, e2] at e3
  have l0 := rv_lt s W; have l1 := rv_lt s1 W; have l3 := rv_lt s3 W
  rw [len_W] at l0 l1 l3
  have hc := Bool.toNat_le c1
  have hc3 : c3.toNat = 0 := by
    rcases Nat.lt_or_ge c3.toNat 1 with h3 | h3
    · omega
    · rcases Nat.lt_or_ge c1.toNat 1 with h1 | h1 <;> omega
  rw [fold448 (rv s W) (s.gpr .r15).toNat]
  have h1 : rv s W + (2 ^ 224 + 1) * (s.gpr .r15).toNat = rv s1 W + 2 ^ 448 * c1.toNat := by
    omega
  rw [h1, fold448 (rv s1 W) c1.toNat]
  exact congrArg (· % P) (by omega)

/-- The arithmetic of a multiply-accumulate step: the product's halves, the
carry word `c` added to the low half, and the sum added to `t`, each carry
going into the high half, which never overflows. -/
theorem step_arith (a v c t : BitVec 64) :
    let p := a.toNat * v.toNat
    let lo : BitVec 64 := BitVec.ofNat 64 p
    let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
    let r := lo + c
    let d := hi + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64
    (t + r).toNat + 2 ^ 64 *
        (d + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ t.toNat + r.toNat))).setWidth 64).toNat =
      t.toNat + c.toNat + a.toNat * v.toNat := by
  intro p lo hi r d
  have ha := a.isLt; have hv := v.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hlo : lo.toNat = p % 2 ^ 64 := BitVec.toNat_ofNat _ _
  have hhi : hi.toNat = p / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : p / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r, d, BitVec.toNat_add, toNat_ofBool, hz, Nat.add_zero, hlo, hhi] at *
  by_cases h1 : 2 ^ 64 ≤ p % 2 ^ 64 + c.toNat <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64;
    by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A multiply-accumulate step: `t:c = t + c + ai · v`, where `ld` loads `v`
into `rax`. -/
theorem mulStep_ok (s : State) {t c ai : Reg} {ld : Instr} {v : BitVec 64}
    (hld : exec ld s = some (s.setReg .rax v)) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) :
    WP isa (.block (mulStep t c ai ld)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * v.toNat ∧
      Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, runBlock_cons, hld, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht',
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := step_arith (s.gpr ai) v (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- `ld` loads `v` into `rax` in every state that agrees with `s` but on the
registers `X`. -/
def LdStable (X : List Reg) (s : State) (ld : Instr) (v : BitVec 64) : Prop :=
  ∀ t, (∀ r, r ∉ X → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
    exec ld t = some (t.setReg .rax v)

theorem ldStable_sc {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) :
    LdStable X s (.mov .rax (.mem (sc d))) (word s.mem base d) := fun t hg hm _ hwr => by
  have ht : Scr t base := ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩
  simp only [exec, readSrc_sc ht hd, hm, Option.map_some]

theorem ldStable_sc32 {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) :
    LdStable X s (.mov32 .rax (.mem (sc d))) ((s.mem.readW (off base d) 32).setWidth 64) :=
  fun t hg hm _ hwr => by
    have ht : Scr t base := ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩
    simp only [exec, readSrc32, State.load32, ea_sc, ht.rdi, ht.read (d := d) (n := 4) (by omega),
      ite_true, hm, Option.map_some, State.setReg32]

/-- Multiply-accumulate steps along `ts`: `ts + 2^(64n) rbp = ts + rbp + rcx · vs`. -/
theorem mulSteps_ok (X : List Reg) (s₀ : State) :
    ∀ (ts : List Reg) (lds : List Instr) (vs : List (BitVec 64)) (s : State),
      Keeps X s₀ s → (∀ r ∈ .rax :: .rdx :: .rbp :: ts, r ∈ X) → .rcx ∉ X →
      (.rax :: .rdx :: .rbp :: .rcx :: ts).Nodup → ts.length = lds.length →
      List.Forall₂ (LdStable X s₀) lds vs →
      WP isa (.block (mulSteps ts lds)) s fun s' =>
        rv s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
          rv s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wv vs ∧
        Keeps (.rax :: .rdx :: .rbp :: ts) s s'
  | [], lds, _, s, _, _, _, _, hl, hf => by
    cases lds with
    | nil => cases hf; exact WP.block_nil ⟨by simp [rv, wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | t :: ts, [], _, _, _, _, _, _, hl, _ => by simp at hl
  | t :: ts, ld :: lds, vs, s, hk, hX, hcX, hnd, hl, hf => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hat : t ≠ .rax := fun e => by subst e; simp at hnd
    have hdt : t ≠ .rdx := fun e => by subst e; simp at hnd
    have hbt : t ≠ .rbp := fun e => by subst e; simp at hnd
    have hct : t ≠ .rcx := fun e => by subst e; simp at hnd
    have htt : t ∉ ts := fun e => by simp [e] at hnd
    rw [mulSteps, WP.block_append_iff]
    have hld := hv s hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
    refine WP.mono (mulStep_ok s hld hat hdt (by decide) (by decide)
      (by decide) hbt) fun s1 ⟨e1, k1⟩ => ?_
    have hXs : ∀ r ∈ [t, .rbp, .rax, .rdx], r ∈ X := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hX _ (by simp)
    have hk1 : Keeps X s₀ s1 := hk.trans (k1.mono hXs)
    refine WP.mono (mulSteps_ok X s₀ ts lds vs s1 hk1
      (fun r hr => hX r (by simp only [List.mem_cons] at hr ⊢; grind)) hcX
      (by simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢; grind) (by simpa using hl) hf)
      fun s' ⟨e', k'⟩ => ⟨?_, ?_⟩
    · have c1 : s1.gpr .rcx = s.gpr .rcx := k1.1 _ (by simp [Ne.symm hct])
      have g1 : s'.gpr t = s1.gpr t := k'.1 _ (by simp [hat, hdt, hbt, htt])
      have r1 : rv s1 ts = rv s ts := k1.rv_eq fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => htt (e ▸ hr), fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
          simp at hnd <;> simp_all
      rw [c1, r1] at e'
      rw [rv, rv, g1, List.length_cons, pow64_succ, wv, Nat.mul_assoc]
      generalize 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat = Y at e' ⊢
      rw [Nat.mul_add, Nat.mul_left_comm]
      generalize (s.gpr .rcx).toNat * wv vs = Z at e' ⊢
      omega
    · refine ⟨fun r hr => ?_, k'.2.1.trans k1.2.1, k'.2.2.1.trans k1.2.2.1, k'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr
      rw [k'.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2]),
        k1.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])]

end VG.Proof.X448.X86_64
