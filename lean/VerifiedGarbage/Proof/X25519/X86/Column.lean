import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# X25519 on x86 (32-bit): columns

Untrusted: everything here is checked by Lean. Each term of a column adds its
value to the 96-bit accumulator `ebx + 2³² ecx + 2⁶⁴ ebp` (`acc`), as long
as the sum fits; the end of a column stores the accumulator's low word and
shifts it down. `cols_ok` sums `n` columns into `n` words and a carry, when
no column reads a word an earlier one stored.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

/-- The accumulator `ebx + 2³² ecx + 2⁶⁴ ebp`. -/
abbrev acc (s : State) : Nat := v s .ebx + 2 ^ 32 * v s .ecx + 2 ^ 64 * v s .ebp

/-- The value of a term, for the working space at `x`. -/
def tval (m : Mem) (x : BitVec 32) : Term → Nat
  | .mulM a b => wv m x a * wv m x b
  | .mulI a c => wv m x a * c.toNat
  | .addM a => wv m x a
  | .addI c => c.toNat
  | .addNot a => 2 ^ 32 - 1 - wv m x a

/-- The offsets of the words a term reads. -/
def treads : Term → List Nat
  | .mulM a b => [a, b]
  | .mulI a _ => [a]
  | .addM a => [a]
  | .addI _ => []
  | .addNot a => [a]

/-- The value of a column. -/
def colv (m : Mem) (x : BitVec 32) (ts : List Term) : Nat := (ts.map (tval m x)).sum

theorem tval_congr {m m' : Mem} {x : BitVec 32} {t : Term} (h : ∀ d ∈ treads t, wd m' x d = wd m x d) :
    tval m' x t = tval m x t := by
  cases t with
  | mulM a b => simp only [tval, wv, h a (by simp [treads]), h b (by simp [treads])]
  | mulI a c => simp only [tval, wv, h a (by simp [treads])]
  | addM a => simp only [tval, wv, h a (by simp [treads])]
  | addI c => rfl
  | addNot a => simp only [tval, wv, h a (by simp [treads])]

theorem colv_congr {m m' : Mem} {x : BitVec 32} {ts : List Term}
    (h : ∀ t ∈ ts, ∀ d ∈ treads t, wd m' x d = wd m x d) : colv m' x ts = colv m x ts := by
  simp only [colv]
  congr 1
  exact List.map_congr_left fun t ht => tval_congr (h t ht)

/-! ## Arithmetic -/

theorem carry_toNat {n : Nat} (h : n < 2 ^ 33) : (decide (2 ^ 32 ≤ n)).toNat = n / 2 ^ 32 := by
  by_cases h' : 2 ^ 32 ≤ n
  · simp only [h', decide_true, Bool.toNat_true]; omega_using [h, h']
  · simp only [h', decide_false, Bool.toNat_false]; omega_using [h']

theorem add3_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  cases c <;> rfl

/-- The accumulator after adding `x0 + 2³² x1` word by word, with carries. -/
theorem acc3 {a b c x0 x1 : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h0 : x0 < 2 ^ 32) (h1 : x1 < 2 ^ 32)
    (h : a + 2 ^ 32 * b + 2 ^ 64 * c + (x0 + 2 ^ 32 * x1) < 2 ^ 96) :
    (a + x0) % 2 ^ 32 + 2 ^ 32 * ((b + x1 + (a + x0) / 2 ^ 32) % 2 ^ 32) +
      2 ^ 64 * ((c + (b + x1 + (a + x0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) =
      a + 2 ^ 32 * b + 2 ^ 64 * c + (x0 + 2 ^ 32 * x1) := by
  generalize e₁ : (a + x0) / 2 ^ 32 = c₁
  have k₁ := Nat.div_add_mod (a + x0) (2 ^ 32)
  have l₁ : (a + x0) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [e₁] at k₁
  have hc₁ : c₁ ≤ 1 := by omega_using [k₁, ha, h0]
  generalize e₂ : (b + x1 + c₁) / 2 ^ 32 = c₂
  have k₂ := Nat.div_add_mod (b + x1 + c₁) (2 ^ 32)
  have l₂ : (b + x1 + c₁) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [e₂] at k₂
  have hc₂ : c₂ ≤ 1 := by omega_using [k₂, hb, h1, hc₁]
  have k₃ := Nat.div_add_mod (c + c₂) (2 ^ 32)
  have l₃ : (c + c₂) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  generalize (c + c₂) % 2 ^ 32 = r₃ at *
  generalize (c + c₂) / 2 ^ 32 = q₃ at *
  generalize (a + x0) % 2 ^ 32 = r₁ at *
  generalize (b + x1 + c₁) % 2 ^ 32 = r₂ at *
  omega_using [k₁, k₂, k₃, h, l₁, l₂, l₃]

/-! ## The steps of a column -/

/-- Reads the registers, memory and regions of a state after writes, for
literal registers. -/
macro "regupd" : tactic => `(tactic| simp (config := {decide := true}) only [acc, v,
  RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
  RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags,
  RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false])


theorem toNat_zero32 : (0 : BitVec 32).toNat = 0 := rfl

theorem readSrc_imm (s : State) (w : BitVec 32) : readSrc s (.imm w) = some w := rfl
theorem readSrc_reg (s : State) (r : Reg) : readSrc s (.reg r) = some (s.gpr r) := rfl


/-- What a column's code leaves: `esi`, `edi`, `esp` and the regions. -/
theorem accAdd_ok {s : State} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x) :
    WP isa (.block (accAdd src)) s fun s' =>
      (acc s + x.toNat < 2 ^ 96 → acc s' = acc s + x.toNat) ∧ Keep s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [accAdd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hx, readSrc_imm,
    Option.bind_some, Option.map_some, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun hlt => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> regupd
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt; have hc := (s.gpr .ebp).isLt
  have hx' := x.isLt
  simp only [add3_toNat, toNat_zero32, Nat.add_zero]
  simp only [BitVec.toNat_add]
  rw [carry_toNat (by omega_using [ha, hx']), carry_toNat (by omega_using [hb, ha, hx'])]
  have := acc3 (c := (s.gpr .ebp).toNat) (x1 := 0) ha hb hx' (by decide) (by omega_using [hlt])
  simp only [Nat.add_zero, Nat.mul_zero] at this
  exact this

theorem toNat_mul_lo (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat * b.toNat)).toNat +
      2 ^ 32 * (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = a.toNat * b.toNat := by
  have := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 32) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])]
  omega_using []

theorem accMul_ok {s : State} {src : Src} {y : BitVec 32} (hy : readSrc s src = some y) :
    WP isa (.block (accMul src)) s fun s' =>
      (acc s + v s .eax * y.toNat < 2 ^ 96 → acc s' = acc s + v s .eax * y.toNat) ∧ Keep s s' ∧
        s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [accMul, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul, hy,
    readSrc_imm, readSrc_reg, Option.bind_some, Option.map_some, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨fun hlt => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> regupd
  simp only [acc, v] at hlt
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt
  have e := toNat_mul_lo (s.gpr .eax) y
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat)) = lo at *
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat / 2 ^ 32)) = hi at *
  have hl := lo.isLt; have hh := hi.isLt
  simp only [add3_toNat, toNat_zero32, Nat.add_zero]
  simp only [BitVec.toNat_add]
  rw [carry_toNat (by omega_using [ha, hl]), carry_toNat (by omega_using [hb, hh, ha, hl])]
  have := acc3 (c := (s.gpr .ebp).toNat) ha hb hl hh (by omega_using [hlt, e])
  rw [← e]
  exact this

open VG.X86.Wp in
theorem readSrc_sc {x : BitVec 32} {s : State} (hc : Ctx x s) {d : Nat} (hd : d + 4 ≤ 4096) :
    readSrc s (.mem (sc d)) = some (wd s.mem x d) :=
  readSrc_mem hc.edi (hc.inRW hd (by decide))

theorem updKeep {s s' : State} {d : Reg} {w : BitVec 32} (h : Wp.Upd s s' d w)
    (hd : d ≠ .esi ∧ d ≠ .edi ∧ d ≠ .esp := by decide) : Keep s s' :=
  ⟨h.other _ hd.1.symm, h.other _ hd.2.1.symm, h.other _ hd.2.2.symm, h.rd, h.wr⟩

theorem updAcc {s s' : State} {w : BitVec 32} (h : Wp.Upd s s' .eax w) : acc s' = acc s := by
  simp only [acc, v, h.other .ebx (by decide), h.other .ecx (by decide), h.other .ebp (by decide)]

theorem xor_ones_toNat (w : BitVec 32) : (w ^^^ 0xffffffff).toNat = 2 ^ 32 - 1 - w.toNat := by
  rw [show (0xffffffff : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes, BitVec.toNat_not]

open VG.X86.Wp in
theorem term_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (t : Term) (hr : ∀ d ∈ treads t, d + 4 ≤ 4096) :
    WP isa (.block (Term.code t)) s fun s' =>
      (acc s + tval s.mem x t < 2 ^ 96 → acc s' = acc s + tval s.mem x t) ∧ Keep s s' ∧ s'.mem = s.mem := by
  cases t with
  | mulM a b =>
    have ha := hr a (by simp [treads]); have hb := hr b (by simp [treads])
    refine wp_ldm hc.edi (hc.inRW ha (by decide)) fun s₁ u₁ => ?_
    have c₁ := (updKeep u₁).ctx hc
    refine WP.mono (accMul_ok (readSrc_sc c₁ hb)) fun s' ⟨h, k, m⟩ => ⟨fun hlt => ?_, (updKeep u₁).trans k,
      m.trans u₁.mem⟩
    rw [h (by rw [updAcc u₁, v, u₁.gpr, u₁.mem]; exact hlt), updAcc u₁, v, u₁.gpr, u₁.mem]; rfl
  | mulI a c =>
    have ha := hr a (by simp [treads])
    refine wp_ldm hc.edi (hc.inRW ha (by decide)) fun s₁ u₁ => ?_
    refine WP.mono (accMul_ok (readSrc_imm s₁ c)) fun s' ⟨h, k, m⟩ => ⟨fun hlt => ?_, (updKeep u₁).trans k,
      m.trans u₁.mem⟩
    rw [h (by rw [updAcc u₁, v, u₁.gpr]; exact hlt), updAcc u₁, v, u₁.gpr]; rfl
  | addM a =>
    have ha := hr a (by simp [treads])
    exact accAdd_ok (readSrc_sc hc ha)
  | addI c => exact accAdd_ok (readSrc_imm s c)
  | addNot a =>
    have ha := hr a (by simp [treads])
    refine wp_ldm hc.edi (hc.inRW ha (by decide)) fun s₁ u₁ => ?_
    refine Wp.cons (s' := (arithFlags s₁ (s₁.gpr .eax ^^^ 0xffffffff) false false).setReg .eax
      (s₁.gpr .eax ^^^ 0xffffffff)) rfl ?_
    have u₂ := Upd.flags s₁ .eax (s₁.gpr .eax ^^^ 0xffffffff) false false (s₁.gpr .eax ^^^ 0xffffffff)
    refine WP.mono (accAdd_ok (readSrc_reg _ .eax)) fun s' ⟨h, k, m⟩ =>
      ⟨fun hlt => ?_, (updKeep u₁).trans ((updKeep u₂).trans k), m.trans (u₂.mem.trans u₁.mem)⟩
    have e : (((arithFlags s₁ (s₁.gpr .eax ^^^ 0xffffffff) false false).setReg .eax
        (s₁.gpr .eax ^^^ 0xffffffff)).gpr .eax).toNat = tval s.mem x (.addNot a) := by
      rw [u₂.gpr, u₁.gpr, xor_ones_toNat]; rfl
    rw [e] at h
    rw [h (by rw [(updAcc u₂), (updAcc u₁)]; exact hlt), (updAcc u₂), (updAcc u₁)]

theorem terms_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (ts : List Term)
    (hr : ∀ t ∈ ts, ∀ d ∈ treads t, d + 4 ≤ 4096) :
    WP isa (.block (ts.flatMap Term.code)) s fun s' =>
      (acc s + colv s.mem x ts < 2 ^ 96 → acc s' = acc s + colv s.mem x ts) ∧ Keep s s' ∧
        s'.mem = s.mem := by
  induction ts generalizing s with
  | nil => exact WP.block_nil ⟨fun _ => by simp [colv], Keep.refl _, rfl⟩
  | cons t ts ih =>
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (term_ok hc t (hr t List.mem_cons_self)) fun s₁ ⟨h₁, k₁, m₁⟩ => ?_)
    refine WP.mono (ih (k₁.ctx hc) fun t' ht' => hr t' (List.mem_cons_of_mem _ ht'))
      fun s₂ ⟨h₂, k₂, m₂⟩ => ⟨fun hlt => ?_, k₁.trans k₂, m₂.trans m₁⟩
    simp only [colv, List.map_cons, List.sum_cons] at hlt ⊢
    rw [m₁] at h₂
    simp only [colv] at h₂
    rw [h₂ (by rw [h₁ (by omega_using [hlt])]; omega_using [hlt]), h₁ (by omega_using [hlt])]
    omega_using []

open VG.X86.Wp in
theorem colEnd_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : o + 4 ≤ 4096) :
    WP isa (.block (colEnd o)) s fun s' =>
      Keep s s' ∧ s'.mem = s.mem.writeW (addr x o) (s.gpr .ebx) ∧ acc s' = acc s / 2 ^ 32 := by
  refine wp_stm hc.edi (hc.inW ho (by decide)) fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have k₁ : Keep s s₁ := ⟨by rw [u₁.gpr], by rw [u₁.gpr], by rw [u₁.gpr], u₁.rd, u₁.wr⟩
  refine ⟨k₁.trans ((updKeep u₂).trans ((updKeep u₃).trans (updKeep u₄))), by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [acc, v, u₄.gpr, u₄.other .ebx (by decide), u₄.other .ecx (by decide), u₃.gpr,
    u₃.other .ebx (by decide), u₂.gpr, u₂.other .ebp (by decide), u₁.gpr, toNat_zero32, Nat.mul_zero,
    Nat.add_zero]
  have := (s.gpr .ebx).isLt
  omega_using [this]

theorem column_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (ts : List Term) {o : Nat}
    (hr : ∀ t ∈ ts, ∀ d ∈ treads t, d + 4 ≤ 4096) (ho : o + 4 ≤ 4096)
    (hlt : acc s + colv s.mem x ts < 2 ^ 96) :
    WP isa (.block (column ts o)) s fun s' => Keep s s' ∧ Frame [sub x o 4] s.mem s'.mem ∧
      wv s'.mem x o = (acc s + colv s.mem x ts) % 2 ^ 32 ∧
      acc s' = (acc s + colv s.mem x ts) / 2 ^ 32 := by
  refine WP.block_append (WP.mono (terms_ok hc ts hr) fun s₁ ⟨h₁, k₁, m₁⟩ => ?_)
  refine WP.mono (colEnd_ok (k₁.ctx hc) ho) fun s₂ ⟨k₂, m₂, h₂⟩ =>
    ⟨k₁.trans k₂, ?_, ?_, by rw [h₂, h₁ hlt]⟩
  · rw [m₂, m₁]
    exact frame_write1 (Frame.refl _ _) hc.fit ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [m₂, wv, wd_write_self, ← h₁ hlt]
    have := (s₁.gpr .ecx).isLt; have := (s₁.gpr .ebp).isLt
    simp only [acc, v]
    omega_using []

theorem cols_zero (o : Nat) (ts : Nat → List Term) : cols o 0 ts = [] := rfl

theorem cols_succ (o n : Nat) (ts : Nat → List Term) :
    cols o (n + 1) ts = cols o n ts ++ column (ts n) (o + 4 * n) := by
  simp only [cols, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- `P r + P 2³² q = P x` for the remainder `r` and quotient `q` of `x` by `2³²`. -/
theorem digit_step (P x : Nat) : P * (x % 2 ^ 32) + P * 2 ^ 32 * (x / 2 ^ 32) = P * x := by
  rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]

/-- `n` columns at `[x + o]`: their words and the carry are the sum of the
columns' values (with the accumulator's value on entry), as long as each
column reads no word an earlier one stored. -/
theorem cols_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ts : Nat → List Term) :
    ∀ n, o + 4 * n ≤ 4096 →
    (∀ k < n, ∀ t ∈ ts k, ∀ d ∈ treads t, d + 4 ≤ 4096 ∧ (d + 4 ≤ o ∨ o + 4 * k ≤ d)) →
    (∀ k < n, colv s.mem x (ts k) < 2 ^ 68) → acc s < 2 ^ 40 →
    WP isa (.block (cols o n ts)) s fun s' => Keep s s' ∧ Frame [sub x o (4 * n)] s.mem s'.mem ∧
      num (fun k => wv s'.mem x (o + 4 * k)) n + (2 ^ 32) ^ n * acc s' =
        acc s + num (fun k => colv s.mem x (ts k)) n ∧ acc s' < 2 ^ 40
  | 0, _, _, _, ha => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, by simp [num], ha⟩
  | n + 1, ho, hr, hb, ha => by
    rw [cols_succ]
    refine WP.block_append (WP.mono (cols_ok hc ts n (by omega_using [ho])
      (fun k hk => hr k (by omega_using [hk])) (fun k hk => hb k (by omega_using [hk])) ha)
      fun s₁ ⟨k₁, f₁, e₁, a₁⟩ => ?_)
    have hfit := hc.fit
    have hV : colv s₁.mem x (ts n) = colv s.mem x (ts n) := colv_congr fun t ht d hd =>
      wd_frame1 f₁ hfit (by omega_using [ho]) (hr n (by omega_using []) t ht d hd).1
        (hr n (by omega_using []) t ht d hd).2
    have hb' := hb n (by omega_using [])
    refine WP.mono (column_ok (k₁.ctx hc) (ts n) (fun t ht d hd => (hr n (by omega_using []) t ht d hd).1)
      (by omega_using [ho]) (by rw [hV]; omega_using [a₁, hb'])) fun s₂ ⟨k₂, f₂, w₂, a₂⟩ =>
      ⟨k₁.trans k₂, ?_, ?_, ?_⟩
    · exact (frameWiden f₁ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho])).trans
        (frameWiden f₂ hfit (by omega_using []) (by omega_using []) (by omega_using [ho]))
    · have hw : num (fun k => wv s₂.mem x (o + 4 * k)) n = num (fun k => wv s₁.mem x (o + 4 * k)) n :=
        num_congr fun k hk => by
          show (wd s₂.mem x (o + 4 * k)).toNat = (wd s₁.mem x (o + 4 * k)).toNat
          rw [wd_frame1 f₂ hfit (by omega_using [ho]) (by omega_using [ho, hk]) (by omega_using [hk])]
      rw [num_succ, num_succ, hw, w₂, a₂, hV, Nat.add_assoc, Nat.pow_succ (2 ^ 32) n,
        digit_step, Nat.mul_add, ← Nat.add_assoc, e₁, Nat.add_assoc]
    · rw [a₂, hV]; omega_using [a₁, hb']

end VG.Proof.X25519.X86
