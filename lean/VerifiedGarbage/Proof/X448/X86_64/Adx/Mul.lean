import VerifiedGarbage.Impl.X448.X86_64.Adx
import VerifiedGarbage.Proof.X448.X86_64.Env

/-!
# X448 on x86-64: multiplication with BMI2 and ADX

A multiply-add with both carry chains (`madd_ok`), a chain of them along a
row (`madds_ok`, by induction on the registers), a row (`rowX_ok`, for any
row of the rotating window), the rows (`rowsX_ok`, by induction on them), and
the multiplication `mulX o a b`, which ends with `reduce` (`reduce_ok`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem of_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).of = s.of := rfl
theorem of_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl

/-- `mulx hi, lo, [m]` runs as `setReg lo` then `setReg hi`. -/
theorem execMulx_mem {s : State} {hi lo : Reg} {m : MemOp} {v : BitVec 64}
    (hv : readSrc s (.mem m) = some v) :
    execMulx hi lo (.mem m) s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
  simp only [execMulx, hv, Option.map_some]

/-- `xor ebp, ebp`. -/
theorem clear_ok (s : State) :
    WP isa (.block [clear]) s fun s' =>
      s'.gpr .rbp = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rbp] s s' := by
  apply WP.of_runBlock
  simp only [clear, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self, BitVec.xor_self,
    RegUpd.cf_setReg, of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial),
    (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mulx hi, lo, [m]`: `lo + 2⁶⁴ hi = rdx · v`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {m : MemOp} {v : BitVec 64}
    (hv : readSrc s (.mem m) = some v) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo (.mem m)]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execMulx_mem hv,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), RegUpd.cf_setReg, of_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨mul_halves _ _, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial),
    (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adox x, r`: `x + r + OF`, the carry out in OF, CF unchanged. -/
theorem adox_ok (s : State) {x r : Reg} {o : Bool} (ho : s.of = some o) :
    WP isa (.block [.adox x (.reg r)]) s fun s' => ∃ o' : Bool, s'.of = some o' ∧ s'.cf = s.cf ∧
      (s'.gpr x).toNat + 2 ^ 64 * o'.toNat = (s.gpr x).toNat + (s.gpr r).toNat + o.toNat ∧
      Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, readSrc, ho,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, of_setReg, of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adcx x, r`: `x + r + CF`, the carry out in CF, OF unchanged. -/
theorem adcx_ok (s : State) {x r : Reg} {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.adcx x (.reg r)]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧ s'.of = s.of ∧
      (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + (s.gpr r).toNat + c.toNat ∧
      Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdcx, readSrc, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, of_setReg, of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `madd x y [m]`: `x + 2⁶⁴ y + o + 2⁶⁴ c + rdx · v`, the carries out in OF and
CF. -/
theorem madd_ok (s : State) {x y : Reg} {m : MemOp} {v : BitVec 64}
    (hv : readSrc s (.mem m) = some v) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hxy : x ≠ y) (hxa : x ≠ .rax) (hxc : x ≠ .rcx) (hya : y ≠ .rax) (hyc : y ≠ .rcx) :
    WP isa (.block (madd x y (.mem m))) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧
      s'.of = some o' ∧
      (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat + 2 ^ 128 * c'.toNat =
        (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat + o.toNat + 2 ^ 64 * c.toNat +
          (s.gpr .rdx).toNat * v.toNat ∧
      Keeps [x, y, .rax, .rcx] s s' := by
  rw [madd, show ([.mulx .rcx .rax (.mem m), .adox x (.reg .rax), .adcx y (.reg .rcx)] :
    List Instr) = [.mulx .rcx .rax (.mem m)] ++ ([.adox x (.reg .rax)] ++ [.adcx y (.reg .rcx)])
    from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hv (by decide)) fun s1 ⟨e1, c1, o1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s1 (o1.trans ho)) fun s2 ⟨o2, ho2, c2, e2, k2⟩ => ?_
  refine WP.mono (adcx_ok s2 (c2.trans (c1.trans hc))) fun s3 ⟨c3, hc3, o3, e3, k3⟩ => ?_
  refine ⟨c3, o2, hc3, o3.trans ho2, ?_, ?_⟩
  · have x1 : s1.gpr x = s.gpr x := k1.1 x (by simp [hxc, hxa])
    have y2 : s2.gpr y = s.gpr y := by
      rw [k2.1 y (by simp [Ne.symm hxy]), k1.1 y (by simp [hyc, hya])]
    have a2 : s2.gpr .rcx = s1.gpr .rcx := k2.1 _ (by simp [Ne.symm hxc])
    have x3 : s3.gpr x = s2.gpr x := k3.1 x (by simp [hxy])
    have d1 : s1.gpr .rdx = s.gpr .rdx := k1.1 _ (by decide)
    rw [x1] at e2; rw [y2, a2] at e3; rw [x3]
    omega
  · exact ((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))

theorem madds_arith {B Q x1 y1 x y o c o1 c1 Y' R d V WV o' c' : Nat}
    (e1 : x1 + B * y1 + B * o1 + B * B * c1 = x + B * y + o + B * c + d * V)
    (e' : Y' + Q * o' + B * Q * c' = y1 + B * R + o1 + B * c1 + d * WV) :
    x1 + B * Y' + B * Q * o' + B * (B * Q) * c' =
      x + B * (y + B * R) + o + B * c + d * (V + B * WV) :=
  calc x1 + B * Y' + B * Q * o' + B * (B * Q) * c'
      _ = x1 + B * (Y' + Q * o' + B * Q * c') := by ring
      _ = (x1 + B * y1 + B * o1 + B * B * c1) + B * B * R + B * (d * WV) := by rw [e']; ring
      _ = _ := by rw [e1]; ring

/-- A chain of `madd`s along `x :: rs`, by the stable words `ms`: the carries
out in OF and CF, at the top register and above it. -/
theorem madds_ok (X : List Reg) (s₀ : State) (hax : Reg.rax ∈ X) (hcx : Reg.rcx ∈ X) :
    ∀ (x : Reg) (rs : List Reg) (ms : List MemOp) (vs : List (BitVec 64)) (s : State) (c o : Bool),
      Keeps X s₀ s → (∀ r ∈ x :: rs, r ∈ X) → (x :: rs).Nodup →
      (∀ r ∈ x :: rs, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx) → rs.length = ms.length →
      List.Forall₂ (fun m v => Stable X s₀ (.mem m) v) ms vs → s.cf = some c → s.of = some o →
      WP isa (.block (madds (x :: rs) (ms.map .mem))) s fun s' => ∃ c' o' : Bool,
        s'.cf = some c' ∧ s'.of = some o' ∧
        rv s' (x :: rs) + 2 ^ (64 * rs.length) * o'.toNat + 2 ^ (64 * (rs.length + 1)) * c'.toNat =
          rv s (x :: rs) + o.toNat + 2 ^ 64 * c.toNat + (s.gpr .rdx).toNat * wv vs ∧
        Keeps (.rax :: .rcx :: x :: rs) s s'
  | x, [], ms, vs, s, c, o, _, _, _, _, hl, hf, hc, ho => by
    cases ms with
    | nil =>
      cases hf
      refine WP.block_nil ⟨c, o, hc, ho, ?_, Keeps.refl _ _⟩
      simp only [wv, List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
        Nat.mul_one]
      omega
    | cons => simp at hl
  | _, _ :: _, [], _, _, _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | x, y :: rs, m :: ms, vs, s, c, o, hk, hX, hnd, hr, hl, hf, hc, ho => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hxr := hr x List.mem_cons_self
    have hyr := hr y (List.mem_cons_of_mem _ List.mem_cons_self)
    have hxy : x ≠ y := fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.mem_cons_self)
    have hxn : x ∉ y :: rs := (List.nodup_cons.mp hnd).1
    have hv' : readSrc s (.mem m) = some v := hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    rw [List.map_cons, madds, WP.block_append_iff]
    refine WP.mono (madd_ok s hv' hc ho hxy hxr.1 hxr.2.1 hyr.1 hyr.2.1)
      fun s1 ⟨c1, o1, hc1, ho1, e1, k1⟩ => ?_
    have hk1 : Keeps X s₀ s1 := hk.trans (k1.mono fun r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact hX _ List.mem_cons_self
      · exact hX _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact hax
      · exact hcx)
    refine WP.mono (madds_ok X s₀ hax hcx y rs ms vs s1 c1 o1 hk1
      (fun r h => hX r (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
      (fun r h => hr r (List.mem_cons_of_mem _ h)) (by simpa using hl) hf hc1 ho1)
      fun s' ⟨c', o', hc', ho', e', k'⟩ => ⟨c', o', hc', ho', ?_, ?_⟩
    · have x' : s'.gpr x = s1.gpr x := k'.1 x (by
        simp only [List.mem_cons, not_or] at hxn ⊢
        exact ⟨hxr.1, hxr.2.1, hxn⟩)
      have d1 : s1.gpr .rdx = s.gpr .rdx := k1.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hxr.2.2 e.symm, fun e => hyr.2.2 e.symm, by decide, by decide⟩)
      have r1 : rv s1 rs = rv s rs := rv_congr fun r h => k1.1 r (by
        have hrr := hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => hxn (e ▸ List.mem_cons_of_mem _ h), fun e => ?_, hrr.1, hrr.2.1⟩
        exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (e ▸ h))
      rw [d1] at e'
      simp only [rv] at e'
      rw [r1] at e'
      simp only [rv, List.length_cons, wv] at e1 e' ⊢
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide] at e1
      rw [pow64_succ rs.length] at e'
      rw [x', pow64_succ (rs.length + 1), pow64_succ rs.length]
      exact madds_arith (B := 2 ^ 64) (Q := 2 ^ (64 * rs.length)) e1 e'
    · refine ⟨fun r hr' => ?_, k'.2.1.trans k1.2.1, k'.2.2.1.trans k1.2.2.1, k'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [k'.1 r (by simp only [List.mem_cons, not_or]; exact ⟨hr'.1, hr'.2.1, hr'.2.2.2⟩),
        k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                   exact ⟨hr'.2.2.1, hr'.2.2.2.1, hr'.1, hr'.2.1⟩)]

/-! ## The rotating window -/

theorem win_mod (i k : Nat) : win i k = win (i % 8) k := by
  unfold win; rw [show (i + k) % 8 = (i % 8 + k) % 8 by omega]

theorem wins_mod (i n : Nat) : wins i n = wins (i % 8) n := by
  unfold wins; rw [show win i = win (i % 8) from funext (win_mod i)]

theorem wins_length (i n : Nat) : (wins i n).length = n := by simp [wins]

theorem wins_succ (i : Nat) : wins i 8 = win i 0 :: wins (i + 1) 7 := by
  unfold wins
  rw [show (8 : Nat) = 7 + 1 from rfl, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg (win i 0 :: ·) (congrArg (List.map · _) (funext fun k => ?_))
  show win i (k + 1) = win (i + 1) k
  unfold win; rw [show i + (k + 1) = i + 1 + k by omega]

theorem wins_snoc (i : Nat) : wins i 8 = wins i 7 ++ [win i 7] := by
  unfold wins; rw [show (8 : Nat) = 7 + 1 from rfl, List.range_succ, List.map_append]; rfl

theorem win_facts : ∀ i < 8, (wins i 8).Nodup ∧ win i 7 ∉ wins i 7 ∧
    ∀ r ∈ wins i 8, r ∈ clob ∧ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by decide

theorem wins_facts (i : Nat) : (wins i 8).Nodup ∧ win i 7 ∉ wins i 7 ∧
    ∀ r ∈ wins i 8, r ∈ clob ∧ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by
  rw [wins_mod i 8, wins_mod i 7, win_mod i 7]; exact win_facts _ (Nat.mod_lt _ (by decide))

theorem win_mem (i k : Nat) (hk : k < 8) : win i k ∈ wins i 8 :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem wins7_sub (i : Nat) {r : Reg} (h : r ∈ wins i 7) : r ∈ wins i 8 := by
  rw [wins_snoc]; exact List.mem_append_left _ h

theorem wins_succ_sub (i : Nat) {r : Reg} (h : r ∈ wins (i + 1) 7) : r ∈ wins i 8 := by
  rw [wins_succ]; exact List.mem_cons_of_mem _ h

theorem rv_append (s : State) : ∀ xs ys : List Reg,
    rv s (xs ++ ys) = rv s xs + 2 ^ (64 * xs.length) * rv s ys
  | [], ys => by simp [rv]
  | x :: xs, ys => by
    rw [List.cons_append, rv, rv, rv_append s xs ys, List.length_cons, pow64_succ]; ring

theorem stable_scs_mem {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (fun m v => Stable X s (.mem m) v) (ds.map sc) (ds.map fun d => word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (stable_sc hs hX (h d List.mem_cons_self))
      (stable_scs_mem hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-! ## A row -/

theorem row_arith {Q B L4 w4 w5 o4 c4 o5 R0 dA : Nat} (hb : R0 + dA < B * Q)
    (c4l : c4 ≤ 1) (o5l : o5 ≤ 1)
    (e4 : L4 + Q * w4 + Q * o4 + B * Q * c4 = R0 + dA) (e5 : w5 + B * o5 = w4 + o4) :
    L4 + Q * w5 = R0 + dA := by
  have e : L4 + Q * w5 + B * Q * o5 + B * Q * c4 = R0 + dA := by
    have := congrArg (Q * ·) e5
    simp only [Nat.mul_add] at this
    rw [show B * Q * o5 = Q * (B * o5) by ring]
    generalize Q * w5 = a1 at *; generalize Q * (B * o5) = a2 at *
    generalize Q * w4 = a3 at *; generalize Q * o4 = a4 at *; generalize B * Q * c4 = a5 at *
    omega
  generalize B * Q = BQ at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp o5l with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c4l with rfl | rfl <;> omega

theorem row_bound {R0 d A B Q : Nat} (hR : R0 < Q) (hd : d < B) (hA : A < Q) :
    R0 + d * A < B * Q := by
  have h1 : d * A ≤ (B - 1) * Q := Nat.mul_le_mul (by omega) (Nat.le_of_lt hA)
  have h2 : (B - 1) * Q + Q = B * Q := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  omega

theorem rowX_eq (a b i : Nat) : rowX a b i = loads (b + 8 * i) ([.rdx] : List Reg) ++
    (([.mov32 (win i 7) (.imm 0), clear] : List Instr) ++
    (madds (win i 0 :: wins (i + 1) 7)
      ((([a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] : List Nat).map sc).map .mem) ++
    (([.adox (win i 7) (.reg .rbp)] : List Instr) ++ stores (h i) [win i 0]))) := by
  rw [rowX, ← wins_succ]; rfl

/-- Row `i`: the window plus `b_i · [a]`, whose lowest word is stored at
`h i`. -/
theorem rowX_ok {t : State} {base : Addr} (hs : Scr t base) {a b i : Nat} (ha : Slot a)
    (hb : Slot b) (hi : i < 7) :
    WP isa (.block (rowX a b i)) t fun t' =>
      (word t'.mem base (h i)).toNat + 2 ^ 64 * rv t' (wins (i + 1) 7) =
        rv t (wins i 7) + (word t.mem base (b + 8 * i)).toNat * fe t.mem base a ∧
      KeepsR clob t t' ∧ Outside base (h i) 8 t.mem t'.mem := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  obtain ⟨nd, h7, hr⟩ := wins_facts i
  have r7 := hr _ (win_mem i 7 (by decide))
  rw [rowX_eq, WP.block_append_iff]
  refine WP.mono (loads_ok hs (b + 8 * i) [.rdx] (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)) fun s1 ⟨g1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have d1 : s1.gpr .rdx = word t.mem base (b + 8 * i) := by
    have := g1 0 (by decide) .r8; simpa using this
  rw [WP.block_append_iff, show ([.mov32 (win i 7) (.imm 0), clear] : List Instr) =
    [.mov32 (win i 7) (.imm 0)] ++ [clear] from rfl, WP.block_append_iff]
  refine WP.mono (mov32_ok s1 (win i 7) 0) fun s2 ⟨z2, k2⟩ => ?_
  refine WP.mono (clear_ok s2) fun s3 ⟨p3, c3, o3, k3⟩ => ?_
  have hrdi7 : Reg.rdi ∉ [win i 7] := by simpa using Ne.symm r7.2.2.2.2.2
  have hs3 := (hs1.of_keeps k2 hrdi7).of_keeps k3 (by decide)
  have m3 : s3.mem = t.mem := k3.2.1.trans (k2.2.1.trans k1.2.1)
  rw [WP.block_append_iff]
  have hsrc := stable_scs_mem (X := clob) hs3 (by decide)
    [a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  refine WP.mono (madds_ok clob s3 (by decide) (by decide) (win i 0) (wins (i + 1) 7) _ _ s3 false
    false (Keeps.refl _ _) (fun r h => (hr r (by rw [wins_succ]; exact h)).1)
    (by rw [← wins_succ]; exact nd) (fun r h => by
      have := hr r (by rw [wins_succ]; exact h); exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩)
    (by rw [wins_length]; rfl) hsrc c3 o3) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s4 ho4) fun s5 ⟨o5, _, _, e5, k5⟩ => ?_
  have hs5 := (hs3.of_keeps k4 (by
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, by decide, Ne.symm (hr _ (win_mem i 0 (by decide))).2.2.2.2.2,
      fun e => (hr _ (wins_succ_sub i e)).2.2.2.2.2 rfl⟩)).of_keeps k5 hrdi7
  refine WP.mono (stores_ok hs5 (h i) [win i 0] (by simp only [h, ACC]; simp; omega))
    fun s6 ⟨m6, out6, g6, rd6, wr6⟩ => ⟨?_, ?_, ?_⟩
  · -- the arithmetic
    have w6 : (word s6.mem base (h i)).toNat = (s5.gpr (win i 0)).toNat := by
      simpa [mv, rv] using m6
    have v6 : rv s6 (wins (i + 1) 7) = rv s5 (wins (i + 1) 7) := rv_congr fun r _ => g6 r
    have L : (s5.gpr (win i 0)).toNat + 2 ^ 64 * rv s5 (wins (i + 1) 7) = rv s5 (wins i 8) := by
      rw [wins_succ]; rfl
    rw [w6, v6, L, wins_snoc, rv_append, wins_length]
    have v5 : rv s5 (wins i 7) = rv s4 (wins i 7) := rv_congr fun r hr' => k5.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun e => h7 (e ▸ hr'))
    have p4 : s4.gpr .rbp = 0 := by
      rw [k4.1 _ (by
        simp only [List.mem_cons, not_or]
        refine ⟨by decide, by decide, fun e => (hr _ (win_mem i 0 (by decide))).2.2.2.2.1 e.symm,
          fun e => ?_⟩
        exact (hr _ (wins_succ_sub i e)).2.2.2.2.1 rfl), p3]
    rw [← wins_succ, wins_snoc] at e4
    simp only [rv_append, wins_length] at e4
    rw [p4] at e5
    have v3 : rv s3 (wins i 7) = rv t (wins i 7) := rv_congr fun r hr' => by
      have := hr r (wins7_sub i hr')
      rw [k3.1 r (by simp [this.2.2.2.2.1]), k2.1 r (by simp; exact fun e => h7 (e ▸ hr')),
        k1.1 r (by simp [this.2.2.2.1])]
    have z3 : s3.gpr (win i 7) = 0 := by rw [k3.1 _ (by simp [r7.2.2.2.2.1]), z2]; rfl
    have d3 : s3.gpr .rdx = s1.gpr .rdx := by
      rw [k3.1 _ (by decide), k2.1 _ (by simp [r7.2.2.2.1.symm])]
    have A3 : wv (([a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] : List Nat).map
        fun d => word s3.mem base d) = fe t.mem base a := by rw [m3]; exact wv_words' _ _ _
    have hb := row_bound (Q := 2 ^ (64 * 7)) (B := 2 ^ 64)
      (rv_lt t (wins i 7) |>.trans_eq (by rw [wins_length]))
      (word t.mem base (b + 8 * i)).isLt (mv_lt t.mem base a 7)
    rw [pow64_succ 7] at e4
    rw [v5]
    generalize 2 ^ (64 * 7) = Q at e4 hb ⊢
    simp only [rv, z3, d3, d1, A3, v3, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      toNat_zero64] at e4 e5 ⊢
    exact row_arith hb (Bool.toNat_le _) (Bool.toNat_le _) e4 e5
  · refine ⟨fun r hr' => ?_, ?_, ?_⟩
    · have nw : r ∉ wins i 8 := fun h => hr' (hr r h).1
      rw [g6, k5.1 r (by simp; exact fun e => nw (e ▸ win_mem i 7 (by decide))),
        k4.1 r (by
          simp only [List.mem_cons, not_or]
          refine ⟨fun e => hr' (e ▸ by decide), fun e => hr' (e ▸ by decide),
            fun e => nw (e ▸ win_mem i 0 (by decide)), fun e => nw (wins_succ_sub i e)⟩),
        k3.1 r (by simp; exact fun e => hr' (e ▸ by decide)),
        k2.1 r (by simp; exact fun e => nw (e ▸ win_mem i 7 (by decide))),
        k1.1 r (by simp; exact fun e => hr' (e ▸ by decide))]
    · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
    · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [← k5.2.1.trans (k4.2.1.trans m3)]; exact out6

/-! ## The product -/

theorem zeros_ok : ∀ (rs : List Reg) (s : State),
    WP isa (.block (rs.map fun r => .mov32 r (.imm 0))) s fun s' =>
      (∀ r ∈ rs, s'.gpr r = 0) ∧ Keeps rs s s'
  | [], s => WP.block_nil ⟨by simp, Keeps.refl _ _⟩
  | r :: rs, s => by
    rw [List.map_cons, show ∀ (x : Instr) l, x :: l = [x] ++ l from fun _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (mov32_ok s r 0) fun s1 ⟨z1, k1⟩ =>
      WP.mono (zeros_ok rs s1) fun s' ⟨z', k'⟩ => ⟨fun r' hr' => ?_, ?_⟩
    · by_cases h : r' ∈ rs
      · exact z' r' h
      · have : r' = r := by simpa [h] using hr'
        subst this; rw [k'.1 _ h, z1]; rfl
    · exact (k1.mono fun _ h => by simp_all).trans (k'.mono fun _ h => List.mem_cons_of_mem _ h)

theorem rv_zero (s : State) : ∀ rs : List Reg, (∀ r ∈ rs, s.gpr r = 0) → rv s rs = 0
  | [], _ => rfl
  | r :: rs, h => by
    rw [rv, h r List.mem_cons_self, rv_zero s rs fun r' h' => h r' (List.mem_cons_of_mem _ h')]; rfl

theorem rows_arith {M P B W' R' R bn A MB : Nat} (tv : M + P * R = MB * A)
    (e : W' + B * R' = R + bn * A) : M + P * W' + B * P * R' = (MB + P * bn) * A :=
  calc M + P * W' + B * P * R'
      _ = M + P * (W' + B * R') := by ring
      _ = (M + P * R) + P * bn * A := by rw [e]; ring
      _ = _ := by rw [tv]; ring

/-- The rows: `[ACC]` and the last window are `[b] · [a]`. -/
theorem rowsX_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) (hz : rv s (wins 0 7) = 0) :
    WP isa (.block ((List.range 7).flatMap (rowX a b))) s fun t =>
      KeepsR clob s t ∧ Outside base ACC 56 s.mem t.mem ∧
      mv t.mem base ACC 7 + 2 ^ (64 * 7) * rv t (wins 7 7) = fe s.mem base b * fe s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  let inv := fun n (t : State) => KeepsR clob s t ∧ Outside base ACC (8 * n) s.mem t.mem ∧
    mv t.mem base ACC n + 2 ^ (64 * n) * rv t (wins n 7) = mv s.mem base b n * fe s.mem base a
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block (rowX a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tout, tv⟩
    have ht : Scr t base := hs.of_keepsR tk (by decide)
    refine WP.mono (rowX_ok ht ha hb hn) fun t' ⟨e, k', out'⟩ => ⟨tk.trans k', ?_, ?_⟩
    · exact (tout.mono (le_refl _) (by omega)).trans
        (out'.mono (by simp only [h]; omega) (by simp only [h]; omega))
    · have m1 : mv t'.mem base ACC n = mv t.mem base ACC n :=
        out'.mv (Or.inl (by simp only [h]; omega)) (by simp only [ACC]; omega)
      have w1 : mv t'.mem base (ACC + 8 * n) 1 = (word t'.mem base (h n)).toNat := by
        simp only [mv, h, Nat.mul_zero, Nat.add_zero]
      have b1 : word t.mem base (b + 8 * n) = word s.mem base (b + 8 * n) :=
        tout.word (Or.inl (by simp only [ACC]; omega)) (by omega)
      have a1 : fe t.mem base a = fe s.mem base a :=
        tout.fe (Or.inl (by simp only [ACC]; omega)) (by omega)
      have mb : mv s.mem base b (n + 1) =
          mv s.mem base b n + 2 ^ (64 * n) * (word s.mem base (b + 8 * n)).toNat := by
        rw [mv_add]; simp only [mv, Nat.mul_zero, Nat.add_zero]
      rw [mv_add, m1, w1, mb, pow64_succ]
      rw [b1, a1] at e
      exact rows_arith (B := 2 ^ 64) tv e
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by simp [mv, hz]⟩)
    fun t ⟨tk, tout, tv⟩ => ⟨tk, tout, tv⟩

theorem wins07_clob : ∀ r ∈ wins 0 7, r ∈ clob := by decide

/-- `[o] = [a] · [b]`, by rows. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  simp only [mulX, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok (wins 0 7) s) fun s1 ⟨z1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowsX_ok hs1 ha hb (rv_zero s1 _ z1)) fun s2 ⟨k2, out2, v2⟩ => ?_
  have hs2 := hs1.of_keepsR k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs2 (h 7) (wins 7 7) (by rw [wins_length]; decide))
    fun s3 ⟨m3, out3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  refine WP.mono (reduce_ok hs3 ho) fun s4 ⟨e4, g4, rd4, wr4, out4⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    rw [g4 r hr, g3 r, k2.1 r hr, k1.1 r fun h => hr (wins07_clob r h)]
  · rw [rd4, rd3, k2.2.1, k1.2.2.1]
  · rw [wr4, wr3, k2.2.2, k1.2.2.2]
  · rw [← k1.2.1]
    have ho' : o + 56 ≤ ACC := ho
    exact ((out2.mono (le_refl _) (by omega)).right o 56).trans
      (((out3.mono (by simp only [h]; omega) (by rw [wins_length]; simp only [h]; omega)).right
        o 56).trans (out4.left ACC 112))
  · have m1 : s1.mem = s.mem := k1.2.1
    have hm : mv s3.mem base ACC 7 = mv s2.mem base ACC 7 :=
      out3.mv (Or.inl (by simp only [h]; omega)) (by simp only [ACC]; omega)
    rw [wins_length] at m3
    rw [show ACC + 56 = h 7 from rfl, m3, hm, show (448 : Nat) = 64 * 7 from rfl, v2, m1] at e4
    rw [Nat.mul_comm] at e4
    exact toFe_mul e4

end VG.Proof.X448.X86_64
