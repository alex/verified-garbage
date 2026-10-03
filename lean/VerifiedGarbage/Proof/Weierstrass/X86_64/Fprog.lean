import VerifiedGarbage.Proof.Weierstrass.X86_64.Env
import VerifiedGarbage.Proof.Mont.X86_64.Ops

/-!
# Field programs on x86-64

`fprog M ops` runs the field operations `ops` on slots of the working space
(`fprog_ok`), one by one with `mul_ok`, `add_ok` and `sub_ok`: on slots that
are apart from each other, from the modulus and from the temporary area
(`Lay`), what the slots stand for (`toM`) follows `runOps ops`, the program
on environments (`Inv`). A slot is read only once it holds a number below
`m`: either it did at the start (`V`) or an earlier operation wrote it
(`readsOk`). Only the registers `clob n`, the slots written and the temporary
area change (`ProgKeep`).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64

/-- The slots `Sl` (offsets of `n`-word numbers in a working space of `size`
bytes): any two are the same or apart, and each is apart from the modulus
and from the temporary area. -/
structure Lay (M : Mod) (size : Nat) (Sl : Nat → Prop) : Prop where
  le : ∀ x, Sl x → x + 8 * M.n ≤ size
  apart : ∀ x y, Sl x → Sl y → x ≠ y → x + 8 * M.n ≤ y ∨ y + 8 * M.n ≤ x
  mo : ∀ x, Sl x → x + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ x
  tmp : ∀ x, Sl x → x + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ x

/-- Slots on a grid: `d + 8 n i` for `lo ≤ i < hi`, with the modulus and the
temporary area on the grid below `lo`. -/
theorem Lay.grid {M : Mod} {size d lo hi imo itmp : Nat} (hmo : M.mo = d + 8 * M.n * imo)
    (htmp : M.tmp = d + 8 * M.n * itmp) (himo : imo < lo) (hitmp : itmp < lo)
    (hsize : d + 8 * M.n * hi ≤ size) :
    Lay M size fun x => ∃ i, lo ≤ i ∧ i < hi ∧ x = d + 8 * M.n * i := by
  have apart : ∀ i j, i ≠ j → d + 8 * M.n * i + 8 * M.n ≤ d + 8 * M.n * j ∨
      d + 8 * M.n * j + 8 * M.n ≤ d + 8 * M.n * i := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := Nat.mul_le_mul_left (8 * M.n) h
      rw [Nat.mul_succ] at this
      omega
    · have := Nat.mul_le_mul_left (8 * M.n) h
      rw [Nat.mul_succ] at this
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨i, -, hi', rfl⟩
    have := Nat.mul_le_mul_left (8 * M.n) hi'
    rw [Nat.mul_succ] at this
    omega
  · rintro x y ⟨i, -, -, rfl⟩ ⟨j, -, -, rfl⟩ hxy
    exact apart i j fun h => hxy (h ▸ rfl)
  · rintro x ⟨i, hi, -, rfl⟩
    rw [hmo]; exact apart i imo (by omega)
  · rintro x ⟨i, hi, -, rfl⟩
    rw [htmp]; exact apart i itmp (by omega)

/-- The state holds the environment `E` in Montgomery's form in the slots
`V`, below `m`, with the modulus in place. -/
structure Inv (M : Mod) (base : Addr) (size m : Nat) (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → ZMod m) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOk M size m s.mem base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x M.n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x

theorem Inv.sub {M : Mod} {base : Addr} {size m : Nat} {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → ZMod m} {s : State} (h : Inv M base size m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv M base size m Sl V' E s :=
  ⟨h.scr, h.mod, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx),
    fun x hx => h.val x (hV x hx)⟩

/-- What a program writing the slots `W` keeps: the registers but `clob`,
the regions, and the memory but the slots `W` and the temporary area. -/
structure ProgKeep (M : Mod) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem ProgKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) : ProgKeep M base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem ProgKeep.mono {M : Mod} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : ProgKeep M base W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeep M base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem rdi_not_clob (n : Nat) : Reg.rdi ∉ clob n := by
  intro h
  simp only [clob, List.mem_cons] at h
  rcases h with h | h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · have := List.mem_of_mem_take h
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at this

theorem ProgKeep.scr {M : Mod} {base : Addr} {W : List Nat} {s s' : State} {size : Nat}
    (h : ProgKeep M base W s s') (hs : Scr s base size) : Scr s' base size :=
  ⟨(h.gpr _ (rdi_not_clob _)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- A number in memory apart from what an operation writes. -/
theorem opKeep_wordsVal {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 8 * M.n ≤ y) →
      (y + 8 * k ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y) → y + 8 * k ≤ 2 ^ 64 →
      wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    simp only [wordsVal]
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega)]; omega)
        (by rw [ofs_off base (by omega)]; omega)
    rw [opKeep_wordsVal h (k := k) (y := y + 8) (by omega) (by omega) (by omega), hw]

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {size m : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → ZMod m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : OpKeep M base o s s') (hr : wordsVal s'.mem base o M.n < m) {v : ZMod m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hlo := hL.le o ho
  have hmo := hL.mo o ho
  have hto := hL.tmp o ho
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => by
      have := hL.apart x o hx ho hxo
      have := hL.tmp x hx
      have := hL.le x hx
      exact opKeep_wordsVal hk (by omega) (by omega) (by omega)
  refine ⟨⟨(hk.gpr _ (rdi_not_clob _)).trans hI.scr.rdi, hk.wr ▸ hI.scr.wr, hn⟩,
    ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, ?_, hM.inv⟩, ?_, ?_, ?_⟩
  · have := hM.mo
    have := hM.sep
    rw [opKeep_wordsVal hk (by omega) (by omega) (by omega)]
    exact hM.val
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · rw [heq x (hI.sl x (List.mem_of_ne_of_mem hxo hx)) hxo]
      exact hI.lt x (List.mem_of_ne_of_mem hxo hx)
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {size m : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : Nat.Coprime (2 ^ (64 * M.n)) m) {V : List Nat} {E : Nat → ZMod m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (op.code M)) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mul_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (add_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (by omega)) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (sub_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2) hA hB)
      fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

/-- `ops` read only slots of `V` or written by an earlier operation. -/
def readsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, V => op.ins.all (fun x => decide (x ∈ V)) && readsOk ops (op.out :: V)

/-- The slots holding a value after `ops`: `V` and those `ops` write. -/
def validAfter : List FOp → List Nat → List Nat
  | [], V => V
  | op :: ops, V => validAfter ops (op.out :: V)

theorem mem_validAfter {x : Nat} :
    ∀ (ops : List FOp) (V : List Nat), x ∈ validAfter ops V ↔ x ∈ V ∨ x ∈ ops.map FOp.out
  | [], V => by simp [validAfter]
  | op :: ops, V => by
    rw [validAfter, mem_validAfter ops, List.map_cons, List.mem_cons, List.mem_cons]
    grind

theorem readsOk_mono : ∀ {ops : List FOp} {V V' : List Nat}, readsOk ops V = true →
    (∀ x ∈ V, x ∈ V') → readsOk ops V' = true
  | [], _, _, _, _ => rfl
  | op :: ops, V, V', h, hV => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨fun x hx => hV x (h.1 x hx), readsOk_mono h.2 fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hV x hx)

theorem readsOk_rename (σ : Nat → Nat) : ∀ {ops : List FOp} {V : List Nat}, readsOk ops V = true →
    readsOk (ops.map (FOp.rename σ)) (V.map σ) = true
  | [], _, _ => rfl
  | op :: ops, V, h => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have h₂ := readsOk_rename σ h.2
    have hout : (op.rename σ).out = σ op.out := by cases op <;> rfl
    have hins : ∀ x ∈ (op.rename σ).ins, ∃ y ∈ op.ins, σ y = x := by
      cases op <;> simp [FOp.rename, FOp.ins]
    simp only [List.map_cons, readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun x hx => ?_, by rw [hout]; exact h₂⟩
    obtain ⟨y, hy, rfl⟩ := hins x hx
    exact List.mem_map_of_mem (h.1 y hy)

theorem fprog_cons (M : Mod) (op : FOp) (ops : List FOp) :
    fprog M (op :: ops) = op.code M ++ fprog M ops := rfl

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {size m : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : Nat.Coprime (2 ^ (64 * M.n)) m) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → ZMod m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (fprog M ops)) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [fprog_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

/-! ## The complete addition -/

theorem rcbN_reads : readsOk rcbN [9, 10, 11, 12, 13, 14, 15, 16] = true := by decide

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {size m : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : Nat.Coprime (2 ^ (64 * M.n)) m) {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → ZMod m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (fprog M (rcb S p q o))) s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprog_ok hL hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

end VG.Proof.Weierstrass.X86_64
