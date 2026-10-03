import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.X86.HPrime.OutputCT

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest, in two runs

`finishOutput_rel`: two runs with the same public data take the same
branches (the output length decides them) and the same number of chain
iterations, and write the output through the same addresses.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput copyRemaining
  leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_movm contains_addr)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- `ChainInv`, for some digest `V`. -/
def ChainAt (s₀ : State) (e : BitVec 32) (j : Nat) (s : State) : Prop :=
  ∃ V : List Byte, V.length = 64 ∧ ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, hV, i⟩ := h
  ⟨i.body, _, i.out, chainOut_length hV j⟩

theorem cf_true {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some true) : p := by
  have e' : t.cf = some true := e
  rw [h] at e'; simpa using e'

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'; simpa using e'

/-- The two runs agree on `esp` and `ebx`. -/
theorem agree_body {s₀ s₀' : State} (q : Same s₀ s₀') {t₁ t₂ : State} (b₁ : Body s₀ t₁)
    (b₂ : Body s₀' t₂) : ∀ r ∈ [Reg.esp, .ebx], t₁.gpr r = t₂.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [b₁.esp, b₂.esp, q.esp]
  · rw [b₁.ebx, b₂.ebx, q.scr_eq]

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

/-! ## `next`, keeping the output -/

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : InitIn (scr s₀) (esp₀ s₀) n s ∧ OutAt s₀ L s) : WP isa next s (OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, b, xs, o, hx⟩ := h
  exact (next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (InitIn (scr s₀) (esp₀ s₀) n t₁ ∧ OutAt s₀ L t₁) ∧
      (InitIn (scr s₀) (esp₀ s₀) n t₂ ∧ OutAt s₀' L t₂)) next
      fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ :=
  rel_wp ((next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => next_out_ok hp hn₁ hn₂ h)
    (fun _ h => next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr_eq, q.esp]; exact h.1, h.2⟩)

/-! ## The chain -/

include hp in
/-- Setting `edx` keeps the body and the output. -/
theorem edx_blk {L n : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .edx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      InitIn (scr s₀) (esp₀ s₀) n t ∧ OutAt s₀ L t := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, u₁.gpr⟩, b₁, xs, o.same u₁.mem, hx⟩

include hp in
theorem emit_body {L : Nat} (hL : L + 32 ≤ ol s₀) {s : State} (h : OutAt s₀ L s) :
    WP isa emitPrefix s (Body s₀) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact (emit_ok hp b o (by rw [hx]; exact hL)).mono fun _ h => h.1

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} (hl : 32 + 32 * j + 32 ≤ ol s₀) {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  have hl' : 32 + 32 * j + 32 ≤ ol s₀' := by rw [q.ol_eq]; exact hl
  refine RelCT.seq (rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => edx_blk (n := 64) hp h.outAt)
    (fun _ h => (edx_blk (n := 64) hp' h.outAt).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp]; exact h.1, h.2⟩))
    (RelCT.seq (next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (rel_wp (emit_rel hp hp' q hl) (fun _ h => emit_body hp hl h)
        (fun _ h => emit_body hp' hl' h)) ?_))
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun _ _ h => agree_regs (agree_body q h.1 h.2)) (by taint_decide)

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (e e' : BitVec 32) (t₁ t₂ : State) : Prop :=
  ∃ j, ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂ ∧ 33 ≤ ol s₀ - (32 + 32 * j) ∧
    ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

include hp hp' q in
theorem chain_rel {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ ol s₀ - (32 + 32 * j) ∧ ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      chain (ChainDone s₀ s₀' e e') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := ChainDone s₀ s₀' e e')
      (fun m t₁ t₂ => ∃ j, m = ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (body_rel hp hp' q (j := j) (by omega) (e := e) (e' := e')).wp
    (F₁ := fun (t : State) => ChainAt s₀ e (j + 1) t ∧ t.cf = some (decide (ol s₀ - (32 + 32 * (j + 1)) < 65)))
    (F₂ := fun (t : State) => ChainAt s₀' e' (j + 1) t ∧ t.cf = some (decide (ol s₀' - (32 + 32 * (j + 1)) < 65)))
    fun t₁ t₂ ⟨⟨V, hV, i₁⟩, ⟨V', hV', i₂⟩⟩ =>
      ⟨(iter_ok hp hV i₁ (by omega)).mono fun _ h => ⟨⟨V, hV, h.1⟩, h.2⟩,
       (iter_ok hp' hV' i₂ (by omega)).mono fun _ h => ⟨⟨V', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have ev : isa.eval .ae t₁ = isa.eval .ae t₂ := by
      show t₁.cf.map (!·) = t₂.cf.map (!·); rw [f₁, f₂]
    refine ⟨ev, fun hf => ?_, fun ht => ?_⟩
    · have : ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have hf' : t₁.cf.map (!·) = some false := hf
        rw [f₁] at hf'; simpa using hf'
      exact ⟨j + 1, c₁, c₂, by omega, by omega, by omega⟩
    · have : ¬ ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have ht' : t₁.cf.map (!·) = some true := ht
        rw [f₁] at ht'; simpa using ht'
      exact ⟨_, by omega, j + 1, rfl, by omega, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := Body s₀ s ∧ Out s₀ s [] ∧ s.gpr .ebp = s₀.gpr .ebp

include hp in
theorem ext_emit {s : State} (h : ExtIn s₀ s) (hol : 32 ≤ ol s₀) :
    WP isa emitPrefix s (ChainAt s₀ (s₀.gpr .ebp) 0) := by
  obtain ⟨b, o, e⟩ := h
  refine (emit_ok hp b o (by simp only [List.length_nil]; omega)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨digest s₀ s, by simp [digest, bytesAt], bt, et.trans e, ?_, ?_⟩
  · rw [List.nil_append] at ot
    simpa [chainOut, chainPrefixes] using ot
  · exact dt

include hp in
theorem ChainAt.keeps {e : BitVec 32} {j : Nat} {s t : State} (h : ChainAt s₀ e j s)
    (k : Keeps (scr s₀) (esp₀ s₀) s t) (m : t.mem = s.mem) : ChainAt s₀ e j t :=
  let ⟨V, hV, i⟩ := h
  ⟨V, hV, i.body.keeps hp k, k.ebp.trans i.ebp, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    WP isa (.block cmpLeft) s fun t => ChainAt s₀ e j t ∧
      t.cf = some (decide (ol s₀ - (32 + 32 * j) < 65)) := by
  obtain ⟨V, hV, i⟩ := h
  refine (cmp_ok hp i.body i.out).mono fun t ⟨cf, k, m⟩ => ⟨ChainAt.keeps hp ⟨V, hV, i⟩ k m, ?_⟩
  rw [cf, chainOut_length hV]

include hp in
theorem left_blk {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s fun t =>
      InitIn (scr s₀) (esp₀ s₀) (ol s₀ - (32 + 32 * j)) t ∧ OutAt s₀ (32 + 32 * j) t := by
  obtain ⟨b, xs, o, hx⟩ := h.outAt
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, by rw [u₁.gpr, o.left, hx]⟩, b₁, xs, o.same u₁.mem, hx⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ ∧ L < ol s₀ ∧ ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel {e e' : BitVec 32} :
    RelCT isa (ChainDone s₀ s₀' e e')
      (.seq (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) next) (Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (rel_taint [.ebx] (F₁ := ChainAt s₀ e j) (F₂ := ChainAt s₀' e' j)
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        obtain ⟨_, _, i₁⟩ := h₁; obtain ⟨_, _, i₂⟩ := h₂
        rw [i₁.body.ebx, i₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
      (fun _ h => left_blk hp h)
      (fun _ h => (left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp, ← ho]; exact h.1, h.2⟩))
    (next_out_rel hp hp' q (n := ol s₀ - (32 + 32 * j)) (by omega) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega, by omega⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) extendDigest (Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (rel_wp ((emit_rel hp hp' q (L := 0) (by omega)).mono
      (fun _ _ ⟨⟨b₁, o₁, _⟩, ⟨b₂, o₂, _⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => ext_emit hp h (by omega)) (fun _ h => ext_emit hp' h (by omega))) ?_
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ ⟨_, _, i₁⟩ ⟨_, _, i₂⟩ => agree_body q i₁.body i₂.body)
    ⟨_, by taint_decide⟩ (fun _ h => chain_cmp hp h) (fun _ h => chain_cmp hp' h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by have := cf_true f₁ ht; omega⟩)
    ((chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by have := cf_false f₁ hf; omega, c₁, c₂⟩) fun _ _ h => h))
    (last_rel hp hp' q)


include hp in
theorem ext_cmp {s : State} (h : ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => ExtIn s₀ t ∧ t.cf = some (decide (ol s₀ < 65)) := by
  obtain ⟨b, o, e⟩ := h
  refine (cmp_ok hp b o).mono fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k, k.ebp.trans e⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ ⟨b₁, _⟩ ⟨b₂, _⟩ => agree_body q b₁ b₂)
    ⟨_, by taint_decide⟩ (fun _ h => ext_cmp hp h) (fun _ h => ext_cmp hp' h)) ?_
  refine RelCT.seq (R := Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨⟨b₁, o₁, _⟩, f₁⟩, ⟨⟨b₂, o₂, _⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by have := cf_true f₁ ht; omega,
        by have := cf_true f₁ ht; omega⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (extend_rel hp hp' q (by have := cf_false f₁ hf; omega)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (copyRemaining_rel hp hp' q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h


end

end VG.Proof.Argon2.X86.HPrime
