import VerifiedGarbage.Proof.Ed25519.X86_64.Field
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Untrusted: run the field workspace inside Ed25519's eight-KiB scratch argument. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

structure Scratch (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

theorem Scratch.of_keep {s t : State} {base : Addr} (hs : Scratch s base) (hk : Keep base s t) :
    Scratch t base := ⟨(hk.gpr _ (by decide)).trans hs.rdi, hk.wr ▸ hs.wr, hs.nowrap⟩

theorem Scratch.of_keeps {s t : State} {base : Addr} {rs : List Reg} (hs : Scratch s base)
    (hk : Keeps rs s t) (hr : .rdi ∉ rs) : Scratch t base :=
  ⟨(hk.1 _ hr).trans hs.rdi, hk.2.2.2 ▸ hs.wr, hs.nowrap⟩

theorem field_lift {s : State} {base : Addr} (hs : Scratch s base) (code : List Instr)
    (f : Env → Env)
    (correct : ∀ t, Scr t base → WP isa (.block code) t fun u =>
      Keep base t u ∧ env u.mem base = f (env t.mem base)) :
    WP isa (.block code) s fun t => Keep base s t ∧ env t.mem base = f (env s.mem base) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv⟩ := correct narrow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem fieldCodeWide_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) :=
  field_lift hs (fieldCode fld ops) (evalOps ops) (fun _ h => fieldCode_ok ops h)

theorem constFieldWide_ok {s : State} {base : Addr} (hs : Scratch s base) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o v :=
  field_lift hs (constField o v) (fun e => Function.update e o v) (fun _ h => by
    refine WP.mono (constField_op h o v) fun t ⟨hk, hv⟩ => ?_
    exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]⟩)

theorem copyFieldWide_ok {s : State} {base : Addr} (hs : Scratch s base) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o (env s.mem base a) :=
  field_lift hs (copyField o a) (fun e => Function.update e o (e a)) (fun _ h => by
    refine WP.mono (copyField_op h o a) fun t ⟨hk, hv⟩ => ?_
    exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]; rfl⟩)

structure RbxKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem RbxKeep.scratch {base : Addr} {s t : State} (h : RbxKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem RbxKeep.trans {base : Addr} {s t u : State}
    (h : RbxKeep base s t) (k : RbxKeep base t u) : RbxKeep base s u :=
  ⟨fun r hr hb => (k.gpr r hr hb).trans (h.gpr r hr hb), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem RbxKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .rbx ∨ r ∈ Proof.X25519.X86_64.clob) : RbxKeep base s t := by
  refine ⟨fun r hr hb => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h
    · exact hb h
    · exact hr h
  · rw [h.2.1]; exact Proof.X25519.X86_64.Outside.refl _ _ _ _

theorem Keep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob) : Keep base s t :=
  ⟨fun r hr => h.1 r (fun hm => hr (hrs r hm)), h.2.2.1, h.2.2.2,
    by rw [h.2.1]; exact Proof.X25519.X86_64.Outside.refl _ _ _ _⟩

theorem RbxKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : RbxKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.mem⟩

end VG.Proof.Ed25519.X86_64
